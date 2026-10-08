//! Chain proofs (`docs/CHAIN_RECURSION.md`, step 3): one proof per block
//! attesting that its header is the tip of a valid chain from genesis.
//!
//! A chain proof for a header verifies the **previous header's chain
//! proof** inside its circuit, then checks the header itself against
//! what that proof attests: it links (`prev_hash` is the attested hash),
//! its height is one more, its timestamp strictly later, and its proof of
//! work meets the target -- computing the real header hash (Poseidon2
//! over the header's bytes) in the circuit. By induction, the latest
//! chain proof vouches for every header back to genesis.
//!
//! Like `aggregate`'s tree, the recursion bottoms out in a second, tiny
//! circuit: the **genesis circuit**, whose proof attests the genesis
//! header as constants. A chain step accepts a child proof by either
//! circuit -- the genesis one's key, or its own (then the child must have
//! carried the same key as input, as an aggregate node's does).
//!
//! Each step also verifies the **block's own proof** -- its tree's root
//! (`aggregate`: a wrap or an aggregation, by the network's keys) -- and
//! checks it claims exactly the reward the schedule gives its height
//! (`prover::Schedule`; none past the chain's end) and moves the state from the
//! parent's (as the child attests) to the header's `state_root` and
//! `output_count`. So a chain proof vouches for every block's validity,
//! not just its header: transactions authorized and balanced, every
//! spent output real and unspent, every created one appended.
//!
//! And it applies the chain's numeric rules (`chain_rules`): the target
//! the next block must meet follows the **retarget** rule (ASERT), and the
//! **cumulative work** grows by this block's.
//!
//! What a chain proof attests (`Tip`, its public inputs):
//!
//! ```text
//! [ step vk | header hash | height, timestamp (4 × 16-bit), output count
//!   (2 × 20-bit) | next target (16 × 16-bit) | state root | anchor time
//!   (4 × 16-bit) | cumulative work (16 × 16-bit) ]
//! ```

#![allow(dead_code)]

use crate::aggregate::{Error, Key, Node, TreeParams, assert_select, fit, vk_digest};
use crate::block::BlockHeader;
use crate::circuit::{Builder, Circuit, CircuitAir, EVar, OVar, Octet};
use crate::ext::Ext;
use crate::poseidon2::{BabyBear, DOMAIN_VK, digest_from_bytes};
use crate::recursion;
use crate::transcript::octet_of;
use crate::state_circuit::{bits_of, canonical_bits, digest_bits, from_bits, hash_bits, pack_octets};
use crate::stark::{self, Proof};

/// What a chain proof attests about its tip header.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tip {
    pub hash: [u8; 32],
    pub height: u64,
    pub timestamp: u64,
    /// The target the *next* header's proof of work must meet.
    pub target: [u8; 32],
    /// The chain state after this block (`state_tree`).
    pub state_root: [u8; 32],
    pub output_count: u64,
    /// The chain's first block's timestamp, which retargeting measures
    /// from (`chain::asert`).
    pub anchor_timestamp: u64,
    /// The chain's cumulative work up to and including it (big-endian).
    pub work: [u8; 32],
}

/// A number's four 16-bit limbs, least significant first.
fn limbs16(v: u64) -> [u32; 4] {
    std::array::from_fn(|j| ((v >> (16 * j)) & 0xffff) as u32)
}

impl Tip {
    /// The tip `header` makes, given what the chain records after it --
    /// `(target, anchor timestamp, cumulative work)` (`Chain::proof_state`).
    pub fn new(header: &BlockHeader, (target, anchor_timestamp, work): ([u8; 32], u64, [u8; 32])) -> Tip {
        Tip {
            hash: header.hash(),
            height: header.height,
            timestamp: header.timestamp,
            target,
            state_root: header.state_root,
            output_count: header.output_count,
            anchor_timestamp,
            work,
        }
    }

    /// `[height, timestamp limbs, output count limbs, 0]` (the count as
    /// `aggregate::wide`).
    fn info(&self) -> Octet {
        let mut o = [BabyBear::ZERO; 8];
        o[0] = BabyBear::new(self.height as u32);
        for (j, l) in limbs16(self.timestamp).into_iter().enumerate() {
            o[1 + j] = BabyBear::new(l);
        }
        o[5..7].copy_from_slice(&crate::aggregate::wide(self.output_count));
        o
    }

    /// The public inputs of a proof attesting this tip, by a circuit
    /// whose key is `vk`.
    fn public(&self, vk: Octet) -> [Octet; 9] {
        let [t0, t1] = octets256(&self.target);
        let [w0, w1] = octets256(&self.work);
        let mut ws = [BabyBear::ZERO; 8];
        for (j, l) in limbs16(self.anchor_timestamp).into_iter().enumerate() {
            ws[j] = BabyBear::new(l);
        }
        [vk, digest_from_bytes(&self.hash), self.info(), t0, t1, digest_from_bytes(&self.state_root), ws, w0, w1]
    }
}

/// A 256-bit big-endian number as 16 big-endian 16-bit limbs, two octets.
fn octets256(be: &[u8; 32]) -> [Octet; 2] {
    let limbs: Vec<BabyBear> = be.chunks(2).map(|p| BabyBear::new(u16::from_be_bytes([p[0], p[1]]) as u32)).collect();
    [limbs[..8].try_into().unwrap(), limbs[8..].try_into().unwrap()]
}

/// In the circuit: two octets of big-endian 16-bit limbs (as `octets256`)
/// as 32 little-endian bytes -- witnesses, range-checked, composing to
/// the limbs.
fn octets_to_bytes(b: &mut Builder, octets: [OVar; 2]) -> Vec<EVar> {
    use crate::chain_rules::witness_byte;
    let limbs: Vec<EVar> = (0..16).map(|i| lane_of(b, octets[i / 8], i % 8)).collect();
    let mut bytes = vec![b.zero(); 32];
    for (i, &limb) in limbs.iter().enumerate() {
        let v = b.ext_value(limb).0[0].value();
        let (hi, lo) = (witness_byte(b, (v >> 8) as u64), witness_byte(b, (v & 0xff) as u64));
        let z = BabyBear::ZERO;
        let composed = b.arith(z, Some(hi), None, BabyBear::new(256), z, Some(lo), BabyBear::ONE, [z; 4]);
        b.assert_eq(composed, limb);
        // Limb i holds big-endian bytes 2i (high) and 2i + 1.
        bytes[31 - 2 * i] = hi;
        bytes[30 - 2 * i] = lo;
    }
    bytes
}

/// The reverse: 32 little-endian bytes as two octets of big-endian
/// 16-bit limbs.
fn bytes_to_octets(b: &mut Builder, bytes: &[EVar]) -> [OVar; 2] {
    let z = BabyBear::ZERO;
    let limbs: Vec<EVar> = (0..16)
        .map(|i| b.arith(z, Some(bytes[31 - 2 * i]), None, BabyBear::new(256), z, Some(bytes[30 - 2 * i]), BabyBear::ONE, [z; 4]))
        .collect();
    [pack_octets(b, &limbs[..8])[0], pack_octets(b, &limbs[8..])[0]]
}

/// The verifier's view of public inputs: each a cell at its address,
/// read once.
fn public_tuples(values: &[Octet]) -> Vec<(BabyBear, Vec<BabyBear>)> {
    values
        .iter()
        .enumerate()
        .map(|(a, v)| {
            let mut tuple = v.to_vec();
            tuple.push(BabyBear::new(a as u32));
            (-BabyBear::ONE, tuple)
        })
        .collect()
}

/// A chain proof, and the tip it attests.
pub struct ChainProof {
    pub air: CircuitAir,
    pub proof: Proof,
    pub tip: Tip,
}

// ---- the genesis circuit -------------------------------------------------------

fn genesis_circuit(tip: &Tip, tree: &TreeParams) -> Result<Circuit, Error> {
    let values = tip.public([BabyBear::ZERO; 8]);
    let (mut b, public) = Builder::with_public(&values);
    // Its key input isn't used (a step checks a genesis child's key
    // against the constant genesis key instead), but every input is read.
    b.halves(public[0]);
    for (k, v) in values.iter().enumerate().skip(1) {
        let expected = b.const_octet(*v);
        b.assert_eq_octet(public[k], expected);
    }
    fit(b, tree)
}

pub fn genesis_key(tip: &Tip, tree: &TreeParams) -> Result<Key, Error> {
    Ok(Key::of(&genesis_circuit(tip, tree)?, tree))
}

pub fn prove_genesis(key: &Key, tip: &Tip, tree: &TreeParams, seed: [u8; 32]) -> Result<ChainProof, Error> {
    let circuit = genesis_circuit(tip, tree)?;
    let air = circuit.air_with(key.preprocessed.clone());
    let proof = stark::prove(&air, &circuit.witness, &tree.params, seed).map_err(Error::Prove)?;
    Ok(ChainProof { air, proof, tip: *tip })
}

// ---- gadgets ---------------------------------------------------------------

/// A witness 16-bit limb, range-checked: the cell and its 16 bits
/// (lowest first).
fn witness_limb(b: &mut Builder, v: u32) -> (EVar, Vec<EVar>) {
    let cell = b.witness_ext(Ext::from_base(BabyBear::new(v)));
    let bits = bits_of(b, cell, 16);
    (cell, bits)
}

/// The bits of a big-endian 64-bit field in the header, from its four
/// limbs' bits (least significant limb first, each lowest bit first):
/// bytes most significant first, each byte's bits lowest first -- what
/// `state_circuit::hash_bits` expects.
fn be64_bits(limb_bits: &[Vec<EVar>; 4]) -> Vec<EVar> {
    let mut out = Vec::with_capacity(64);
    for limb in limb_bits.iter().rev() {
        out.extend_from_slice(&limb[8..16]);
        out.extend_from_slice(&limb[..8]);
    }
    out
}

/// A 256-bit number's bits, most significant first, from a digest's
/// bytes (`digest_to_bytes`: each element 4 little-endian bytes, read as
/// one big-endian number).
fn digest_bits_msb_first(element_bits: &[EVar]) -> Vec<EVar> {
    let mut out = Vec::with_capacity(256);
    for byte in 0..32 {
        let base = 32 * (byte / 4) + 8 * (byte % 4);
        out.extend(element_bits[base..base + 8].iter().rev());
    }
    out
}

/// Assert `x <= y`, both given as bits, most significant first: scanning
/// down, `lt` becomes 1 at the first position where `x` has 0 and `y` 1
/// while all before were equal.
fn assert_le(b: &mut Builder, x: &[EVar], y: &[EVar]) {
    let (o, z) = (BabyBear::ONE, BabyBear::ZERO);
    let one = b.one();
    let mut eq = b.one();
    let mut lt = b.zero();
    for (&xi, &yi) in x.iter().zip(y) {
        // (1 - x)·y = y - x·y; equal bits: 2xy - x - y + 1.
        let less_here = b.arith(-o, Some(xi), Some(yi), z, o, None, z, [z; 4]);
        let same = b.arith(BabyBear::new(2), Some(xi), Some(yi), -o, -o, Some(one), o, [z; 4]);
        lt = b.mul_add(eq, less_here, lt);
        eq = b.mul(eq, same);
    }
    let le = b.add(lt, eq);
    b.assert_eq(le, one);
}

/// Assert `x > y` for 64-bit numbers given as four 16-bit limbs (least
/// significant first): `x - y - 1` subtracts with no final borrow.
fn assert_greater(b: &mut Builder, x: &[EVar; 4], y: &[EVar; 4]) {
    let value = |b: &Builder, v: EVar| b.ext_value(v).0[0].value() as i64;
    let (o, z) = (BabyBear::ONE, BabyBear::ZERO);
    let mut borrow = b.one(); // the "- 1"
    for j in 0..4 {
        let raw = value(b, x[j]) - value(b, y[j]) - value(b, borrow);
        let (d, out) = if raw < 0 { (raw + (1 << 16), 1) } else { (raw, 0) };
        let (diff, _) = witness_limb(b, d as u32);
        let out_cell = b.witness_ext(Ext::from_base(BabyBear::new(out)));
        bits_of(b, out_cell, 1);
        // x - y - borrow + 2^16·out - diff = 0.
        let t = b.sub(x[j], y[j]);
        let t = b.sub(t, borrow);
        let t = b.arith(z, Some(out_cell), None, BabyBear::new(1 << 16), z, Some(t), o, [z; 4]);
        b.assert_eq(t, diff);
        borrow = out_cell;
    }
    b.assert_zero(borrow);
}

/// Lane `l` of an octet, as a base cell.
fn lane_of(b: &mut Builder, o: OVar, l: usize) -> EVar {
    let (lo, hi) = b.halves(o);
    b.lane(if l < 4 { lo } else { hi }, l % 4)
}

// ---- proof of work ---------------------------------------------------------------

/// The header's proof-of-work value (`pow::pow_value`), from its attempt's
/// output `out` (`native`, its values): each lookup's index from the mix,
/// the item read proven against the dataset tree's root (built in), the
/// mixing (`pow::fold`), and the final hash.
fn pow_value(b: &mut Builder, params: &crate::pow::Params, out: [OVar; 3], native: &[BabyBear; 24]) -> OVar {
    use crate::pow::{self, ITEM_ELEMS, MIX};
    let tree = pow::dataset_tree(*params);
    let root = b.const_octet(tree.root());
    let k: Vec<EVar> = pow::K.iter().map(|&c| b.const_base(BabyBear::new(c))).collect();
    let mut mix: Vec<EVar> = (0..MIX).map(|e| lane_of(b, out[1 + e / 8], e % 8)).collect();
    for (index, item) in pow::lookups(params, native) {
        let sum = mix[1..].iter().fold(mix[0], |acc, &m| b.add(acc, m));
        let bits = canonical_bits(b, sum);
        let cells: Vec<EVar> = item.iter().map(|&v| b.witness_ext(Ext::from_base(v))).collect();
        let octets = pack_octets(b, &cells);
        let mut h = recursion::hash_octets(b, pow::DOMAIN_ITEM_LEAF, ITEM_ELEMS * 4, &octets);
        for (level, sibling) in tree.path(index).iter().enumerate() {
            let sibling = b.witness_octet(*sibling);
            let cap = b.const_octet(pow::node_capacity(level));
            h = b.permute(h, sibling, cap, Some(bits[level]))[0];
        }
        b.assert_eq_octet(h, root);
        let acc: Vec<EVar> = (0..MIX)
            .map(|e| {
                let mut a = b.zero();
                for c in 0..ITEM_ELEMS / MIX {
                    a = b.mul_add(cells[MIX * c + e], mix[(e + c) % MIX], a);
                }
                a
            })
            .collect();
        let t: Vec<EVar> = (0..MIX).map(|e| b.add(acc[e], mix[e])).collect();
        mix = (0..MIX).map(|e| b.mul_add(t[e], t[(e + 1) % MIX], k[e])).collect();
    }
    let mix_octets = pack_octets(b, &mix);
    recursion::hash_octets(b, pow::POW_DOMAIN, 24, &[out[0], mix_octets[0], mix_octets[1]])
}

// ---- the chain step ------------------------------------------------------------

/// The chain step for `header`, given the previous header's chain proof
/// and the block's root proof.
fn step_circuit(child: &ChainProof, block: &Node, header: &BlockHeader, tip: &Tip, keys: &StepKeys, self_vk: Octet, tree: &TreeParams) -> Result<Circuit, Error> {
    fit(step_builder(child, block, header, tip, keys, self_vk, tree)?, tree)
}

/// The keys a step builds in: the genesis circuit's, and the block tree's
/// wrap and aggregation circuits'.
#[derive(Clone, Copy, Debug)]
pub struct StepKeys {
    pub genesis: Octet,
    pub wrap: Octet,
    pub aggregate: Octet,
    /// The retarget rule's parameters.
    pub difficulty: crate::chain::DifficultyConfig,
}

/// `step_circuit`, laid out but not yet padded.
fn step_builder(child: &ChainProof, block: &Node, header: &BlockHeader, tip: &Tip, keys: &StepKeys, self_vk: Octet, tree: &TreeParams) -> Result<Builder, Error> {
    let genesis_vk = keys.genesis;
    if header.prev_hash != child.tip.hash || tip.hash != header.hash() {
        return Err(Error::InvalidProof);
    }
    let (mut b, public) = Builder::with_public(&tip.public(self_vk));
    let (self_lo, self_hi) = b.halves(public[0]);

    // The child: a chain proof by the genesis circuit or by this one.
    let statement = recursion::verify(&mut b, &child.air, &child.proof, &tree.params).ok_or(Error::InvalidProof)?;
    if statement.tuples.len() != 9 {
        return Err(Error::InvalidProof);
    }
    let mut tuple_header = octet_of(-BabyBear::ONE);
    tuple_header[1] = BabyBear::new(9);
    let tuple_header = b.const_octet(tuple_header);
    for (k, (cells, &h)) in statement.tuples.iter().zip(&statement.tuple_headers).enumerate() {
        b.assert_eq_octet(h, tuple_header);
        let address = b.const_octet(octet_of(BabyBear::new(k as u32)));
        b.assert_eq_octet(cells[1], address);
    }
    let [c_vk, c_hash, c_info, c_t0, c_t1, c_state, c_ws, c_w0, c_w1] = std::array::from_fn(|k| statement.tuples[k][0]);
    let cap = statement.preprocessed_cap.ok_or(Error::InvalidProof)?;
    let cap_octets = recursion::table_octets(&cap);
    let key = recursion::hash_octets(&mut b, DOMAIN_VK, 8 * cap_octets.len(), &cap_octets);
    let is_step = vk_digest(&child.air.preprocessed_commitment().cap) == self_vk;
    let s = b.witness_ext(Ext::from_base(BabyBear::new(is_step as u32)));
    let s_squared = b.mul(s, s);
    b.assert_eq(s_squared, s);
    let genesis = b.const_octet(genesis_vk);
    let (genesis_lo, genesis_hi) = b.halves(genesis);
    let (key_lo, key_hi) = b.halves(key);
    assert_select(&mut b, key_lo, s, genesis_lo, self_lo);
    assert_select(&mut b, key_hi, s, genesis_hi, self_hi);
    let (vk_lo, vk_hi) = b.halves(c_vk);
    for (mine, theirs) in [(self_lo, vk_lo), (self_hi, vk_hi)] {
        let d = b.sub(theirs, mine);
        let gated = b.mul(s, d);
        b.assert_zero(gated);
    }

    // The header's fields.
    let state_root = public[5];
    let body_hash = b.witness_octet(digest_from_bytes(&header.body_hash));
    // Any 32 bytes.
    let aux_bits: Vec<EVar> = header
        .aux_hash
        .iter()
        .flat_map(|&byte| {
            let cell = b.witness_ext(Ext::from_base(BabyBear::new(byte as u32)));
            bits_of(&mut b, cell, 8)
        })
        .collect();
    // The output count: below 2^DEPTH, as its two `wide` limbs.
    use crate::state_tree::{DEPTH, LIMB_BITS};
    if header.output_count >= 1 << DEPTH {
        return Err(Error::InvalidProof);
    }
    let count: Vec<(EVar, Vec<EVar>)> = limbs16(header.output_count).iter().map(|&l| witness_limb(&mut b, l)).collect();
    let count_bits: Vec<EVar> = count.iter().flat_map(|c| c.1.clone()).collect();
    for &bit in &count_bits[DEPTH..] {
        b.assert_zero(bit);
    }
    let count_out = [from_bits(&mut b, &count_bits[..LIMB_BITS]), from_bits(&mut b, &count_bits[LIMB_BITS..DEPTH])];
    let timestamp: Vec<(EVar, Vec<EVar>)> = limbs16(header.timestamp).iter().map(|&l| witness_limb(&mut b, l)).collect();
    // Height: the child's plus one, below 2^31 (so its limbs are unique).
    let child_height = lane_of(&mut b, c_info, 0);
    let height = b.add_base(child_height, BabyBear::ONE);
    let (h0, h0_bits) = witness_limb(&mut b, (header.height & 0xffff) as u32);
    let h1 = b.witness_ext(Ext::from_base(BabyBear::new((header.height >> 16) as u32)));
    let mut h1_bits = bits_of(&mut b, h1, 15);
    h1_bits.push(b.zero());
    let composed = b.arith(BabyBear::ZERO, Some(h1), None, BabyBear::new(1 << 16), BabyBear::ZERO, Some(h0), BabyBear::ONE, [BabyBear::ZERO; 4]);
    b.assert_eq(composed, height);
    // ... and canonical (`canonical_bits`), so the bits are the height's
    // own, not the height plus p.
    let height_bits: Vec<EVar> = h0_bits.iter().chain(&h1_bits[..15]).copied().collect();
    {
        let mut top = height_bits[27];
        for &bit in &height_bits[28..31] {
            top = b.mul(top, bit);
        }
        let low = from_bits(&mut b, &height_bits[..27]);
        let both = b.mul(top, low);
        b.assert_zero(both);
    }

    // The block's proof: by the tree's wrap or aggregation circuit,
    // claiming exactly the reward at this height, from the parent's state
    // to this one's.
    let reward = scheduled_reward(&mut b, &keys.difficulty.schedule, &height_bits);
    let (count_in, block_out) = block_proof(&mut b, block, keys, tree, c_state, public[5], height, &reward)?;
    for l in 0..2 {
        let child_count = lane_of(&mut b, c_info, 5 + l);
        b.assert_eq(count_in[l], child_count);
        b.assert_eq(block_out[l], count_out[l]);
    }
    let zero_bits = vec![b.zero(); 16];
    // Strictly after the child's timestamp.
    let child_ts: [EVar; 4] = std::array::from_fn(|j| lane_of(&mut b, c_info, 1 + j));
    let ts: [EVar; 4] = std::array::from_fn(|j| timestamp[j].0);
    assert_greater(&mut b, &ts, &child_ts);
    // The nonce: 32 bytes, as `pow::attempt` takes it -- three bytes to
    // an element.
    let nonce_bytes: Vec<EVar> = header
        .nonce
        .iter()
        .map(|&byte| {
            let cell = b.witness_ext(Ext::from_base(BabyBear::new(byte as u32)));
            bits_of(&mut b, cell, 8);
            cell
        })
        .collect();
    let nonce: Vec<EVar> = nonce_bytes
        .chunks(3)
        .map(|c| {
            let mut e = c[c.len() - 1];
            for &byte in c[..c.len() - 1].iter().rev() {
                let shifted = b.scale(e, BabyBear::new(256));
                e = b.add(shifted, byte);
            }
            e
        })
        .collect();

    // The header's id (`pow::header_id`): its prefix -- every field but
    // the nonce, hashed as bytes -- and the nonce, through one
    // permutation, which also starts the proof of work's mix.
    let mut bits = digest_bits(&mut b, c_hash);
    bits.extend(digest_bits(&mut b, state_root));
    bits.extend(digest_bits(&mut b, body_hash));
    bits.extend(aux_bits);
    bits.extend(be64_bits(&std::array::from_fn(|j| count[j].1.clone())));
    bits.extend(be64_bits(&[h0_bits, h1_bits, zero_bits.clone(), zero_bits]));
    bits.extend(be64_bits(&std::array::from_fn(|j| timestamp[j].1.clone())));
    let prefix = hash_bits(&mut b, &bits);
    let domain = b.const_base(BabyBear::new(crate::pow::ATTEMPT_DOMAIN));
    let zero = b.zero();
    let nonce_lo = pack_octets(&mut b, &nonce[..8])[0];
    let capacity = pack_octets(&mut b, &[nonce[8], nonce[9], nonce[10], domain, zero, zero, zero, zero])[0];
    let out = b.permute(prefix, nonce_lo, capacity, None);
    b.assert_eq_octet(out[0], public[1]);

    // Proof of work: the memory-bound value, as a 256-bit number, at most
    // the target.
    let native = crate::pow::attempt(&crate::pow::prefix(&header.pow_preimage()), &header.nonce);
    let value = pow_value(&mut b, &keys.difficulty.pow, out, &native);
    let hash_bits_msb = {
        let element_bits = digest_bits(&mut b, value);
        digest_bits_msb_first(&element_bits)
    };
    let mut target_bits = Vec::with_capacity(256);
    for octet in [c_t0, c_t1] {
        for l in 0..8 {
            let limb = lane_of(&mut b, octet, l);
            let bits = bits_of(&mut b, limb, 16);
            target_bits.extend(bits.into_iter().rev());
        }
    }
    assert_le(&mut b, &hash_bits_msb, &target_bits);

    // The chain's numeric rules: the next target (retargeting), and the
    // cumulative work, this block having met the parent's target.
    let target = octets_to_bytes(&mut b, [c_t0, c_t1]);
    // (The first block's timestamp, carried unchanged from genesis.)
    let anchor: [EVar; 4] = std::array::from_fn(|j| lane_of(&mut b, c_ws, j));
    let next_target = crate::chain_rules::retarget(&mut b, &keys.difficulty, &height_bits, &ts, &anchor);
    let child_work = octets_to_bytes(&mut b, [c_w0, c_w1]);
    let work = crate::chain_rules::add_work(&mut b, &target, &child_work);

    // What this proof attests.
    let info = pack_octets(&mut b, &[height, ts[0], ts[1], ts[2], ts[3], count_out[0], count_out[1]])[0];
    b.assert_eq_octet(info, public[2]);
    let [t0, t1] = bytes_to_octets(&mut b, &next_target);
    b.assert_eq_octet(t0, public[3]);
    b.assert_eq_octet(t1, public[4]);
    let ws = pack_octets(&mut b, &anchor)[0];
    b.assert_eq_octet(ws, public[6]);
    let [w0, w1] = bytes_to_octets(&mut b, &work);
    b.assert_eq_octet(w0, public[7]);
    b.assert_eq_octet(w1, public[8]);
    Ok(b)
}

/// The chain step's key. Its fixed columns don't depend on the values, so
/// any child proof, block proof and header serve to lay it out.
pub fn step_key(sample_child: &ChainProof, sample_block: &Node, sample_header: &BlockHeader, sample_tip: &Tip, keys: &StepKeys, tree: &TreeParams) -> Result<Key, Error> {
    Ok(Key::of(&step_circuit(sample_child, sample_block, sample_header, sample_tip, keys, [BabyBear::ZERO; 8], tree)?, tree))
}

/// The keys of a chain: genesis and the step (proving keys), and what the
/// step builds in.
pub struct ChainKeys {
    pub genesis: Key,
    pub step: Key,
    pub built_in: StepKeys,
}

/// Prove `header` extends the chain `child` attests, `block` being its
/// block's root proof, and `tip` what that makes of it (the circuit
/// checks every field).
pub fn prove_step(keys: &ChainKeys, child: &ChainProof, block: &Node, header: &BlockHeader, tip: &Tip, tree: &TreeParams, seed: [u8; 32]) -> Result<ChainProof, Error> {
    let circuit = step_circuit(child, block, header, tip, &keys.built_in, keys.step.vk, tree)?;
    let air = circuit.air_with(keys.step.preprocessed.clone());
    let proof = stark::prove(&air, &circuit.witness, &tree.params, seed).map_err(Error::Prove)?;
    Ok(ChainProof {
        air,
        proof,
        tip: *tip,
    })
}

/// Whether `proof` is a chain step proof attesting `tip`.
pub fn verify(keys: &ChainKeys, tip: &Tip, proof: &Proof, tree: &TreeParams) -> bool {
    let air = CircuitAir::new(tree.trace_len, keys.step.preprocessed.clone(), public_tuples(&tip.public(keys.step.vk)));
    stark::verify(&air, proof, &tree.params)
}

/// Rows a chain step uses (before padding), for measurement.
pub fn step_rows(child: &ChainProof, block: &Node, header: &BlockHeader, tip: &Tip, keys: &StepKeys, tree: &TreeParams) -> Result<usize, Error> {
    Ok(step_builder(child, block, header, tip, keys, [BabyBear::ZERO; 8], tree)?.rows_used())
}

/// Verify a block's root proof in the circuit and check what it claims:
/// its key is the tree's wrap or aggregation circuit's (an aggregation's
/// `vk` input being that key), it balances against exactly `reward` (its
/// amount limbs), and it moves the state from `state_in` (the parent's
/// root) to `state_out` (this header's), its outputs filling the window
/// `count_in..count_out` at `height` (the header's). Returns its
/// `(count_in, count_out)`, each two limbs (`aggregate::wide`).
#[allow(clippy::too_many_arguments)]
fn block_proof(b: &mut Builder, block: &Node, keys: &StepKeys, tree: &TreeParams, state_in: OVar, state_out: OVar, height: EVar, reward: &[EVar]) -> Result<([EVar; 2], [EVar; 2]), Error> {
    use crate::aggregate::{add_amount, limbs_of};
    let statement = recursion::verify(b, &block.air, &block.proof, &tree.params).ok_or(Error::InvalidProof)?;
    if statement.tuples.len() != 8 {
        return Err(Error::InvalidProof);
    }
    let mut tuple_header = octet_of(-BabyBear::ONE);
    tuple_header[1] = BabyBear::new(9);
    let tuple_header = b.const_octet(tuple_header);
    for (k, (cells, &h)) in statement.tuples.iter().zip(&statement.tuple_headers).enumerate() {
        b.assert_eq_octet(h, tuple_header);
        let address = b.const_octet(octet_of(BabyBear::new(k as u32)));
        b.assert_eq_octet(cells[1], address);
    }
    // (`data`, `challenge` and `product` bind the body, which only
    // validators see; the state doesn't depend on them.)
    let [vk, _data, amounts, root_in, root_out, counts] = std::array::from_fn(|k| statement.tuples[k][0]);

    // Its key: wrap (s = 0) or aggregation (s = 1, carrying its own key).
    let cap = statement.preprocessed_cap.ok_or(Error::InvalidProof)?;
    let cap_octets = recursion::table_octets(&cap);
    let key = recursion::hash_octets(b, DOMAIN_VK, 8 * cap_octets.len(), &cap_octets);
    let is_aggregate = vk_digest(&block.air.preprocessed_commitment().cap) == keys.aggregate;
    let s = b.witness_ext(Ext::from_base(BabyBear::new(is_aggregate as u32)));
    let s_squared = b.mul(s, s);
    b.assert_eq(s_squared, s);
    let (wrap, aggregate) = (b.const_octet(keys.wrap), b.const_octet(keys.aggregate));
    let (wrap_lo, wrap_hi) = b.halves(wrap);
    let (agg_lo, agg_hi) = b.halves(aggregate);
    let (key_lo, key_hi) = b.halves(key);
    assert_select(b, key_lo, s, wrap_lo, agg_lo);
    assert_select(b, key_hi, s, wrap_hi, agg_hi);
    let (vk_lo, vk_hi) = b.halves(vk);
    for (mine, theirs) in [(agg_lo, vk_lo), (agg_hi, vk_hi)] {
        let d = b.sub(theirs, mine);
        let gated = b.mul(s, d);
        b.assert_zero(gated);
    }

    // Exactly the reward: a == b + reward (the limbs are range-checked by
    // the wrap and aggregation circuits).
    let limbs = limbs_of(b, amounts);
    let expected = add_amount(b, &limbs[4..], reward);
    for j in 0..4 {
        b.assert_eq(limbs[j], expected[j]);
    }

    // The height its outputs were stamped with: `[product, height, 0, 0,
    // 0]`.
    let product_hi = b.halves(statement.tuples[7][0]).1;
    b.assert_eq(product_hi, height);

    // The state.
    b.assert_eq_octet(root_in, state_in);
    b.assert_eq_octet(root_out, state_out);
    let [count_in, count_out, base, end]: [[EVar; 2]; 4] = std::array::from_fn(|k| [lane_of(b, counts, 2 * k), lane_of(b, counts, 2 * k + 1)]);
    for l in 0..2 {
        b.assert_eq(base[l], count_in[l]);
        b.assert_eq(end[l], count_out[l]);
    }
    Ok((count_in, count_out))
}

/// Whether the number with bits `bits` (lowest first) is below the
/// constant `c`: scanning down from the top, the first bit where they
/// differ is 0 in it and 1 in `c`. A bit.
fn below_const(b: &mut Builder, bits: &[EVar], c: u64) -> EVar {
    if c >> bits.len() != 0 {
        return b.one();
    }
    let mut eq = b.one();
    let mut lt = b.zero();
    for (i, &bit) in bits.iter().enumerate().rev() {
        if (c >> i) & 1 == 1 {
            // Below here if the bit is 0; still equal if it's 1.
            let below = b.sub(eq, bit);
            let below = b.mul(eq, below);
            lt = b.add(lt, below);
            eq = b.mul(eq, bit);
        } else {
            let one = b.one();
            let flipped = b.sub(one, bit);
            eq = b.mul(eq, flipped);
        }
    }
    lt
}

/// The reward the schedule gives the height whose bits are `height_bits`
/// (lowest first, canonical), as amount limbs (`output::amount_limbs`);
/// past the schedule's end, unsatisfiable.
fn scheduled_reward(b: &mut Builder, schedule: &crate::prover::Schedule, height_bits: &[EVar]) -> Vec<EVar> {
    if let Some(end) = schedule.end {
        let before_end = below_const(b, height_bits, end);
        let one = b.one();
        b.assert_eq(before_end, one);
    }
    let early = below_const(b, height_bits, schedule.first_blocks);
    let (first, then) = (crate::output::amount_limbs(schedule.first), crate::output::amount_limbs(schedule.then));
    let z = BabyBear::ZERO;
    (0..first.len())
        .map(|j| {
            // then + early·(first - then)
            let then_j = b.const_base(then[j]);
            b.arith(z, Some(early), None, first[j] - then[j], z, Some(then_j), BabyBear::ONE, [z; 4])
        })
        .collect()
}

// ---- chain proofs on a real chain -----------------------------------------------

/// Checks chain proofs: the genesis and step circuits' caps (their
/// verifying keys), at the tree parameters.
#[derive(Clone, Debug)]
pub struct ChainVerifier {
    pub genesis_cap: Vec<crate::merkle::Hash>,
    pub step_cap: Vec<crate::merkle::Hash>,
    pub tree: TreeParams,
}

impl ChainVerifier {
    pub fn of(keys: &ChainKeys, tree: TreeParams) -> Self {
        ChainVerifier {
            genesis_cap: keys.genesis.preprocessed.cap.clone(),
            step_cap: keys.step.preprocessed.cap.clone(),
            tree,
        }
    }

    /// The AIR of a chain proof attesting `tip`: the genesis circuit's for
    /// the first block, the step circuit's after.
    fn air(&self, tip: &Tip) -> CircuitAir {
        let log_lde = self.tree.trace_len.trailing_zeros() as usize + 2 + self.tree.params.log_blowup;
        let (cap, vk) = if tip.height == 0 {
            (&self.genesis_cap, [BabyBear::ZERO; 8])
        } else {
            (&self.step_cap, vk_digest(&self.step_cap))
        };
        let preprocessed = std::sync::Arc::new(crate::stark::Preprocessed::from_cap(crate::circuit::NUM_PREPROCESSED, log_lde, cap.clone()));
        CircuitAir::new(self.tree.trace_len, preprocessed, public_tuples(&tip.public(vk)))
    }

    /// Whether `bytes` is a chain proof attesting `tip`.
    pub fn verify(&self, tip: &Tip, bytes: &[u8]) -> bool {
        match Proof::from_bytes(bytes) {
            Some(proof) => stark::verify(&self.air(tip), &proof, &self.tree.params),
            None => false,
        }
    }

    /// `bytes` as a chain proof of `tip`, to verify in a step's circuit.
    pub fn proof(&self, tip: &Tip, bytes: &[u8]) -> Option<ChainProof> {
        Some(ChainProof {
            air: self.air(tip),
            proof: Proof::from_bytes(bytes)?,
            tip: *tip,
        })
    }
}

/// The chain-proof circuits' verifying keys (caps, hex) for each network:
/// derived from the circuits, the network's genesis and difficulty rule,
/// and the tree keys (the `chain_keys` test in `main` regenerates them).
const GENESIS_CAP: &str = "3c1c3e0dab62eb34b9a4d5263cb5c84eea26d42250023a7553388b37af318c003b084416580f4900c9d6a35b95bbca5fc3eb3442c5754947450c3404899e880ab2c58639687a0507e7fd64745c499a6733f8281dbf94756b1d246657bbdb9040274695454d5e62076a5296734559db1e985a2f2bdd54ad16db589716ef0f8b4232858f0efad5e33e825ccd70693a8f13d4d1314980b8671cabc743400ccfa729229a6937300cbc70b123b90454a7714586ad420bc640d31414050025b24c89770c629c2109ecd82f6d222064b9a4ca5fcb8c241674391b634ab20d539241980bb5eb8f67885a926b0cba6957be18845d51d86128c410b763f04a0302c0a7fe2dcc3544536c83215ed03141710c8cce1406efde6cac397a3dde45ab13ab70325c8b83907714c7404be9aa6648f3a2f82855e1026e4889d92f02b28b47640f6561f4be0e420ed21c2882510756559e82480b424957c363e601370f8f3ee342bf098a5bdd5ff93604181df35c3bb8446f065e515d2eae97623639c4716d682cbc767e5d134b5614684f3e272d0e4f3cee47a3502a1f58ce0c533c68b903a065d20cda2c3c34e5eceb423566f4375f0e810fdf96573c4d544d101bcb38022b221c3e0acc771f5f46a8126797860e10281f236c66331981ec833295353e2eb5d70e18ad23fc68bf6959421f2f7f0824b0c22094afbe45259d0632532f0d30df12580d07e84902e0241a46a90278260a43e10cf44a8951c9a282434be121098cd5c01c29c51f64ea119e5a30a47e037fc8a35db60f465bf4768959c6d5240256c2c62ff96e43350915443a6ae43732004e8221dc984714a291e249926a286a044d5242950a9f0569ba7e568e05f864d80fb04a637ffd46230f60116b2f8d658062872d44ad856208c93e43d8206c2de17c0f54bc621020b2fc1e304b79ba3ebb9fcf11cea49f54e167a73dfcefca54e7d0263eb88d665f3ed9ad626ee3a0324dd14e5f47c5393d8dc0c9300cf2b029ceda4e2291c74c737c13086ff55512024e5c2d5d2515d546c155e62d95af04342ff2e55678f6be2a7bc09931768d9019b5a0c72881713c6d940f34037c93d36bdc0f3f3179edaf20d4b9136a19b2af2bde15242482bea16a368fd440bbb9d81cba2b47580f591b0517a597020d83fe4a1e20721651a9b8098622ef0340e0f059afe35b444c8c20665f9ca10300c4e8402215370ad3f0ab6c2e99de19ce04be54591ada40bd3cad3649984e2bc2f52321d536925726c8ed0f4c821b6e586ce46ad0eb9c4f3b21b81b2c5403455b44196f9d33b915c027b50f4e3d956e36b1055ba8230741ee020e27b2f7ff3496fd830d3346aa26593984104bd81f770e5ded15f4acd16b42a3ee1d20bea36e57b884707f8885536ef51d1b023e0a15ec3f68241f76a7650049d62e3f165644c66cad2ab447fa69";
const STEP_CAP: &str = "26427c4cd7ab421502aef02343818c65f682f73b312dcc0bf42bc55a4b304a3500a68a3b6b9e29228f149a50ba0d9101f10e5a066065e506f6a3104a28d76b2b66dbe731cdf4e75588ba37650594552026ae981e9be37f225de243036a24a24a201ef52c98301337fe2ef27505528f582754c13b773432390b08056e21ff9a5c63523139eb41532f5beb4b24a3c12b459cec8844c681a16d008d731ffb9fe76b513437529bf1d229fd075506a55fd85d8ca06c5fabfff76660003245dd58d902234df0548dd88a01cd2e7e41b3ca44266977b300a34bcb53c9ce5524f1096f16c38072443f22ff2fc5072d437e68832991122e46742aa14b7f015e194895a444a6cd961929a2dc23e732e8027f43587113e13c268ac2e6654177d31e6ba0c66061f7107634997c3d025fa13f031e3d3ecf1c966aa11660373647643596336d010f3f141a1c7b7566a271a7343fe1515d63ef533e4029776de03f372465e6ed23e842c64ce35fa3185aa5a42b32cf5e75b2979642599151490fd4bf3893a77350ee8f19680e4584058ed9ea3260d8ae5818902c4494ea28495d0da225c220f826d9b9cc6ad7a9ed314aa98916cffb9d48d2617a45af953936ce068c48708d842c14c27171507deb0830718d1cd337ca084abaf71fd8ba740a3fb978462f35b06e1fa4b91b21010d55140e854dbbb82f58e9a348189dab4e2b1475290fa07daa53c226e542a7930941525fc6170c9e6d38c1e9d72a814f805e388431726200443815020d738eb15f3d80172a1688a0330e3b1c484ac867681399b4f64464fd9a06c0a2ef603d17b0258efbbc5adcb9191dcc2ecf170a563f17b7cb1a4c7dd6af18d954e71a9b72382fe96abb1951b7cd287dfcba2c23307926a1fcb370bfa55b331267c44ff777c6137d691d54a29a596836e23a31e758ea604c33af1524b7910a88a2fe247b64500fd080de07e9244c3b592df04b3814d05d89c2af02418fb41f61b67030998768602f9a5b31ba724e3a66b52417106dc32dbf3d2a22c716f46bdbb95e6ef9fd945d0d45f570cb510f06f369877252675a6a692c6043c5d75528ef55382b33eb1e24b362256a7b67e20e61cbbe58aada725449d35441c254d5269481692be417182d88e3cd414655973b5bcfb63c82c3e74b690fc22192d784124745901d34a413119ccae058a69dc96c763c9e4559ca8d4579c2d203b26d1063c3548c1d3e2f586b354855350c283f4f000abf482939424e12d34c72e712ef5e05afae1c244d0e4d43756563e479564e08d4f65283a1602e6c04cf5d7be5be515870ac6db0c52431dbab04667a3b802aea7e555940482715a67e755e2cf86f3d2f5fda5eda68915912be0a34d4c99723f750f30f9c2b691ad433626cb6eb962d8d76580d9ee74a533e278417dd9d7d166036625640951472f6a48716e9b26b34";
const DEV_GENESIS_CAP: &str = "73bb8c64034f596731c19544cd86c9221b37b6015b1cd234ee36fa0e89e6b748c67ecc273a797744ef52552bf089496d091b304c09fc802ecd971a2bdcb3e83f4aa4243908bde74616720759d0ab9111bdcbd93d6ea3dd407a32264b65251c23e1d8fc59fe94b51076d8af3ea811a03a82944925d2c44d55d7738a3ad675656f93cd0709fd114440c69b012e4a98d44574f04b0a612ee22e00a03b2018fcf4718c2255366417d13d57eab21b4a4d53660a2d2a4c85a3756365846607b5534c4d3f77ea4d2605762d0f23b20a2e3c5f64a5ef641bfb437a4f91b1e147923d4d5a02bebd3ee76f2228bf18fa2cb1d9150ee877b373c9a76657dffd3c5841fe0e0a047e41000d4d3a3118a8646f556c750086fc5e690655aa136d7b6f04bc23795ca892576a016691116b2782119692593683f9f02ef69ed049958ff83b14b6a26cf526e308b67c4a51f27711317ee0934e99b8841be076fb1721014209c06eac45cefb0557692821707f13a46374091e4e8653662a35fbea11e8fa8a3c329dd84dd4276c04b2cd1c27718fc647d4352b6fde91c54797466866717b6a2c70f5c8753ede696eb2bf7e2463f8d4531b5df7559c9a311a341cc82b0875295f44ca724e50a5d65e87c08034f85bae5af210e16113638051cf944b58835dd06f04130d0789123a148639e733be8851041f5a6b5473c8f64b38abb339dc637e5f6690f9455f58dd1631afd1766c4b7f5ec5f30f47245bc56a1c08ce2715bbca29d8025f73cabed8531ef69b1d5c38d02e0e26634f05f7274a96311f614f580d537e6a961bf41e621e219a047632f05e1acb317e28de98ee27a2601d035ad01263ae4bb65ecfbb6e46db62483e3e060f3a5cab8a471886650b339a1e242b0bba62283b0f409a016d48f4d8310f448b813cec2ec73812720902e0c8433b733eaf2f0bf61413ba33e24b2763803339b7d2729b63e04d1690ab5d0d3e2a52a7628b58a60c1d6f414b7f428c227c55940a86390e24be642d9ed42f3f3125157d97b123b0466f00178cac54da602160791eaa326b43a7775300096b7924d15dbeabba762062894ee8c3e91ab208410269f23659bd347e14b0ad9b6e64de9019f7b03a4ea3a057447477341dc24eb32b6463f62c2b9873042e0d3f72b07256706e86c8014abf661775f8561d07d5f1758c1ce83fc8e174583e53901ed9627760c061d40f9f00fb0046282145d5437c7112105f706d3b3f3d7f780245e961666bc987a15706672c195c6771229def915aa970201b49afab65553968757689f2600d25db20a25d795d90aff12e5f30b856d1f8c204bd95fe75e3af7540f7f8d966852b295cef7e5c0301e5b70e7b7531372fd2c24fc439ed4e4d8c4167c1344338d1adc375a9e603316b97dc252ba38172991b8160137dca5108c97050a574f03eb98cd2534c92bd73";
const DEV_STEP_CAP: &str = "fac84b3d29a61162a7e4d8656a8dbc1fe0baa77624ea86576c0cd122637f26093f36db6b5b88f63efa682b51d44eee1621501631e0664b705d7ff95cc79083583c7c5274ae248f4ffd895004e5ae8771849d684b91eecf20292b7a52cc6ee16006623a239d4d3542e1ca9d31ba96822e07daec5f52b656169467cf5f68a8bc20bb63550b654fc9055acc9d1cb3e1fa13a6c02f4f9bcef21aaf58154fe39c114dc7072b66042e8430804ac2426ac5e0149188a113f5bc174f9771c6327cdb3f0fd211c9538004a313c05da574fc9b632afc829929f9656317cd23f147ebed593f4d84be295f32f71cc7213d4bbddec92e4547e96918192f7514d9751ed3c85e58aa307e5a736d295fd018462a82a4076b51e5db47fe39490634cb721dbee1822c95841c0a0caa113911625f67ecf65171344bf81e9b5c642805bb726b53004a2d5bf30431e5cb1561aee90f6685a31362936c8038fcdad21604ba207695910729bc6889660b843a74031a0a5931008114d2890a685bf4df538c5ef35434daee67df05fc57c136b36932da4436b0cd664fea5f54056026b54a3f600374dbf5803437e78c0715b8155c564be865226a9c0c8b106a6d61f44f43bf134f57f9289523cf369a4dad45532838936f54279db568b349af1e9936a45c15328b4ba70da1723a1f2f564184c8658c22a62b0ce4543883f46a3c0f244b517b6b654ae71c1b33c1a795591b66914e78c2c71c0c84db2e6744e7434a40d46d479169727fdc1d0eb4c82d5280db7d0c796e66388c8e71637140347452962b3e769e0f2d19a8b1730f6b372823404d5b3f8daf50a563216bfea9b50ea9ab0312354f8a609cd88918fd9abd053f5ae377d1cc9d1b6ccc74439ef5023b4c8fd6137687184a7c1d7c3a844d7f7587e73d677a84ec4bf5751a4c545a615f928623070febe2163310cd133c4d2d0c057bba7161872f2a2ef21015946d542d8568cc4d5783a53595172674f33b0e58ea4ced771e2d1e65223c165438daae22b77bd4215d67be0392a7875560234e0d59fdbc517537d5204686914f8eeb311accdf8718efd75f1c0ec3395c37c58a72dbebd8646c2e18418b81b55fe9c58670ced5a801505ac93467b0fd3edd11713d30931756bdbd9341031be32fa1a06e7634caad338e25fa4f9d2ad77439d17847f1be306c7c476f0f79c9861a0f85ef06da017426dad2cf05ef95b3222bfe235fe9451a2ba3c05f03170dba5c40ebbb2832b38a0464e0e815a1b2c053abae37543a6b6c07680211301e485c295d64aa12072a0d032bc7eb5af354ce752a8dd5375da9eb09b7f2ad6d663c0a28fbc77e70e689157707c4881aa859966bb6057c59d80963328be37235f443d437e0465712294db02104ab7858c3e9b912e3e84f15f368c5555605f41c0365493d8de4c7518157b53ea3ecfc2191ad4029";

fn cap_from_hex(hex: &str) -> Vec<crate::merkle::Hash> {
    let bytes: Vec<u8> = (0..hex.len() / 2).map(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap()).collect();
    bytes.chunks_exact(32).map(|c| c.try_into().unwrap()).collect()
}

pub fn cap_to_hex(cap: &[crate::merkle::Hash]) -> String {
    cap.iter().flatten().map(|b| format!("{b:02x}")).collect()
}

/// This network's chain-proof verifier (consensus constants).
pub fn consensus_verifier() -> ChainVerifier {
    let (genesis, step) = match crate::network::current() {
        crate::network::Network::Main => (GENESIS_CAP, STEP_CAP),
        crate::network::Network::Dev => (DEV_GENESIS_CAP, DEV_STEP_CAP),
    };
    ChainVerifier {
        genesis_cap: cap_from_hex(genesis),
        step_cap: cap_from_hex(step),
        tree: crate::prover::tree(),
    }
}

/// Everything needed to prove a block's chain proof, all from chain data
/// (`chain::Chain::chain_proof_inputs`).
#[derive(Clone, Debug)]
pub struct ChainProofInputs {
    pub header: BlockHeader,
    pub tip: Tip,
    /// For any block but the first: its body and proof, its parent's tip,
    /// and the parent's chain proof (from this block's own body).
    pub block: Option<BlockInputs>,
}

#[derive(Clone, Debug)]
pub struct BlockInputs {
    pub inputs: Vec<[u8; 32]>,
    pub outputs: Vec<[u8; 32]>,
    pub nonces: Vec<[u8; crate::recovery::NONCE_LEN]>,
    pub proof: crate::prover::Proof,
    pub state: crate::aggregate::StateChange,
    pub parent_tip: Tip,
    pub parent_chain_proof: Vec<u8>,
}

/// Produces chain proofs, deriving its proving keys when it first needs
/// them: the genesis circuit's from the first block's tip, the step's
/// from the second block (whose body holds the first's chain proof --
/// any consistent sample lays the circuit out the same).
pub struct ChainProver {
    difficulty: crate::chain::DifficultyConfig,
    tree: TreeParams,
    genesis: Option<Key>,
    step: Option<Key>,
}

impl ChainProver {
    pub fn new(difficulty: crate::chain::DifficultyConfig, tree: TreeParams) -> Self {
        ChainProver {
            difficulty,
            tree,
            genesis: None,
            step: None,
        }
    }

    /// The keys a step builds in, given the genesis key.
    fn built_in(&self, genesis: &Key) -> StepKeys {
        let (wrap, aggregate) = crate::prover::tree_vks();
        StepKeys {
            genesis: genesis.vk,
            wrap,
            aggregate,
            difficulty: self.difficulty,
        }
    }

    /// Both keys, once derived.
    pub fn keys(&self) -> Option<ChainKeys> {
        let (genesis, step) = (self.genesis.clone()?, self.step.clone()?);
        let built_in = self.built_in(&genesis);
        Some(ChainKeys { genesis, step, built_in })
    }

    fn genesis_key(&mut self, genesis_tip: &Tip) -> Result<Key, Error> {
        if self.genesis.is_none() {
            self.genesis = Some(genesis_key(genesis_tip, &self.tree)?);
        }
        Ok(self.genesis.clone().unwrap())
    }

    /// A verifier for what's been derived so far (the genesis circuit's
    /// proofs; the step's once its key is), if anything has.
    pub fn verifier(&self) -> Option<ChainVerifier> {
        self.genesis.as_ref().map(|g| self.partial_verifier(g))
    }

    /// The verifier for the genesis circuit's proofs, and (once derived)
    /// the step's.
    fn partial_verifier(&self, genesis: &Key) -> ChainVerifier {
        ChainVerifier {
            genesis_cap: genesis.preprocessed.cap.clone(),
            step_cap: self.step.as_ref().map(|k| k.preprocessed.cap.clone()).unwrap_or_default(),
            tree: self.tree,
        }
    }

    /// Lay out the step for `inputs` (a block after the first) and its
    /// proving pieces: the child chain proof and the block's root.
    fn step_parts(&self, genesis: &Key, inputs: &ChainProofInputs) -> Result<(ChainProof, Node, BlockInputs), Error> {
        let block = inputs.block.clone().ok_or(Error::InvalidProof)?;
        let child = self.partial_verifier(genesis).proof(&block.parent_tip, &block.parent_chain_proof).ok_or(Error::InvalidProof)?;
        let height = u32::try_from(inputs.header.height).map_err(|_| Error::InvalidProof)?;
        let root = crate::prover::block_root(&block.proof, &block.inputs, &block.outputs, &block.nonces, &block.state, height).ok_or(Error::InvalidProof)?;
        Ok((child, root, block))
    }

    /// Prove the chain proof for `inputs`' block. `second` is the second
    /// block's inputs (its parent the first), to derive the step key from
    /// the first time one is needed.
    pub fn prove(&mut self, inputs: &ChainProofInputs, second: impl FnOnce() -> Option<ChainProofInputs>, seed: [u8; 32]) -> Result<Vec<u8>, Error> {
        let Some(block) = &inputs.block else {
            let key = self.genesis_key(&inputs.tip)?;
            return Ok(prove_genesis(&key, &inputs.tip, &self.tree, seed)?.proof.to_bytes());
        };
        // The keys, the first time: from the second block's inputs (this
        // block's own, or fetched).
        if self.genesis.is_none() || self.step.is_none() {
            let sample = if block.parent_tip.height == 0 { inputs.clone() } else { second().ok_or(Error::InvalidProof)? };
            let first_tip = sample.block.as_ref().ok_or(Error::InvalidProof)?.parent_tip;
            let genesis = self.genesis_key(&first_tip)?;
            if self.step.is_none() {
                let (child, root, _) = self.step_parts(&genesis, &sample)?;
                self.step = Some(step_key(&child, &root, &sample.header, &sample.tip, &self.built_in(&genesis), &self.tree)?);
            }
        }
        let genesis = self.genesis.clone().ok_or(Error::InvalidProof)?;
        let keys = self.keys().ok_or(Error::InvalidProof)?;
        let (child, root, _) = self.step_parts(&genesis, inputs)?;
        Ok(prove_step(&keys, &child, &root, &inputs.header, &inputs.tip, &self.tree, seed)?.proof.to_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block::{Block, BlockHeader, mine_block};
    use crate::chain::{Chain, DifficultyConfig};
    use crate::output::Output;
    use crate::storage::Storage;
    use crate::transaction::Transaction;

    struct TempDir(std::path::PathBuf);

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    /// A real chain: an empty first block (the genesis), then `n` blocks,
    /// each paying the reward to a fresh key, proven for real (this
    /// network's parameters: run with `NETWORK=dev` for speed). Returns
    /// the genesis header, each block's header and root proof, and the
    /// target they were mined at.
    /// (The chain itself comes back too: each block's `Tip` is what it
    /// records, `Chain::proof_state`.)
    #[allow(clippy::type_complexity)]
    fn chain_of(n: u8) -> (TempDir, Chain, BlockHeader, Vec<(BlockHeader, Node)>, [u8; 32]) {
        let dir = TempDir(std::env::temp_dir().join(format!("chain-step-{}-{n}", std::process::id())));
        let storage = Storage::open(&dir.0).unwrap();
        let config = DifficultyConfig::for_tests();
        let target = config.initial_target;
        let mut chain = Chain::open(&storage, config, 5, None).unwrap();
        chain.skip_proof_checks(); // proving checks them itself
        let mine = |chain: &mut Chain, unproven: crate::block::UnprovenBlock, proof: crate::prover::Proof| -> Block {
            let (target, min_timestamp) = (unproven.target, unproven.min_timestamp);
            let mut block = unproven.finish(proof);
            block.header.timestamp = block.header.timestamp.max(min_timestamp);
            assert!(mine_block(&mut block, &target, u64::MAX, &crate::pow::Params::TEST));
            chain.apply_block(&block).unwrap();
            block
        };
        let unproven = chain.build_block(&[]).unwrap();
        let genesis = mine(&mut chain, unproven, crate::prover::Proof::placeholder()).header;
        let mut blocks = Vec::new();
        for k in 0..n {
            let (_, pk) = crate::wots::keygen(&[40 + k; 32]);
            let mut tx = Transaction::new();
            tx.add_output(Output::new(&pk, crate::prover::REWARD)).unwrap();
            let txs = [tx];
            let unproven = chain.build_block(&txs).unwrap();
            let (proof, root) =
                crate::prover::prove_block_with_root(&unproven.inputs, &unproven.outputs, &unproven.nonces, &txs, &unproven.plan, [k; 32]).unwrap();
            let block = mine(&mut chain, unproven, proof);
            blocks.push((block.header, root));
        }
        (dir, chain, genesis, blocks, target)
    }

    fn built_in(genesis: &Key) -> StepKeys {
        let (wrap, aggregate) = crate::prover::tree_vks();
        StepKeys { genesis: genesis.vk, wrap, aggregate, difficulty: DifficultyConfig::for_tests() }
    }

    fn tip(chain: &Chain, header: &BlockHeader) -> Tip {
        Tip::new(header, chain.proof_state(header.hash()).unwrap())
    }

    /// Genesis, then two chain steps, each verifying its predecessor's
    /// chain proof and its own block's proof inside its circuit; the last
    /// proof alone vouches for both blocks -- their headers, and their
    /// transactions and state. Then: a header that doesn't link, a block
    /// proof for another block's state, or a timestamp that doesn't move
    /// forward can't be proven. Run with `NETWORK=dev cargo test --release
    /// -- --ignored --nocapture a_chain_of_blocks_proves_recursively`.
    #[test]
    #[ignore]
    fn a_chain_of_blocks_proves_recursively() {
        let tree = crate::prover::tree();
        let (_dir, chain, g, blocks, _target) = chain_of(2);
        let g_tip = tip(&chain, &g);
        assert_eq!(g_tip.state_root, crate::state_tree::empty_root());
        let genesis = genesis_key(&g_tip, &tree).unwrap();
        let g_proof = prove_genesis(&genesis, &g_tip, &tree, [1; 32]).unwrap();
        let [(h1, r1), (h2, r2)] = [&blocks[0], &blocks[1]];
        let (t1, t2) = (tip(&chain, h1), tip(&chain, h2));
        let keys_in = built_in(&genesis);
        let step = step_key(&g_proof, r1, h1, &t1, &keys_in, &tree).unwrap();
        let keys = ChainKeys { genesis, step, built_in: keys_in };
        let p1 = prove_step(&keys, &g_proof, r1, h1, &t1, &tree, [2; 32]).unwrap();
        assert!(verify(&keys, &p1.tip, &p1.proof, &tree));
        let p2 = prove_step(&keys, &p1, r2, h2, &t2, &tree, [3; 32]).unwrap();
        assert!(verify(&keys, &p2.tip, &p2.proof, &tree));
        assert_eq!((p2.tip.height, p2.tip.output_count, p2.tip.state_root), (2, 2, h2.state_root));
        assert!(p2.tip.work > p1.tip.work);
        // Claiming anything else about the tip fails.
        let tampers: [fn(&mut Tip); 7] = [
            |t| t.height += 1,
            |t| t.hash[0] ^= 1,
            |t| t.output_count += 1,
            |t| t.state_root[0] ^= 1,
            |t| t.target[5] ^= 1,
            |t| t.anchor_timestamp += 1,
            |t| t.work[31] ^= 1,
        ];
        for tamper in tampers {
            let mut wrong = p2.tip;
            tamper(&mut wrong);
            assert!(!verify(&keys, &wrong, &p2.proof, &tree));
        }

        let refused = |r: std::thread::Result<Result<ChainProof, Error>>| r.is_err() || r.unwrap().is_err();
        let attempt = |child: &ChainProof, root: &Node, header: &BlockHeader, tip: &Tip| {
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| prove_step(&keys, child, root, header, tip, &tree, [4; 32])))
        };
        // A header that doesn't link to the proven tip.
        assert!(refused(attempt(&p2, r2, h1, &t1)));
        // Block 2's header, with block 1's proof (the wrong state change).
        assert!(refused(attempt(&p1, r1, h2, &t2)));
        // A timestamp that doesn't advance.
        let mut early = h2.clone();
        early.timestamp = h1.timestamp;
        assert!(crate::block::mine_header(&mut early, &p1.tip.target, u64::MAX, &crate::pow::Params::TEST));
        let early_tip = Tip { hash: early.hash(), timestamp: early.timestamp, ..t2 };
        assert!(refused(attempt(&p1, r2, &early, &early_tip)));
        // The right block, but claiming more work than it did.
        let mut greedy = t2;
        greedy.work[31] ^= 1;
        assert!(refused(attempt(&p1, r2, h2, &greedy)));
    }

    fn check(b: Builder) {
        assert!(holds(b));
    }

    /// Whether the circuit's constraints hold.
    fn holds(b: Builder) -> bool {
        let circuit = b.finish();
        let params = stark::Params {
            log_blowup: 1,
            num_queries: 4,
            grinding_bits: 0,
            hiding: false,
        };
        let air = circuit.air(&params);
        let mut t = crate::transcript::Transcript::new(b"pow circuit test");
        let challenges: Vec<Ext> = (0..2).map(|_| t.challenge_ext(b"c")).collect();
        stark::check(&air, &circuit.witness, &challenges).is_ok()
    }

    /// The circuit's reward is the schedule's at every height around its
    /// boundaries, and past the end no reward satisfies it.
    #[test]
    fn the_reward_in_the_circuit_follows_the_schedule() {
        use crate::prover::{DEV_SCHEDULE, MAIN_SCHEDULE};
        let first = MAIN_SCHEDULE.first_blocks;
        let end = MAIN_SCHEDULE.end.unwrap();
        for schedule in [MAIN_SCHEDULE, DEV_SCHEDULE] {
            for height in [0, 1, first - 1, first, first + 1, end - 1, end, end + 1, (1 << 27) - 1, crate::poseidon2::P as u64 - 1] {
                let build = || {
                    let mut b = Builder::new();
                    let x = b.witness_ext(Ext::from_base(BabyBear::new(height as u32)));
                    let bits = canonical_bits(&mut b, x);
                    let reward = scheduled_reward(&mut b, &schedule, &bits);
                    let limbs: Vec<BabyBear> = reward.iter().map(|&l| b.ext_value(l).0[0]).collect();
                    (b, limbs)
                };
                match schedule.reward(height) {
                    Some(expected) => {
                        let (b, limbs) = build();
                        assert_eq!(limbs, crate::output::amount_limbs(expected).to_vec(), "height {height}");
                        assert!(holds(b), "height {height}");
                    }
                    // (The builder refuses a failing assertion outright.)
                    None => assert!(std::panic::catch_unwind(build).is_err(), "height {height}"),
                }
            }
        }
    }

    /// The proof-of-work gadget computes exactly the native value, and its
    /// constraints hold; canonical bits hold at the field's edges.
    #[test]
    fn proof_of_work_in_the_circuit_matches_native() {
        let params = crate::pow::Params::TEST;
        for c in 0..3u64 {
            let mut nonce = [0u8; 32];
            nonce[..8].copy_from_slice(&c.to_le_bytes());
            let header = format!("header {c}");
            let native = crate::pow::attempt(&crate::pow::prefix(header.as_bytes()), &nonce);
            let mut b = Builder::new();
            let out: [OVar; 3] = std::array::from_fn(|k| b.witness_octet(native[8 * k..8 * k + 8].try_into().unwrap()));
            let value = pow_value(&mut b, &params, out, &native);
            assert_eq!(
                crate::poseidon2::digest_to_bytes(b.octet_value(value)),
                crate::pow::pow_value_of(header.as_bytes(), nonce, &params)
            );
            check(b);
        }
        let mut b = Builder::new();
        for v in [0, 1, (1 << 27) - 2, (1 << 27) - 1, crate::poseidon2::P - 1] {
            let x = b.witness_ext(Ext::from_base(BabyBear::new(v)));
            let bits = canonical_bits(&mut b, x);
            assert_eq!(bits.len(), 31);
        }
        check(b);
    }

    /// Rows the proof of work adds to the chain step, with the real
    /// parameters. `cargo test --release -- --ignored --nocapture
    /// pow_circuit_rows`.
    #[test]
    #[ignore]
    fn pow_circuit_rows() {
        for (name, params) in [("main", crate::pow::Params::MAIN), ("dev", crate::pow::Params::DEV)] {
            let native = crate::pow::attempt(&crate::pow::prefix(b"rows"), &[0; 32]);
            let mut b = Builder::new();
            let out: [OVar; 3] = std::array::from_fn(|k| b.witness_octet(native[8 * k..8 * k + 8].try_into().unwrap()));
            let before = b.rows_used();
            pow_value(&mut b, &params, out, &native);
            println!("{name}: proof of work = {} rows ({} lookups)", b.rows_used() - before, params.lookups);
        }
    }

    /// The step's size and proving time with this network's parameters --
    /// the per-block floor. `[NETWORK=dev] cargo test --release --
    /// --ignored --nocapture chain_step_costs`.
    #[test]
    #[ignore]
    fn chain_step_costs() {
        let tree = crate::prover::tree();
        let (_dir, chain, g, blocks, _target) = chain_of(2);
        let g_tip = tip(&chain, &g);
        let time = std::time::Instant::now;
        let start = time();
        let genesis = genesis_key(&g_tip, &tree).unwrap();
        let g_proof = prove_genesis(&genesis, &g_tip, &tree, [1; 32]).unwrap();
        println!("genesis key + proof: {:.2?}", start.elapsed());
        let keys_in = built_in(&genesis);
        let (h1, r1) = &blocks[0];
        let (t1, t2) = (tip(&chain, h1), tip(&chain, &blocks[1].0));
        crate::recursion::clear_profile();
        let rows = step_rows(&g_proof, r1, h1, &t1, &keys_in, &tree).unwrap();
        println!("chain step: {rows} rows of {} ({:.0}%)", tree.trace_len, 100.0 * rows as f64 / tree.trace_len as f64);
        crate::recursion::print_profile(rows, 2, tree.params.num_queries);
        let start = time();
        let step = step_key(&g_proof, r1, h1, &t1, &keys_in, &tree).unwrap();
        println!("step key: {:.2?}", start.elapsed());
        let keys = ChainKeys { genesis, step, built_in: keys_in };
        let p1 = prove_step(&keys, &g_proof, r1, h1, &t1, &tree, [2; 32]).unwrap();
        let (h2, r2) = &blocks[1];
        let start = time();
        let p2 = prove_step(&keys, &p1, r2, h2, &t2, &tree, [3; 32]).unwrap();
        println!("step proof: {:.2?}, {} KB", start.elapsed(), p2.proof.to_bytes().len() / 1024);
        let start = time();
        assert!(verify(&keys, &p2.tip, &p2.proof, &tree));
        println!("verify: {:.2?}", start.elapsed());
    }
}
