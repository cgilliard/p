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
    // The version: two 16-bit limbs, at least `BLOCK_VERSION` (1): not
    // zero, their sum having an inverse.
    if header.version < crate::block::BLOCK_VERSION {
        return Err(Error::InvalidProof);
    }
    let version: Vec<(EVar, Vec<EVar>)> = [header.version & 0xffff, header.version >> 16].iter().map(|&l| witness_limb(&mut b, l)).collect();
    {
        let sum = b.add(version[0].0, version[1].0);
        let inverse = BabyBear::new((header.version & 0xffff) + (header.version >> 16)).inverse();
        let inverse = b.witness_ext(Ext::from_base(inverse));
        let product = b.mul(sum, inverse);
        let one = b.one();
        b.assert_eq(product, one);
    }
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
    // (The version first: big-endian, each byte's bits lowest first.)
    let mut bits: Vec<EVar> = version.iter().rev().flat_map(|(_, limb)| limb[8..16].iter().chain(&limb[..8]).copied().collect::<Vec<_>>()).collect();
    bits.extend(digest_bits(&mut b, c_hash));
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
const GENESIS_CAP: &str = "2a24102dbc45005078c86317e572e7502af7d528d352d31eb7ff6c4c832177186229db4c78fb7d5efd0fdf39301f15238f166307694f4e27220404489adf3b4561daf2690b2ad35662a13212827b2a1f1f3af32bf49cf038746bc14b4dd9e0713784e747ad5f8f60050efd474ea4ad3c88215255a528832a9605071c713f3d3099954025fb3bb06cc37b2106420a125f45a13915d45ef16142d3a02addca4445e215f93dd70c94020fe7715cf2fb737209471f3b528bb7495ef1ef0dd15d0e39d4bb472a0563e21f09d2a96fef12d950f38e7e18706e7f1a8c8653200f203f3fa7fc62047fe4e50be513022bf1816a1175d44a6d61c7e31a08cf325ffb06191cbf17216fb0cbff14bf4d951acba0ba08aebf2758f058606a282340601ad865393e44ea54b3353134bde7a740a4eb1e606fc5e13788e8e63f1193687673f1ca2f6a8bd65ae797d81b69155629ab429149f6f5db4af28a9f1dabcfd419751f2c263392d44496b906469456a938facc2f1fe2e8fe4b8c45b23931523d4056041b6d935fc263110600722d979f58dcec8761e354ec3405834d0a45f4906e30176669d43c6f4da52e4a3ea9b8805870ff862ef64f07375af82b3bff76d4700d9b0522ae022c4e1e47901883ac001597a3320a9ffd730fdbd66f6259fb033387188f5fc363245a729aa040ae006f1919e67e761de02111af3a8652f06f4d0172f1171f5497bc6813cdb729f093f15452ed9b4985dfd644269ec116409c605de4ba4a70fb578b7341ed443800b06974c32287774d9c9f53f8b2f33c3ddf2b3df7dabb5ae410285174c5521c6e322e544b651b2c2ee3713204387f1b1b88d808fb361c239fa4b369bc9555751c9eeb1ba3ba3202830f975027bc8f1db382bc0fc2433f77125b0a57365ba85f9fb1c52c0b8d4f44d97fae663fccbe1e13cb571d019ea4671b039d220f23380bafb33520bddec200e68d41740b56412426b2b05e0cf01c620d1e514d95f6394dc0a73661290d1b7249078f73bdea5925405ce7277fbbe71ab0ddae4b87e05d33107d33251dc9a74a1aed9016d3873327b8fa7d70d75882737d4a0a3bca3267648c1d7714cfa3571e624aaa62b59e863625652229a26bf003d0a3f9719abd3523b91b4801595c1068d19ba049cdb65f17e1884f3d7da5002578e1620678374c6de460966d5f503d652af3824a4e49dc0661a4930555aad8236eeca735d337a5404ea02e602421b9518d19705db818ed4a8b8e2d11f67f0a5feccef2208611460d92096f4af2b89d728488b226a52f9a3274afc138a271215c0f69f944b23ae7461b99b060bd56240843a8641d0153a628a284d60de2bdf522136a41151ed1623df1b98a6d17c14b5b7158a7779a2b2f1f65594712e3ab4300bdb65b2c627fad331005ab115b6bc3169719f2455ac0232d6567cf740013b915";
const STEP_CAP: &str = "f8a00674f130f034a1b4605290986e5d2f5f1b0f1f374b2df93be95c6dba573caedfa6601844d712d933e322c7d3a16bbf415f4075f60e1448bae056e93be94321418177fd787c694a75a81d66139f4af554fc54691810191ef4594b99a34a234be90c20c07baf71b85e7d3545124d341de435447a42b66900ce2d447f610c386cff8828cb0f052542c41c01c2c92903d71efe77d4d5a90495d3d953d35bf861e212152f79128c6374612a0ae17f3c71ba85bd4ea01a9c540d28b51c1b2f076da786fd41135050022861195a3e15be2d840f0c6f0e7f062eaa6a912f899aa01651e9a11527d0c91cf831bc1a286c0a1d6903c8130cc0b564b07d680d950a9933eae2f700f01ea249d4b06c776d81ac32237f7751fb21a244751cf748fc46c5641c050241da380222a13c2975ebfd0f1525a8b87226e85643b4043d2ed3793875356058345712852d09a42b28782a4121a05b9f3e5bd0174dbe3fc738e5fa13261fe7514191f95e097a840114ca067064a9f8dc1e452a040a2c6cc62c052b516f15eb38278de82813aae5ed6fff5fe00e46cf28753c9a0571c19749730c1e904f8cdced0104fed047f8d7555997378e4a64345c2bf4bcce1b394aeb42d54d663e847b9e25d51777442ce1146eb2649e273b82a1778c4efe3423bccc4ac51678117e20fc201c9f927715f808577ff4cc2a41f0244852415f64980bd631f892a967ce21725dc9f7085df611010b75c2c7054fd5c90f9cadae1e0ab440617526b7466d57ae64ac3c9a1000b4427527d6774ba4cc361e5856be5577f8db72632eef429398031dfb1e335fc266735d8e4005376551323328042f2a1adb50549109ac4f7bade8251ea82c6c810bba6e398bc30c81e08713cbd3b9394f92a6648679ee5156385d3593420c079530535cf87cc14a15ccb525f68d271bbcedc559f805031180b58708d8b98f0410f77d01a1c2d004872d925740e46021b926ac3624c0302d551f9c5b7804d05b0e900e43514d06638ff8c2406432f924d676642c3a5acb67a0247050c4cb513244cbd82ab99532347cef6735c1b57b054b14b44b53b56a598422f33b6f0e5d2943bfc9242a704e44d9a78271f928965298da5a182fa6f2440049b911dce180132ce1ca56f3670a321055f347b53f4f58812ea269aec1cb63968a545c8cf2bf3a9b355c2b090ac64316afc361d1f6bd34db51dd4cbd90644ae39df02125fc811a8362384952f94113a32ef4330d3e4f373117184d630a453833d6f56d6b1d494a1d466b72f2c6186c54ed976bc5b5cf75b06ccd315a82e7478be8e4733de88465c2b17a642bbe382d54acf00463a4f52824f1a27396390077ef834367d980c214ab99a44b1f74b308e0dedd4ef0e3b02e6ad06a1e9b006c259c55b1093950bc66d84cdb4a2e6c321e9bd36f424a7138612b2ab04b9875622f";
const DEV_GENESIS_CAP: &str = "67b7ac74ba34c258fb95ab0cbad7c8631ac5036274a1d064edc0415abcd39d51f9a4894851d3107027f469639a5a00023d4c2913f3aaa166ba40543e5f0232519dd70b62cf30287201de761de9957d44846d50237205b10318229375c5cafe665c8d2403e66caf54e72df3705eaacf3a5c0b155cdd77d85e0d0372513523e349e8ac470a9f71032db0022824bbf41f3bf376c158ca7b4b37e49abf0c7be5e74ff97a96452b34422ad8efa161f92b991abd95d16e54cec16eb5a9bb0799c4dc6fa345ef5dec7b1974290747285285b73e0ae75f1e39ea3241dfc22063251f8d16c0fdd7674c99682e67529f51e4195414ebfad713c2714b25d5a562290e857b04337c052b8366136abb7593475a2d5a1e262e691ac7bc224312b05c5cc84ad92d399450434b98796d3a77fb74b287a12c494e0357b12664053cc0601cc2e5d604abfc203ab28e3b3e72dd2b57ad45a8374ca671011f535c3b69dc1a0735366d1ccc9dde1a63519d5c557ee8007b5ba233cd6565141f060540f1407c65bf2fd55757c7634741aabe0311bb2e2f5174d8295a00f63a49211130b81b831a4693093c338a763587c56a106c101514e61d1f3a63d1513cc83aa2023471ce5b0861a55a894400725286825117e59f09ca61c30b92119b03b92742662f328747e03c6b07def13e57e557796d8b51940229fb563cea5e206823ce31005c141a39ab9c8b55f8434e345626d5410d9643774b7c901ac9fda243f676d62e6a898807f49c3c6416166a2c32a5106a1277861414624d498ff919011677ad65e858b619bafc1f3ed00d9a7401e28e26a1bc604273326253a2697f77a4d7d8184713c722c53b060e4b750f5bb2ea4d509d83fe3d8e5b0840a62c1d68ac050742a0d73903fd4f243d16ad5c2f23e9f339cd27dd03aa11133d6a404e084b247b5526d01725f3a1fb1ce12dc73fce7d716f53396512bdef0d450ae09f4a4199ba1253ad3c159c368b5b11d9a27146b0fb2af6a0302658be060686990f1bb188b234f8a2c51df8b2d45c682cf14782dde340493975257925870a211a5a68781b290dddbf3a3ee526a6085368013f8adc572b53318a41e9c61260cc272232519d6e32e48b623b587e080822989f0ba0e67b5e7701be5278bf802499c1171f0bdadb5ba6801672079d8008c03bef76f44b354d99110151924fb775ba967c393728163076845f475a349954b5fb0250d112cc49424d0e32a1e98c0ad000ce4e77153318c2081958a0b9404d4d60a45d1b49360e9d302f582a409d40129a174c21045425bcb04676e0acb76163483c47d7c2591248aae927f75fe3673f5ace6d8d66e041c8b2104623efe7528d084133fa29b129ac2a2601ec03f320714c241b28e737401b6532102a9a1c1f3ed8340a089a2b1da904af3b257031075ba90137d408ad0780c0b968f813fd17";
const DEV_STEP_CAP: &str = "d7aa522cda477f37242d8339a6154d3bf87a174b95bd165a8f4d695aefae1a41dc2c7c12853a1c4431893b227fae134e986f94178f2bd7157576f11998c452748aace80fbc3f1760a90f1b093414875dfeeec344aefd5a0c50b771111632120d9b4cc4661bd33f5e7d692e536fae7a4f9213977660d603505ca9ed44d8599e3c21380c418157e43a9e2aae5bf297e552beb9da0fdc76336f5173c14ca6d1f16f433f085cc7c3dc59226bde4c34cac33908c20a24907409281234a525a40c092bb1542371385b8c719d9c29531d45e70671d0f3499886bd62b40e4a3d905a875173a33174fa95db779b23072005bdac142a7b5b5ff2e386045e55766be9a9d63ded2e3b6d1241f61422c92169f6c1a7561c828543256f9a0752e34c19ea96ee10110356599c345111dd8c592524ba3247bdc2e7509e6ddf405292dc317a7b1f52056dc03ed06f371efc7718602f63b658795ddf498d1f80185590a22a488d0f422e2a04480a8788006fbded452cb8234ebc62f81f32a9ed3932dea901e382a011413d28054e9fcf630f43ad615e97fb76eb12e10bbebaee0ec3bb2d69181f484b44955260e33fbe022edc7800329e551121f72e279801a6427990f4437a3f25602682be0ef2e841339aed1e6c66729e66888a41190d229f107f36a3693d6d555e3c63e645e313591c7825111ba2609e3b9830f3744e11440cd795797141f05e4f7704f76b481b1e2764aca0737b7d454839659b50d72f1418e0ee93145b988542cec2a42e7e32d510e1c7606b2209681e4f512853b4d6aa57258d6a4b3535f56ee079bc128e99b971e8d1f6242f410e1fc1d9b11069d57945a248432b7f8f71202d12593022da24490f4204463757290f2db66e242821655a8e2a8b4173a1366d31ed30305c5cca1d8ae34d0d8d3c4257748da5022cf11131bb09646c42e4ef437168f84e4c6e195e9002cf1e2b17974c8694146ca8f34154159a753c0b0b1a70d796fe4e77fba611edcf8e2523be4d0aaa6b450dc6acc90dd0ad2502de5a1c16b267cb6aceef2b4f8a52d408699e725e3e70802642132561de44762bea4b7b56e4456a225cdd2864cd7e88667d27a9118779cf369c729e43e2c86a666fbc654252905154504288658a83cb0fad44014da35a152027eb95354fda6433cb18336cb95a0662fcb789430ffa4305c6077568d75f3f1ba5653d52acfd7c36a81ed91726854f5a3f76f25472ff1b3b0c10793a3ff6ee2fc217536dc742a749ab732910c10d7738f2905b5453714b69bdc57d62df7ac960fecf8574d0a1820466f299688623bd33238db8496348602af267df3adda19361aed5214286c43070f4aeca6d47c5411a43ab6e4aa8c6bf47ff3d780d860fc326ce657e121a3bf8312dc3cb428ef13c3ae32d15342761406c586da7008482a129b5e67c4d1dce1f3510885c32";

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
