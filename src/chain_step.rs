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
//! checks it claims exactly the reward and moves the state from the
//! parent's (as the child attests) to the header's `state_root` and
//! `output_count`. So a chain proof vouches for every block's validity,
//! not just its header: transactions authorized and balanced, every
//! spent output real and unspent, every created one appended.
//!
//! And it applies the chain's numeric rules (`chain_rules`): the target
//! the next block must meet follows the **retarget** rule, and the
//! **cumulative work** grows by this block's.
//!
//! What a chain proof attests (`Tip`, its public inputs):
//!
//! ```text
//! [ step vk | header hash | height, timestamp (4 × 16-bit), output count
//!   | next target (16 × 16-bit) | state root | window start (4 × 16-bit)
//!   | cumulative work (16 × 16-bit) ]
//! ```

#![allow(dead_code)]

use crate::aggregate::{Error, Key, Node, TreeParams, assert_select, fit, vk_digest};
use crate::block::BlockHeader;
use crate::circuit::{Builder, Circuit, CircuitAir, EVar, OVar, Octet};
use crate::ext::Ext;
use crate::poseidon2::{BabyBear, DOMAIN_VK, digest_from_bytes};
use crate::recursion;
use crate::transcript::octet_of;
use crate::state_circuit::{bits_of, digest_bits, from_bits, hash_bits, pack_octets};
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
    /// The retarget window's start (`chain::next_retarget`) after it.
    pub window_start: u64,
    /// The chain's cumulative work up to and including it (big-endian).
    pub work: [u8; 32],
}

/// A number's four 16-bit limbs, least significant first.
fn limbs16(v: u64) -> [u32; 4] {
    std::array::from_fn(|j| ((v >> (16 * j)) & 0xffff) as u32)
}

impl Tip {
    /// The tip `header` makes, given what the chain records after it --
    /// `(target, window start, cumulative work)` (`Chain::proof_state`).
    pub fn new(header: &BlockHeader, (target, window_start, work): ([u8; 32], u64, [u8; 32])) -> Tip {
        Tip {
            hash: header.hash(),
            height: header.height,
            timestamp: header.timestamp,
            target,
            state_root: header.state_root,
            output_count: header.output_count,
            window_start,
            work,
        }
    }

    /// `[height, timestamp limbs, output count, 0, 0]`.
    fn info(&self) -> Octet {
        let mut o = [BabyBear::ZERO; 8];
        o[0] = BabyBear::new(self.height as u32);
        for (j, l) in limbs16(self.timestamp).into_iter().enumerate() {
            o[1 + j] = BabyBear::new(l);
        }
        o[5] = BabyBear::new(self.output_count as u32);
        o
    }

    /// The public inputs of a proof attesting this tip, by a circuit
    /// whose key is `vk`.
    fn public(&self, vk: Octet) -> [Octet; 9] {
        let [t0, t1] = octets256(&self.target);
        let [w0, w1] = octets256(&self.work);
        let mut ws = [BabyBear::ZERO; 8];
        for (j, l) in limbs16(self.window_start).into_iter().enumerate() {
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

/// `x`'s 31 bits, lowest first -- its *canonical* value, below p: with
/// only `bits_of`, a value below 2^27 - 1 could also be written as itself
/// plus p, and pick another dataset index than validators do.
fn canonical_bits(b: &mut Builder, x: EVar) -> Vec<EVar> {
    let bits = bits_of(b, x, 31);
    // p - 1 = 2^31 - 2^27: the top four bits all set leave only zeros below.
    let mut top = bits[27];
    for &bit in &bits[28..31] {
        top = b.mul(top, bit);
    }
    let low = from_bits(b, &bits[..27]);
    let both = b.mul(top, low);
    b.assert_zero(both);
    bits
}

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

    // The block's proof: by the tree's wrap or aggregation circuit,
    // claiming exactly the reward, from the parent's state to this one's.
    let (count_in, count_out) = block_proof(&mut b, block, keys, tree, c_state, public[5])?;
    let child_count = lane_of(&mut b, c_info, 5);
    b.assert_eq(count_in, child_count);

    // The header's fields.
    let state_root = public[5];
    let body_hash = b.witness_octet(digest_from_bytes(&header.body_hash));
    if header.output_count >= 1 << 31 {
        return Err(Error::InvalidProof);
    }
    let count: Vec<(EVar, Vec<EVar>)> = limbs16(header.output_count).iter().map(|&l| witness_limb(&mut b, l)).collect();
    let z = BabyBear::ZERO;
    let composed_count = b.arith(z, Some(count[1].0), None, BabyBear::new(1 << 16), z, Some(count[0].0), BabyBear::ONE, [z; 4]);
    b.assert_eq(composed_count, count_out);
    b.assert_zero(count[2].0);
    b.assert_zero(count[3].0);
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
    let window_start: [EVar; 4] = std::array::from_fn(|j| lane_of(&mut b, c_ws, j));
    let (next_target, next_window) = crate::chain_rules::retarget(&mut b, &keys.difficulty, height, &ts, &target, &window_start);
    let child_work = octets_to_bytes(&mut b, [c_w0, c_w1]);
    let work = crate::chain_rules::add_work(&mut b, &target, &child_work);

    // What this proof attests.
    let info = pack_octets(&mut b, &[height, ts[0], ts[1], ts[2], ts[3], count_out])[0];
    b.assert_eq_octet(info, public[2]);
    let [t0, t1] = bytes_to_octets(&mut b, &next_target);
    b.assert_eq_octet(t0, public[3]);
    b.assert_eq_octet(t1, public[4]);
    let ws = pack_octets(&mut b, &next_window)[0];
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
/// `vk` input being that key), it balances against exactly the reward,
/// and it moves the state from `state_in` (the parent's root) to
/// `state_out` (this header's). Returns its `(count_in, count_out)`.
fn block_proof(b: &mut Builder, block: &Node, keys: &StepKeys, tree: &TreeParams, state_in: OVar, state_out: OVar) -> Result<(EVar, EVar), Error> {
    use crate::aggregate::{add_amount, limbs_of};
    let statement = recursion::verify(b, &block.air, &block.proof, &tree.params).ok_or(Error::InvalidProof)?;
    if statement.tuples.len() != 6 {
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

    // Exactly the reward: a == b + REWARD (the limbs are range-checked by
    // the wrap and aggregation circuits).
    let limbs = limbs_of(b, amounts);
    let reward: Vec<EVar> = crate::output::amount_limbs(crate::prover::REWARD).iter().map(|&l| b.const_base(l)).collect();
    let expected = add_amount(b, &limbs[4..], &reward);
    for j in 0..4 {
        b.assert_eq(limbs[j], expected[j]);
    }

    // The state.
    b.assert_eq_octet(root_in, state_in);
    b.assert_eq_octet(root_out, state_out);
    Ok((lane_of(b, counts, 0), lane_of(b, counts, 1)))
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
const GENESIS_CAP: &str = "eb6dcf0d9f6605156f869366cb2af264e273362186672b59bba26412dac0bc42e11a2607f18fed1da766e53343975550a543d93ea660d568b20d91447fce321f676bb9399e095242dc89581d0b5488125619f5026eb17a4b68d2f135794b3f22b5622157a2e0e61f1caaff1deda514479d9b8b091cea9e633ec26e3de3814a3b90054751f823a61813344d731bf3970a24de223734fc353a8d1f28325172ed1b5d12d90fc315ae26026d1e68d9f875229b1fa13a68908a41d8d0e62759b05659e1f3ca05753e3d45b7b63c0d5299ba333843e115a8d970137b859972bb02404788844b0402d99c5fd87fa54efe59496cbc03fc5f9176656c919d3e0838b70756d325703ea61ddd39650b7c25c1b06117478c702b5634c304c65c362b7164942fad83370b4e3ed92eceb0951b3d0cb344e1f31d5851c2dd6a6fcac73955248754e5f02f6125834619547a4f0f603ffb053b4f66419c385d485bca7b4d44455a60929dbd244ecef92191544b0cb03fa80d69230d5619419f33ee82f303ebae20532b0b0245a8dac12cc49f88607d1e21241a20f72b750e58595a2a3d1a473bbf10197ef32224d25a16101843174019c846fd24573ed6745867a1f238589501ea05d69cb81d4405465ffd81fb0a7ebaca186a20464a70996f378c824a33edacfa4c58fc104ef3c8803ea7bf203cff176b758aefea2f9343dc02872c5439ea9bbb363684136258e08b46cbc3f46dbeb21548ab807371f3eb26559d41f32dff870f32272a6b333dec06347c1fa65458505e023b52b725fef1c86116534a56967dd140aae6742b111c8235f1dc5d73ead4514c5b17c11a8ca2e740dee1104449b17e318b5ee20c536a2c717cb9c64554272c3b88bcce44386fb6361d49920ff8df6324ada96639f88a162749f4962468cf8a476864a0195fea030784bd0e092794046f5c0c66185c0070453703b218e7148e057f3bc835f924461f88f1d12e470af4395f823f35487e2969e1ef6e092c49277120eecc079ce5ad02ae27db2e5cff5f103b980703495c464b01b99d6f6480e61ccf0ff65cb20cf8650a46cc1ef4273b1ea8f85b47a4511110cf8e7d0a5b775f2363c6fb1ccc6d096b2eac0b24b75cdd3ba965c33feb72d5585de2ff59b1e4a1699a003e1eea554f55af20d101a2f45f656e54a87482379648aef92614784b6349405f3207e5461b00dfdaa473698fad6ba84cbf43f79e01287f5bfe2cd01a796a0d0a9d0d27763b5bdb02453969422425f6e52c54c748c44bb8b0cb4f335b5e6f5596700696223d6749138b4de1fc152c6067202b1716d430e4cbcc183aa2b6542c165a16e3b11e73b78fd40fc0c14c0b4b35972f1b6b90137fcab81ab2397b0406e1d020b714991a030961741b483577c15e4f33ba4ac807ec4e22327d059709c3b1706ecb513b49c0ed557779a5ae4f";
const STEP_CAP: &str = "97fa454218443e3273afd8454801bd396db5d100e2959a14e1c1cd5267374a643838190bee575c524f68e50c18c9054c951bcf052ee1696eda53a56f52e8b55cd145734f8ce63d40c585df0a9fea6b336ea01b58fa2cf0229e02675cf427071284329c1d92be7637e635f610113a90771194080e58d7c622c876d94e9c620840beb1ed7345d2d7460ab1f52e63927e37143211726e390404a619fb1e7b897926b44cdc650d93671321f1af020acd2c1f202cdb5326e97e1b4e35b475f6181d37c5e7c4713c10775699aa41378cf7f746ffcbe811de2a45151224aa6b3a2f9b1248c9f6469b3dd6601366952de7f8d21290533b71c8c62957d218605adaaf9556122ad321908b29600963a46af6c8885ec470c6147b57e768efbe2821db4ba43fea10094e8102eb344b137b65316e16520b42621a2db3f33d1b4dd10207df5313e6bbd977b04259204ec6ef6465d4de2587a65858492d0146ea113e195dcc173f32ea7735323b6930733037011c8a01482b35961041d806505317ed05f28c5c2db1e188053ebfec3cda912706442b3d662ebdde0ce7d2a05f7ae47a358cad70184869f14f51bc226180447f0f99dec30cd349b55881bf2a538585a8751251fb4add57d8269935f4729662601aac2a235c965fc51c43246767b333245be39bee68e49c4450d178ee6bc9d83729020e6e5f2c54c55d050f4f258aa81f19d0cba41534ace9073d25266a071dff2405a8bf22d460652fe1e45e0e22c3cd2a03888006a73f865033c80e6473931b398e613a12b445691638ff241f6885fb36ce604263552c6b3f9be955045854422de192163f137e153c65902a26a05511246517455036c87d1e8f03b22d5e66093cfa7fd34f8f9ea42aae55eb23ad985b5719477c098673d751835461517e84d60bee05da5ad574be24c8802142f24d575f3718da5dcb75767565e9b01bc5ef0c3db407e3388ad5840f629d0b4c6c444662a658da58834bf7181f75d03053ac1a65c3995753d9583e18780e1841d8a6b576127b824b642bc66bf89c0707526d5b37fb7d71172f43163da0b75d66d261c7333e2b695cbf80fc0b3d4e507097952374e92de27503e47d63f46f6e18eb6a9b3568a4ec73ccbb1766b93b20381ea9714c1d59886ae7aa1d5e52b50f27a90bfc680a06182558f81d49f877db3b0e85b2174b46a012bf98b41f8919ab1684d47a0940cdae7188211417dc03c003e99cd33ca28d9c402e807c040efd36612edb3b0faa73272a446bca557b46b46f55161814eaf26c2b192da367064c04112afd1c656bb40e1f61a05571e2c1931062d5b421f5112e1797588544c7ff340b94cd080320a2f549dc37c003167fa413e821923152b6156804ede80a41821e6799701436107d495bde1fcf28297af6446ca6b76c74f28a2644dcf364f2a7fb568f1e462a6684fc46";
const DEV_GENESIS_CAP: &str = "3ca73f38d814ed4d09f6da097b7e6c749c8d8a31e77ebf16273eeb5ab05bd7517a2260334890284dc8629f6a0cc57f487f680b599ce83e34572a6d3fcb4e8f70551d550485b5611f80ffe62604e8710a265a7410f571cf343642ad6c604a5073a5c4ad21196fe162bb4e0b04835db6170fd09955dbc72f4347cf8a70cdc7310254667b38e70c4c69dc577a5245e98071e3dbf2394eaa8e3748465d0493b52b77a69076086d840072fae7434cc3b4d0220743df0313d565481c8dfc37cf188e64012dc764b1ff3e366e45912a71b4be540419e7427d883520492c476d01ab7a430d624b612fecca2d84fe834053283e2a7ac51b45cc081162eed7a72f9239e13fc4501b0b839b432e001d092095f267659c8c204c16c7002036e2e26ea3ac5b383587ff331807e73b4b6f9164f04e831a48c3210ae629314ac8b8a23e2513280ca54ad514095842615390000b925433754f61862fded7d1744c4a1d434421b1074ff1bb1d02fbe133d288dc0a3c4383551032b06b1389f90dca04440b6137151a170f8621a113b258ca2973416f63160b19162e1438f6dc3fa80e682d835db1735411077149b1c461bce8d73ea36d575fe75e8f38f56dc661d4683e67aa61a84cd9d4591a777c0e1cc75c9b4b31e08c2de0ef8712c81d5c745fc51c720004ef0376e081206ff59603391cf85cbc63d05dca957116207bdf34eb1eb4289070650d229dc15e98313e45d75e714dfa14c21c4f7022435fd00e3d4be6ea5f583c813670dad21d4413025f043f9e541b0a743549b8630cb9492c04de37c03a060d2648ba84d0013d5bb26801828f0408127f67fae2b1606b7de639eef8316bca3da641702017143897f11155555f3b016d892027988b13832eef3565983e6f01e4b638abae2c13283c0700a253707114c85d0c103d9530a3d9d364dd267a7605deda624988143212350420bdbb1c0fe59f4a6f0537933656f7f209d0fbbf18cbce9d773718792a7252a15bc50b4d0fb825d35fd52bca2f3036642c8936dd568b61f65f8c839132bb40ff255edd5c18ae1b726fb767d847fcd63d414996f416d0e87155f67ef705e994220266a8a0085960882578d2ab6f8c7119369570150e569fca50486dc75f06e6c73ccff4113c44cf0d017805a64c96afef5f3ef84136bfbd52465dee93214a31556296cc096e906d852c5a36bf3af8385b069796c93fd07704483be33d73618b82551c1e9b25d9cc066d0d826917395649686f22962882723a72e5d49665e921c9760ecae4773778666115099d33895dd54ef7792d5cd5f52a6b24aa811d192bdd4d0e681b7784700568698a774451834a3d890e9c400728fe16aa3f2416d4d1ee76acbd2c46d543c040d98bf577f7e72240825ff934415cc77719e6e7543634c00ae7ecfb0d39aae53b2019045ff23d28587daf2e19cabf7f50";
const DEV_STEP_CAP: &str = "f394953130d0a61e5818bf58ba6a7d3d4eb569247e93aa754ccc362b175da06445ebbb65970319219647736674eaa8522183cf5958586558d1a21724f500042a57bcde43520f0e3d82aa5c4572e8d10152c32b35e932be008c7ec06463ad0924ad1401183e3a711731f2d271acb6dc5a1f12f01819ada05275f72a0a54354c1fa77cd8423826b6372c081a0867e4c175f34bde53fe9c9167915e091ad11c6f1288859b6d361d034208a4701007333b72d466b3031566ef744cbc77300c3a9f56b7b4ac3a2e0cb12ad1811b13f3e5e5236a25f308d8b2fd31a3c64208473cbc68ee9d722d3751910c247fe36bbbd69c595d79407693fb234723413c1286eb1d2b9cafff630554f2775e07ed43c4608457cb84820b82203c3c4594e219fe40050c32de256b7b27e9577ce4b52c0a720722f3d8ba1b8fd6a60b67d4203c90814f01a97cb71fd9bd7413ca02ec47ff13cd6bae9ac41ec492e5314620fa1d4d20ab2855873342ca5fc71aae04c174796d8211dadcbc660b834166061630500bd2f46a9f87276f97b0a45c4e725170e9e00e2db4eb78666b482a2d302726403c369000e8ddb90ea4187f4f4d511a3a2eced81da153d107310ad31d2dd632726f79f9023b3d7f3ceb917f2709e255447f7dd0152d2c280635b92e0396846c2c3dcfae56eddb3044bb8be5178bbec52fbeaf8c362dc93b7760444b5ab0263421f7351f4cf6155c0d23a1b272cc3dcf33370a4b3fcd9dab6460b9e23bd0c27b538fab9f26697117760f4f014a12da27446ab631459811cc602441ce31665b5857bbec1142234bf15fd6204f4646147b03db3d4b1ce7f4b64e2985232768280c53936b913b9a0804598d0e3644cc329a3f3239f1091ead423a15645d6ab74d9029d7fe2471ce31ae39796d4135becd852540a34b69aaaf662642b39305a39fa65dab3a066368f87e630bfde83913a0ca3cb9d7b81b2f8975133c9a9644dcf5b2594fb69409b50bfa656c6da41dc8af332aa8ea6104fe9b6a13e6bf4569c93f6a4a2773b70bdb31e1521c7a8528a7ed630c524ba51f00dba76cf2f7f474e068824eedc7b63d5096b475adddd3563b83d05f52a78b511ccd24028cafc7382eadb54302f3de751483d41fbc016468862a9d7698a9d429e0c8bf738641b601ab81066d7569d448cf1ab24700ca9169ff7dff4b535ba1642ea9023f33ca6f2685f9f44e7304d2668ea9d112bc6c354d666e8f4bb18fb559a9442b1c9d7c965c1aac3752e64e48022ccdef403f534766de387b01326c443d04bcab0805e7607578fb530b2377764b43efb44692f95f34eb8ebb1b4f0414419fc07213b3475e151a71d81e370f9356cc55b63adf40d85d73f8031ab0758a0f6e92fe2030d30d5c05388c7557a9635f20bae3722adee0008aeb276b64f9384d4f29d173f695893f8014784eb4b1250b";

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
        let root = crate::prover::block_root(&block.proof, &block.inputs, &block.outputs, &block.nonces, &block.state).ok_or(Error::InvalidProof)?;
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
            |t| t.window_start += 1,
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
        stark::check(&air, &circuit.witness, &challenges).unwrap();
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
