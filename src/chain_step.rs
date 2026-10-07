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
use crate::state_circuit::{bits_of, digest_bits, hash_bits, pack_octets};
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
    let nonce_bits: Vec<EVar> = header
        .nonce
        .iter()
        .flat_map(|&byte| {
            let cell = b.witness_ext(Ext::from_base(BabyBear::new(byte as u32)));
            bits_of(&mut b, cell, 8)
        })
        .collect();

    // The header's hash: Poseidon2 over its bytes, as `BlockHeader::hash`.
    let mut bits = digest_bits(&mut b, c_hash);
    bits.extend(digest_bits(&mut b, state_root));
    bits.extend(digest_bits(&mut b, body_hash));
    bits.extend(be64_bits(&std::array::from_fn(|j| count[j].1.clone())));
    bits.extend(be64_bits(&[h0_bits, h1_bits, zero_bits.clone(), zero_bits]));
    bits.extend(be64_bits(&std::array::from_fn(|j| timestamp[j].1.clone())));
    bits.extend(nonce_bits);
    let hash = hash_bits(&mut b, &bits);
    b.assert_eq_octet(hash, public[1]);

    // Proof of work: the hash, as a 256-bit number, at most the target.
    let hash_bits_msb = {
        let element_bits = digest_bits(&mut b, hash);
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
const GENESIS_CAP: &str = "7c0b3d4f5f584840b16e3e0c917c8d31e5716e3f707a4341420f00483c7a0c31142d3345aafd9c1fd0cad60a9b80f14aaad2475f8ca41e487e141a752bb9850e8d7c1b4846959833c7f656156b7f5542aa811933d6a1fe17291e4c3c3daef50f0aab5c6cf581a00ced59ac4bedb58a1452fb9b64a212c07793b2540886e0b204e44150347bb43a582ba1ea4637f9116ee0804e232e14ee573b2b391140eb8571add8b6275c40916e29e5a7578ed2982d99155924bbd62a4a136b0d60dde38174b6c8642e5cadfb60725a92276cc64064eb2fe72e76e00131f8f9060f8ee25a4765094c74d2dd91208ebd064a97185b310504707078e9656d5d225f1c0c4bd52868a13f73e92ac00ba9276b2e50c5e965e6fe31380965bf16249b005dec9c655a54cef82dcf53fc30c360cc73ac331b4faae13910f4beed521358586707080851b75d514b6861245b2125e40f5e3e7f08b5cd2413c50061314a0d1c3535ec253390d40b00b3dd462943dc5d22f172971d904ffd04a6c0e022a1cfd659a3cf9f3a38214134998a603e3251e64692a83618ee0d990613b1433e07ce540e083f2e58ccf40b6352536774f951036e49461f368548612bef9c1a57cdac2c4c5661365e385f985fa6647c4020eaa95b4e7c641bac297926bb218953aa2c183e6d304b2302a484772cb4e610fb02ff531bb2904aa685cb10d76fc93bf77a59179461073b17fab72e03212d06dee0b95a65cbd6068ac34b3f7187490ad7c1460eb84594447421fd2f7d83594307c6f809c9d2b05d08118417a9e2c81c9505f96bb2fba214b051ad0beb8c030b65eb23317931cd12daaa095b2b584e203f87ea120a817918a5eb475bebcf01690481fe70dde6696a1d17066a8175ca4150a1da513939514fbce42176c0087f4ac1d1934f53e37169e61b064509ec8e0b88d5af064232bc2764e37b367f19a10e01eda6490823c01ee14e891e95c14c676b88ff5793a04e74ccec9f42b631a13f3a1151420709e47333bbc94bec9b5a4dda49051a55c5a0129896f73632122d34eb606140b5005435c2f754610cb4e14cc1c90f74e9ceda2fc6395a53bafe446b152b711e1293cc516f8f7b242bd61d6a983a1e05e95d19400cbefc2453db291edc92ee08c3d2b44c8e72c2153d12c472bd3195735c2ef0366acc10190167e329d32bd13be44df0451fa0a90c9edfab6a1e06fe43899822250ca20d1f0417ee48c2d7fb4c66626e5e99c401705f060b4a754d14567d77384e9bfe081409fffe2e3c3e064c413ece1a115e2d0de6f8643f65e54961d5dd3d5e15b4453ebe9f6e40322b9966f5e3f32634b357009958450adf444c4ee4472861da7776708a96ac6ce46a9139ea6f7525e2389a03df9a33373f4e34688f69f95a2f841f128a50452b365fba4985eec75ecae0245f112eba47e12ef43742859a56";
const STEP_CAP: &str = "c2fdca322cc3af194059a7214e775324c6cb7e2b2bf6046f9362c70242e51d2ce1c5d31335ecb005ffa1c03eac5ef934bd0c3911556c8b4340b4546a9bef303c18a8aa77cfd4724f273d025478f65a1b4644e15f90226a30f3e7856cf422773cdab6640bcfe175262e794938c2623f4f015d2273aef4363b02745011a22904168618f2004e37e7745052be1479b0426a061dcf534d2fbe04b419ea1efb36ed0d74b809535315676e2e24371e1d0d0e5ae0b9460802b81a0293a28a5cccf418051e7c455171c35f53bff9a73c9beeba1efd384116c60b5a4d7a81586703545828142ea527dd11a87322753d50a2d36212ea95dc58ce9a17233ba4c331a56945064258a527e046150c5a281812db3b5d690136bb6e59835008c1c7376665085b1f5ae18126c731374e43cbdc188912742e190d5e4a45416736bc5bbb0c2039a22eab578504656284292495fb7171da3d042382c43aff666a0b333b1936eb6113139fd0b527f6cd31092fefd3226bc41949bc38d50633eec17322bd975621f03e74152c1c22f3bcdc4834866b1b205e1228db56fb37b63c65747e69a6024669d5005a7d282939ffec305d79113c2cc07742cd7eec0ab8c9e72107d6fc17a5731a297a86950e35be9b29a828c33099541f5d199d6c0234d0fe6ebbc8da36a1220041726b8c1112646f53a222c80ae5939374cbdab446f241572147118a3c0b7f99194cefb339de739970913b5d3f23afda771425db739de78667e7af3214974dac57b628e84117a77e4f9b6c0655cf8a8743d8085c3117c2a72ea316f06e4b0c5d5d742fad4a53e710116b48d42a00101475fe5aa308d281ff2a4fbb6e300bbc1b39b1bd8a3f056682314ea7d930a1d1ac3a743abe0bee569139ba5d8752a914ed20e70fac702a9ced4a1a23d52c94e23e6230ad0c23fb26a4170756246d47b558087f7e382cbd1d1903962c992c1a75bd0c6a5a3155c6ef4658dd786f07845bbe427450376d9b3a6c31eec31b260c6f156fc795746c94fd305652bc01641704b94e075f282ba72d950ee833db4b5115ff53c03ae9160be30d0fa6d0e13bb2b2d1676fd3406d813293465068711791f6b13e108f0b71c9da4a27e5b38807fd57cb07ffbd2e6c2fd339439d9345248ceb0d195471d031452c3211f978a42f91dbf76df043be05125a15647035696dfba65f498d419d353325bd6c141714672c48af14b1ec4f0914f31414f69c6c2c408fce4200dd6a4d2d2abb488513f8406ec8e819aa37545e37326375c63378042f94623eede5d64a26c97d3952734b68a2d7dd0462c2e90b81b8ab45e3060f2a6f838c3d5a948d3f5c36126c59d2c62b0cfb3d1cb09620774604745e1fa8c1528f09b0611f0af643d2b6b40aa253162b8d05ae61b3f7384099e459446fd2ae1107b65e5f72700c5eb08a003d7c4a622c3545b15c";
const DEV_GENESIS_CAP: &str = "c94d7c70375d825a5dad2e1caff598336f19211a76f56a4949de431b26330b439de115530d9e426b46e5c122a71d466a9321711eac60ed31504aa3392984bd4f1087421bedab5131614362352a160f689774614caca75f4007b46570a4a0d253ee2107376ee9a81d495a5058c9ca883ed745c73329676e528b3cef04e002292ef997b13761cf6e290fdcd16f460053757dc8d342041d08021dcc0c49d176702e3fbd4e3b2eb178075a24b135724c2b182a573d4166741f6853a9256538ea1a0cc03af21730a6ee755fa3ef1e661f3510007c5f63fb3b0f504c6b872e2691853ff593624af327b414ec5ae06d198604181a5abb30017bea00a176ad1f25c661572a1bd300b132e3245b034e3e5c7f1927b624553f76ab6a5748f3613423d09f23af0f48156f62072e0e249e1f50d25c3b11fd956e51315f4171f22f07bb77de396e50c03a12f211726c9e911a393d38030937b733a6bd9918b49e2808f06c257214b10d0f605eb7239b2d5421ebfa4d5b6e5d8f03b572750be28525578ebea3375b51eb763de3e276703b283f0596b8445c98521c6513be49f9de183c1c293a48e951d336b123553ce6974a772989bc23a6f61524c651ea2328d94f62c5bb890873c64856fb9e446b4ed3a460a01332045df13c2e4bde4a75b95d98599cbe051e0970ef6dcce4624f10e65b3925a3402012a8d818ba678c71ed489423dae4bf1e6a276740b31f1017e844ed2c635abb25e33dd025701d401973b6a217cfa3781f09e5ea1d8ed92274e839db0955a4ba17af6ca7065d1d3f7568f15f39618cdc6bcf92630f3dd94f0f8ebc62279d9cdd3794eedb62b6f8850677767063ab90d40fc9e64941568a1a049b58412dc516234122dcba6f0dcd96334159922af7558314fb18a1723c046633a4a14a5ded5a0118a2028d6399c09c046804da12cdae9c5a46704c1a56e8af5425ff2c29845c99296bb36a16da6a3b6b3257b873586a0c119babf149f04c5966d2d17d4464d8a856fbe01b2bee98f8763010a63b2c19e4281b6225332b27b6020387623d14344972fdee383ffc25c2203e18973222bdcb15124f2f5c6afff06bcb45e23cb402cc163ee893301557a84b57d50b26a7e64b052df2f316992f504e28ede943795c753ab885ab5b99f2b148199e6d6019a8ba296830392f9b9f842a027a832825165a60ff8c1f27ff16d14ed9c77308d0fc9f4e693e6f562c396c443adf135e8e592b5acf617323276a6234e3764d4b6078792e30dcd36604da171f8e6e4051c360cc69e304e0237d4fec6d8eb3d83ffc37ea44286c00417f204920028ad75db125ec4f04793365735df45b21d76b1c90ff871a83245611dd64d31dcafca75f20b8970a649f09639cd95c22a9f8af67580ff33840550c043707a01481b06e21fee9db3827e0b65029037a234786cb0ab0ff6c5b";
const DEV_STEP_CAP: &str = "1b791b77a3097a4023153e5976f8d865f69bf50956b7d73554af7d5d6f27fb18451858135ecbd606a2ef57011e9ed802f02a02083a65831661c03639d8e9136dff2e7918c931bb128e7c1a550a430554cc8ca871b80b6960d8d9023c3ab5315fbb324424e27efe44a76608467a84b62ad15ce602d3eca674a9911077ec105b2e5521f33b232b074a22c632712f340f26e50dad35af3ebe484019584cff260218cafc045cf1ff2210dfa82b1ee01354346340722d1542b608d1b26c42c4ce8174bfed365941651226103f8e506021bc140c004b09453df771d89fe521d0937500af74e4063d0b8c1355921c5b4f8e3f35d8f14e29789a4141ac1ce00d6f6cff5800492053b3a4ce41cefa20657739fc45b715c846c430e031ae0b621d201b83009cbcfe1aa8fa8611dbbf1750f7fe65418464ce1607b05e5bb309896f6542483e17a79f3bb90dcd58c48da81b4cd49a187a96e722e888fd5df5999908820c9f4f5ccb1571f978b94797888e3c6e59c735aa7cd070b2640331c0a60311af663736547c7b09a4956d6bbbb4ac1e8f882c61f3c5461462aae93778e20c705abf3e1993bafb15530e5358c53ce72ec54fe875643f255bbaade31d7aad0b34fbc5743a1641fd530d6f1642411b68576ac9c01645da42022b06361a3ca3882931567566b782e736bdbd3c1c1c6e800ba889014faf1aca07414c7f4ed5a56d249073942753d592640cf26f34d96480573293571091f7eb2507d22177a954fa54ff9e134ebf2d031fbeac0d03e287e265491c2f2535c5fa4a39662262090ceb668b6660702873472f8453462ead1e2c531416532ba647dc18189bdb28aa56a7038a4622193fdbaf1cbc732220e52a122d96462802838a72373a1d6d080e86b06604c8b71f0db6ab4dfd81442b6b40fa5e05dad763d5f22e33796405628c88fa5fedfcdf461856186b50bb1932ca2036387987c54d6b4eb4366c328473446abc49cbc8854b3570d01ae945445b9390ca247727a5263a89343212df037756e23125571ce9352f175057cccadc06c218f42ca7ad7a4c3bd9061decfa1c6b93cadd1bdfd18f628ea2bf35e2ad71226f89cb6345c160112209d550056bf64bbe2ffe31d33f98206a6f860a228975384b8dba63304a9647273b254de137d2551abb685c32d20f68f393482c1f98504d776dd13b5acd7e220f3281441e34c1318f170f2714e35461ec0a852c211126341d60131e1c277d6ed6439e29f8cb9171850ed72a318fde4e40f7fd5a1460c0010291b323a2db621f6d7c5e587f38cf232169b20ef99b613a20f020226fcfdb2f34bb9307d102442718ccef6c31d2e368ef213719bf394564c8c768315fa235400eccc14228862a20ea1e766479a7d01008d94e70d7a07775c94ee65209bc1e5a5c16e745dcf6bd69183ac70940ada07241729b054ccd5c16";

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
            assert!(mine_block(&mut block, &target, u64::MAX));
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
        assert!(crate::block::mine_header(&mut early, &p1.tip.target, u64::MAX));
        let early_tip = Tip { hash: early.hash(), timestamp: early.timestamp, ..t2 };
        assert!(refused(attempt(&p1, r2, &early, &early_tip)));
        // The right block, but claiming more work than it did.
        let mut greedy = t2;
        greedy.work[31] ^= 1;
        assert!(refused(attempt(&p1, r2, h2, &greedy)));
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
