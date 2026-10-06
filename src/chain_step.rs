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
const GENESIS_CAP: &str = "a1e6b6687f261f5df77fdf232a98973edaa8fd28ce0ecf6151adfe0dbee35250579cec1ba83f1e61e698ed6fd7177348e37ab7520763dc6bbeab5a42ed622700988ee113da4e3559b01d1c5a72e59d1b18006938c572b56afc475468dae1eb1a2305d03fbb5e89332caad670402647103b39c256ada2874df82ec06cbe6ddc114f96822bdb1c4012dc1d29552671cf4ae74c5769da5a155fbcf34c3d48b7901934f730375767a140a5ba553a3b275f45679a1713f8d52c2a9efc49276cd6ce03abf8f93f7d7be628d6f73a558699df2bad78ef121527fb6761c3ae529241211e4c11bc03c1eaed286da7be54cc02c4706439230df2778645f9666c4a21e3613338b308385c0ad24c8c01df3750988c5f40bdcd42f2e1ed18164807270445116ea8c393173bdb6a0e3175331c1bc8425b7ce7f714dd6745641cbd6647d6f7e43179a73f4777ceb94d0e6a9f6f93a6693320e03a46f576b16efe174816bd129735c35284681a24671ee4bf626353474d5249e4407246f8274cdf512b500280591fc981a32e904243221a2bd62241461966ba360d5a8f73ff624b606247f3e96b355a7865290fa54300dcfca54effb1d75d72e767583cb84a1256f3686d1e50952a2ea9b174f9f9ef5163096a0d15e36208d242e10f0494ef585517a62373154d4d120964229ff38e720234ca4a7f5ac372f11dd266f6b08f5c4c665c0dc907e20b26451950a88d6219ed1b0114537f000ca47be230c78a117445a85c0eb4e8d16f2019922f3456bb3ed18d246df54a3c51de286e12d951f046404dd357e382e14b0537e26db036e05dcfc0f51946e4625387b4372f7d1e960847e7d01eb3289e3978d71d0f54a5ec405ee39d6b9f17e06d3721675e1df51175a6764527b84fb7663305283ce37fff62ec5f743c63bd402eabbdaa559f8b904afa32506e069ddf763571f02975677b5f8a20d7260263cf4e0900fd682f27da5f912f323e1cf9d44228e3dd51507e7b0cdb186c43a74c626b2b7ead02208c17682beb642c2f0a5722457c466ec55da368deee93642941273197690463869d026051cf114f4d3d407166dbcc45faa57131fc99b16d2e98693c7aaa37747cad4628b6ab2272a5b20e238360ce254455492f99da861af36585116c76390b8b29cc5f51c37017a5936d633553293699435a4864ebee323ead45343c8caf768e815348ac006a22bf489b0b83c49947337eb07217f0071545408f3d199b271bc8614a48550c330d1d1d6834337a9e543b13940b61fee21922e336261f4d76616897723b9fde6d29259e8a1e4ed16d1cf47a5e5d5077e250f3083214f6eded3dc08f1242b2ae752cd0c9471f84850e74f6837d4ab0e5f416b87cc53c7113103753e1c835fae0421e9cc61c55e1ae382489ce9561feeb842a1d0aad39565d493c13913462b4779535ffce6074";
const STEP_CAP: &str = "f578db0752477b3cb5dfb772ecf5635c42c36a6afcb2c82dc3a9c315ced7bc61851982422cc57e5544da22079a45c31700ba86093472b85cb714250a2d8bf9622c8c3a4d6cb76871fabe9745daf229314881170062fd5061b4447970a42aea64c888d11f6df875036dbf475c87481954a9f15e3bcfbd3f0ebb3fd526a80dd0436e4fac0ab94653065aa2152ad8fa1709322aca4c71310c2a21437b48014d7b0e4856ed38d416a3513ac96a08aff6cb5aa1a167714687d26fa722a8645341663734b4fc183e5de868e354d65a3c160e4f99cb4b5b2815582c61a4b7480e6fad2bdc84f96a2f3f2425607e0c375ae1b577d433a40acf64f4118c7b4f6a3a37cf76d80c47736b4e63631f65652a03d1563ee29da86e1af94208d12d8c262c743271402e755d4e789b2659dd332b22526224f8dde23671f61e6f10de99532944fc07b4fe940326330d000a0ee26a99ea894243983177cf204b5c52d81016e2d1222f4a2d5c1c75efe72d12d325067577da21c5dfcc0f3375636d3fb3c353e4a7231c67ac90157841756d22d0794ab3ff180befd7db453a330d398b4d7d4d75cddd599f26d0682078dc6e5f0a624ffc01f12b64268a6d81c564280ab472404c60f666f58c35433d22955c4aff4903c6e909105b6fc77465b5a21059182a57a278640ce008eb09bee14f063f3bcc32d9cf133092070917bd15a064e0fb7e0649139b3b351f8e2a81529a241eb19031bc8d3a6eb5a6b170eef52926cdf3da058853c876f53baf2833eade0077a2f9435f2cee538f39fa6fa18c14509fda2619a281605ecb06b7260e2c7f4d1494846f8988b539286a36762bd6b567fd953c331fa2df27c8ef384e0e20e95e58e30063b0fd1f5e258b3c70c4fa266150ff626d938cd812380d4767f3944e5ea4e58b38938e6526fb6b4d424c60df0175b67230488790075a264f6daf92a15167cd35007423c1152bd0ae032e3ae248cf275b7083a07c07684cc105fee58f1f9047da008f6ec330623d37374338e12ffe0fb071b01ea25edade2c57d695792445166c6fc5f6935e0934526716964c772587d930eb615a01e39fe752d4a12063de9e045a7e494f2a9aef0b17795a435d21176a50899662256677e108caa01673e0edef114bb7be4535f7cd65a886e62e9f413a3ec1b1e15207087124dea5bf451635524f924d51100ef51739e293e456a37073747d228c3e241c272643834c30d5e6bb03cc81224e59983a12e2fc50196520c96087b8ae319f411a297fd40b0cebc5a15fdcbc9a14037ada75b12ca757699d36275110ce45aa3643159338324809396c2605750f3fdc1ff63fdaa0bb1c0c4cb764e677426d36b8996dd89e50442cbf637786e87f4ae2f41a482db5a9294196964c7dbc6c1793c6fb5cbd3d913188e14d047c8cc91588fc6468c4af8d2e1c1f1d3f2829dc18";
const DEV_GENESIS_CAP: &str = "9a3937034a6296677f111453c747b53e1ddec9123d4764173893be1c4151046feadae43d7b572c10ef9a89009e92a96391deb30df1a1be2050db5f36194fa0260e75db20a020cb00a0e0350857edde674773861e1bb06120108c352e7478c762a7a75e28f120533f8f77e72852c05d2c35bdfd28603fe3136713aa2a12b7c70f5ff432316144263a5b4ce71df46d374c6d65dd72c1fc5e10ebbadb036b94c17594642c025f7d4706f8997a3db43a9d11fc6ef430f6b1064a18fba33168c62c629f9da92b6a2eb944d370bf353ced6207cafaae6b73d67d183ffe483ce5043a0e87f3663cf10e221278e21140ecc8630684e64a402e30630536fea83a9aa93a0027a13f61215a2e48ea95fe7494139a273f6c4f6e05d1ab731045dd254eca827777e01454b049d556092d3148ee9d260df115f23a39aeca26795d97582411960e7acbe722f53676152450f86d705c1b083c1648278add030c2053594988cd821f9fc6ce5bfcf89a3bd8099c1b4e4bc7745a9c126360a68850a79b3220c8bc61415e702620c291d300a1ef7e1ef97b406f607878502e8b9110c222dd3cb4977c57223f3669eb3e26211e4e4267d48d3856a76c254ea7c3f02f8fa22b136b8a283f0f3bbe4a1d39c923031326194ce5ec1f129024603dbd505b47c742687af7061497ec805147e22e689b37c26bbf2cfb58df902d39762bcc7035833605cbb4f2018ca25c39062b715e625bcb655db1332525c6be1ed6ebfd29fad519765b793300de7a822a56f5de5c405f2f237224d1432632f103e1c358450458d676cf78275863775a18f6179a52f340e54663c74f22c03e5019cc753a2f80b3443edefb552094c1b45c2b7f0f5756e35d39d5aa8e2fb5fe475ccb40433249358566f5273c5b115c3b21e9d5de48c76afa1fce69d0387df5ad55a39b201175f8990761ac7c1acc06380810d4ca3fbaede957af70c15d347305253913155e6d23c0426cf31f68b3c85110eb7cf76a7e0bc46c80859d5578ee170a1aa2492a33592548128a2d6f0054a5701fb3a94a3c59a10a8c661e1424d16e6e705832165280413d8381e74ec4b3bd39b59e6a0650516424254b5f3a87f1b519ecc23a045270ef748b14891e0bf8b3095f45fe30c4c1513d04dd0906749c14305a719b1a2622a20b126e8658d2735573834ea3072f477e24f6a3730b5b2d4e329481bb765e58710bcbf48c5d9718202c381c593c6b176e4653e75d3987bfd832fde7db4bc24ef95a8feab63c6a924a1c10e5783ae9f8df427d47b34e192e3b5c2cb71216bd46aa2db97e1221eb593310f45d8b7649691f655638e533715c9923a50ba1769daff6514afc124fc469623cb7dfc00d4184ee2c686d1e496d7b64719c9c7f3d5a8c671a94d04d681cb5630f3ef6291c8591d56ecb8d9f717a10ec0a1efcbd30c3ab5f4f7f90b936";
const DEV_STEP_CAP: &str = "5b3cd06b455adf27c11fb87596df8b107b94965612e8c67046ddfb6741426622d52bdb24c76e4e0a639b2110afd50d01c923420b29eaba0ed58bb835ed813d2d15290e0cca3f8b5b0e388a5d2d88131121d7772657539704f62d326aad1cb25da52418020ff71c2808efe62b7d03da2aafa4f207325701750b1b9871f53a843ca334a325243ecd3f9e841b31edbe694fb852a069b2166c298a868748cccdaa112cbd5f2bad34166eef0ceb4754d12770b120be11067f29050956b903090f0f54ded0806d63deba5f04f01e5e98f2bd164e71343c9efdc9525116960d26f52721bf0be53626b24d3cf65a663626ba430431a4ed72fd35440ca13ab3316ac70a4c855e74735dc24924621259026fe379187d44f76ef9dd9c0d316c502ac056f2591c43900bc107170d1326ce2d23339219e73d6f130c595b4c7d39d44e0cbb0913ee64660d8d34752d6423af69426cfd688bfe9b360abf7e4f04897e71f61377681cfbbd3dcc76a53676efaa658042643727443326b045b404a640bc012b03e36eef8d651afaefd94e1b28ba48228a01497a624c0f4539522dd34ee55004d6460a078cb42395934c2d4286a73c9b207f2cdc8a8d4484e1716401a5376939170822ecf7e24c18f2f253412c6e505bcecb2016622a2dd9e9ab6e474cc62cf3ae7758c5db5b2d0453cb1b34299c169c50885fee0bcd1af33ec7075cb3e5495a95fa6dde40466274256907c131c372531c6302f4f0f25beafc463f9dee0b27af57d5472977d76b8ef79e0c696b17425154c911e838d12fec8750738c1ff620d212cd75a1ec4901499d3f0be35095411682b025ece30212fd790624670436687367120a4813db096564c1063a193045d11e9247f4bffd25842a4362b905cc679c767a31350cda44b584442511d85d44c547a431b761e35cc9328d4c09f1e0291d8c320e7873a20b153ee530c715cb0b7b151e5c3b5f4d0cb69ce474497b330c6ee2cd570fcb5b069e84b8122e47130b60c13b4c0800dc43cbbed9429892be74fbf1a02b98c3ad6ae03e17499e75da48c15193237a4c7b5043976e6a70525f616cf25040a1fc870afd1f67084515fb6040307e33fc996f4283d5f43eea14ab2b5357830a62b1102b42c1d95f4a04ed4081690a6ddabd0311e8f5b844d197dc5f618aa668535370233d014c587b08710c9bdff4291c1b2c365310e52931282c00e20d0f1cd5bec12a88b7850779cddb622936bc5718f9467364ca226c9853890a7bb3247366966e2132d62e1a0cb9dd14f9f56364208bdf5ca7c13127f223b460967ee352fe2678772ea0ab27bdddca48125f8342d6c8c202d85782404b58772f44cb7a4c47dab03ee604d100e3e9eb2a590cd3687a2a825c5c284803cff88b4df17bb92618bda03a53bef012892a213555f3dd0ed079ae0a2d07cf3f5f76a31dbb452f62";

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
        let rows = step_rows(&g_proof, r1, h1, &t1, &keys_in, &tree).unwrap();
        println!("chain step: {rows} rows of {} ({:.0}%)", tree.trace_len, 100.0 * rows as f64 / tree.trace_len as f64);
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
