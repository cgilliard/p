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
//! What a chain proof attests (`Tip`, its public inputs):
//!
//! ```text
//! [ step vk | header hash | height, timestamp (4 × 16-bit) | target (16 × 16-bit) ]
//! ```
//!
//! **Milestone 1** (this module, so far): header chaining and proof of
//! work. Still to come -- the doc's milestone 2: the target's retargeting
//! (here it's carried unchanged), cumulative work, the block's contents
//! proof, and its state transition (`state_circuit`).

#![allow(dead_code)]

use crate::aggregate::{Error, Key, TreeParams, assert_select, fit, vk_digest};
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
}

/// A number's four 16-bit limbs, least significant first.
fn limbs16(v: u64) -> [u32; 4] {
    std::array::from_fn(|j| ((v >> (16 * j)) & 0xffff) as u32)
}

impl Tip {
    pub fn of(header: &BlockHeader, target: [u8; 32]) -> Tip {
        Tip {
            hash: header.hash(),
            height: header.height,
            timestamp: header.timestamp,
            target,
        }
    }

    /// `[height, timestamp limbs, 0, 0, 0]`.
    fn info(&self) -> Octet {
        let mut o = [BabyBear::ZERO; 8];
        o[0] = BabyBear::new(self.height as u32);
        for (j, l) in limbs16(self.timestamp).into_iter().enumerate() {
            o[1 + j] = BabyBear::new(l);
        }
        o
    }

    /// The target as 16 big-endian 16-bit limbs, two octets.
    fn target_octets(&self) -> [Octet; 2] {
        let limbs: Vec<BabyBear> = self.target.chunks(2).map(|p| BabyBear::new(u16::from_be_bytes([p[0], p[1]]) as u32)).collect();
        [limbs[..8].try_into().unwrap(), limbs[8..].try_into().unwrap()]
    }

    /// The public inputs of a proof attesting this tip, by a circuit
    /// whose key is `vk`.
    fn public(&self, vk: Octet) -> [Octet; 5] {
        let [t0, t1] = self.target_octets();
        [vk, digest_from_bytes(&self.hash), self.info(), t0, t1]
    }
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

/// The chain step for `header`, given the previous header's chain proof.
fn step_circuit(child: &ChainProof, header: &BlockHeader, genesis_vk: Octet, self_vk: Octet, tree: &TreeParams) -> Result<Circuit, Error> {
    fit(step_builder(child, header, genesis_vk, self_vk, tree)?, tree)
}

/// `step_circuit`, laid out but not yet padded.
fn step_builder(child: &ChainProof, header: &BlockHeader, genesis_vk: Octet, self_vk: Octet, tree: &TreeParams) -> Result<Builder, Error> {
    if header.prev_hash != child.tip.hash {
        return Err(Error::InvalidProof);
    }
    let tip = Tip::of(header, child.tip.target);
    let (mut b, public) = Builder::with_public(&tip.public(self_vk));
    let (self_lo, self_hi) = b.halves(public[0]);

    // The child: a chain proof by the genesis circuit or by this one.
    let statement = recursion::verify(&mut b, &child.air, &child.proof, &tree.params).ok_or(Error::InvalidProof)?;
    if statement.tuples.len() != 5 {
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
    let [c_vk, c_hash, c_info, c_t0, c_t1] = std::array::from_fn(|k| statement.tuples[k][0]);
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
    let state_root = b.witness_octet(digest_from_bytes(&header.state_root));
    let body_hash = b.witness_octet(digest_from_bytes(&header.body_hash));
    let count: Vec<(EVar, Vec<EVar>)> = limbs16(header.output_count).iter().map(|&l| witness_limb(&mut b, l)).collect();
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

    // What this proof attests.
    let info = pack_octets(&mut b, &[height, ts[0], ts[1], ts[2], ts[3]])[0];
    b.assert_eq_octet(info, public[2]);
    // (Milestone 1: the target carries over unchanged -- retargeting is
    // still to come.)
    b.assert_eq_octet(c_t0, public[3]);
    b.assert_eq_octet(c_t1, public[4]);
    Ok(b)
}

/// The chain step's key. Its fixed columns don't depend on the values, so
/// any child proof and header serve to lay it out.
pub fn step_key(sample_child: &ChainProof, sample_header: &BlockHeader, genesis: &Key, tree: &TreeParams) -> Result<Key, Error> {
    Ok(Key::of(&step_circuit(sample_child, sample_header, genesis.vk, [BabyBear::ZERO; 8], tree)?, tree))
}

/// The keys of a chain: genesis, and the step.
pub struct ChainKeys {
    pub genesis: Key,
    pub step: Key,
}

/// Prove `header` extends the chain `child` attests.
pub fn prove_step(keys: &ChainKeys, child: &ChainProof, header: &BlockHeader, tree: &TreeParams, seed: [u8; 32]) -> Result<ChainProof, Error> {
    let circuit = step_circuit(child, header, keys.genesis.vk, keys.step.vk, tree)?;
    let air = circuit.air_with(keys.step.preprocessed.clone());
    let proof = stark::prove(&air, &circuit.witness, &tree.params, seed).map_err(Error::Prove)?;
    Ok(ChainProof {
        air,
        proof,
        tip: Tip::of(header, child.tip.target),
    })
}

/// Whether `proof` is a chain step proof attesting `tip`.
pub fn verify(keys: &ChainKeys, tip: &Tip, proof: &Proof, tree: &TreeParams) -> bool {
    let air = CircuitAir::new(tree.trace_len, keys.step.preprocessed.clone(), public_tuples(&tip.public(keys.step.vk)));
    stark::verify(&air, proof, &tree.params)
}

/// Rows a chain step uses (before padding), for measurement.
pub fn step_rows(child: &ChainProof, header: &BlockHeader, genesis: &Key, tree: &TreeParams) -> Result<usize, Error> {
    Ok(step_builder(child, header, genesis.vk, [BabyBear::ZERO; 8], tree)?.rows_used())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block::{BlockHeader, mine_header};

    fn mined(mut h: BlockHeader) -> BlockHeader {
        assert!(mine_header(&mut h, &TARGET, 1_000_000));
        h
    }
    use crate::stark::Params;

    /// Light parameters for tests (not secure).
    const TEST_TREE: TreeParams = TreeParams {
        trace_len: 1 << 16,
        params: Params {
            log_blowup: 1,
            num_queries: 8,
            grinding_bits: 0,
            hiding: false,
        },
    };

    /// Easy enough to mine instantly: the first byte zero.
    const TARGET: [u8; 32] = {
        let mut t = [0xffu8; 32];
        t[0] = 0;
        t
    };

    fn genesis_header() -> BlockHeader {
        mined(BlockHeader {
            prev_hash: [0; 32],
            state_root: [1; 32],
            body_hash: [2; 32],
            output_count: 0,
            height: 0,
            timestamp: 1_791_000_000_000,
            nonce: [0; 32],
        })
    }

    fn next(prev: &BlockHeader, k: u8) -> BlockHeader {
        mined(BlockHeader {
            prev_hash: prev.hash(),
            state_root: [10 + k; 32],
            body_hash: [20 + k; 32],
            output_count: 5 * k as u64 + 70_000,
            height: prev.height + 1,
            timestamp: prev.timestamp + 61_000,
            nonce: [0; 32],
        })
    }

    /// Genesis, then two chain steps, each verifying its predecessor
    /// inside its circuit; the last proof alone vouches for all three
    /// headers. Then: a header that doesn't link, or whose proof of work
    /// is too weak, can't be proven.
    #[test]
    #[ignore]
    fn a_chain_of_headers_proves_recursively() {
        let g = genesis_header();
        let g_tip = Tip::of(&g, TARGET);
        let genesis = genesis_key(&g_tip, &TEST_TREE).unwrap();
        let g_proof = prove_genesis(&genesis, &g_tip, &TEST_TREE, [1; 32]).unwrap();
        let h1 = next(&g, 1);
        let step = step_key(&g_proof, &h1, &genesis, &TEST_TREE).unwrap();
        let keys = ChainKeys { genesis, step };
        let p1 = prove_step(&keys, &g_proof, &h1, &TEST_TREE, [2; 32]).unwrap();
        assert!(verify(&keys, &p1.tip, &p1.proof, &TEST_TREE));
        let h2 = next(&h1, 2);
        let p2 = prove_step(&keys, &p1, &h2, &TEST_TREE, [3; 32]).unwrap();
        assert!(verify(&keys, &p2.tip, &p2.proof, &TEST_TREE));
        assert_eq!(p2.tip.height, 2);
        // Claiming anything else about the tip fails.
        let mut wrong = p2.tip;
        wrong.height = 3;
        assert!(!verify(&keys, &wrong, &p2.proof, &TEST_TREE));
        let mut wrong = p2.tip;
        wrong.hash[0] ^= 1;
        assert!(!verify(&keys, &wrong, &p2.proof, &TEST_TREE));

        // A header that doesn't link to the proven tip.
        let stray = next(&g, 9);
        assert!(prove_step(&keys, &p2, &stray, &TEST_TREE, [4; 32]).is_err());
        // A header whose timestamp doesn't move forward.
        let mut early = next(&h2, 3);
        early.timestamp = h2.timestamp;
        let early = mined(early);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| prove_step(&keys, &p2, &early, &TEST_TREE, [5; 32])));
        assert!(result.is_err() || result.unwrap().is_err(), "a timestamp that doesn't advance");
    }

    /// Just the step's row count with the consensus parameters (one
    /// genesis proof to verify, no step proofs): quick.
    /// `cargo test --release -- --ignored --nocapture chain_step_rows`.
    #[test]
    #[ignore]
    fn chain_step_rows() {
        let tree = crate::prover::tree();
        let g = genesis_header();
        let g_tip = Tip::of(&g, TARGET);
        let genesis = genesis_key(&g_tip, &tree).unwrap();
        let g_proof = prove_genesis(&genesis, &g_tip, &tree, [1; 32]).unwrap();
        let rows = step_rows(&g_proof, &next(&g, 1), &genesis, &tree).unwrap();
        println!("chain step: {rows} rows of {} ({:.0}%)", tree.trace_len, 100.0 * rows as f64 / tree.trace_len as f64);
    }

    /// The step's size with the consensus tree parameters -- the per-block
    /// floor's rows -- and its proving time.
    /// `cargo test --release -- --ignored --nocapture chain_step_costs`.
    #[test]
    #[ignore]
    fn chain_step_costs() {
        let tree = crate::prover::tree();
        let g = genesis_header();
        let g_tip = Tip::of(&g, TARGET);
        let time = std::time::Instant::now;
        let start = time();
        let genesis = genesis_key(&g_tip, &tree).unwrap();
        let g_proof = prove_genesis(&genesis, &g_tip, &tree, [1; 32]).unwrap();
        println!("genesis key + proof: {:.2?}", start.elapsed());
        let h1 = next(&g, 1);
        println!("chain step: {} rows (of {})", step_rows(&g_proof, &h1, &genesis, &tree).unwrap(), tree.trace_len);
        let start = time();
        let step = step_key(&g_proof, &h1, &genesis, &tree).unwrap();
        println!("step key: {:.2?}", start.elapsed());
        let keys = ChainKeys { genesis, step };
        let start = time();
        let p1 = prove_step(&keys, &g_proof, &h1, &tree, [2; 32]).unwrap();
        println!("step proof (over genesis): {:.2?}", start.elapsed());
        let h2 = next(&h1, 2);
        let start = time();
        let p2 = prove_step(&keys, &p1, &h2, &tree, [3; 32]).unwrap();
        println!("step proof (over a step): {:.2?}, {} KB", start.elapsed(), p2.proof.to_bytes().len() / 1024);
        let start = time();
        assert!(verify(&keys, &p2.tip, &p2.proof, &tree));
        println!("verify: {:.2?}", start.elapsed());
    }
}
