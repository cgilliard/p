//! Proving a block's state transition -- the spike of
//! `docs/CHAIN_RECURSION.md` (step 1): what it costs, in circuit rows, to
//! prove that a block's inputs were unspent outputs (and are now spent)
//! and that its outputs were appended, for two choices of state structure.
//!
//! **Variant B -- a fixed-depth state tree** (what's implemented here in
//! full): one binary Merkle tree of `DEPTH` levels over output positions.
//! A leaf is `EMPTY` until an output is appended there, holds the
//! output's commitment while it's unspent, and becomes `SPENT` once
//! spent -- one structure in place of today's PMMR and bitmap. Nodes are
//! one Poseidon2 permutation each, `[left ‖ right | DOMAIN + level]`
//! (`node`), like the recursion code's Merkle checks. Every operation has
//! the same shape whatever the data -- a circuit is fixed in advance, so
//! that matters: an MMR's appends merge a data-dependent number of peaks,
//! and its paths vary in length. The state the chain commits to is
//! `(root, count)`.
//!
//! - **Spend** at position `p`: the leaf is the commitment (its path
//!   recomputes the current root), and is set to `SPENT` (the same path
//!   with the new leaf gives the next root) -- 2 × `DEPTH` permutations.
//! - **Append** at position `count`: the leaf is `EMPTY`, and is set to
//!   the commitment; `count` increases -- the same 2 × `DEPTH`.
//!
//! **Variant A -- today's structures** (`pmmr`, `bitmap`), measured by
//! building their primitives in the circuit: a PMMR node hash
//! (`hash_bytes` over `pos ‖ left ‖ right`) and a bitmap page hash
//! (`hash_bytes` over 4096 bytes), each checked against the native
//! hash, then multiplied out by path lengths (`variant_a_costs`).
//!
//! Not yet handled (open questions in the doc): rejecting a duplicate of
//! a live output (the tree is indexed by position, so it can't see one).

#![allow(dead_code)]

use std::collections::HashMap;

use crate::circuit::{Builder, EVar, OVar, Octet};
use crate::ext::Ext;
use crate::poseidon2::BabyBear;

pub use crate::state_tree::{DEPTH, EMPTY, SPENT, capacity, leaf_capacity, node};

// ---- the tree, natively ------------------------------------------------------

/// The state tree in memory (sparse: untouched subtrees are implicit) --
/// a reference for `state_tree::StateTree`, and the witness source for
/// circuit tests.
pub struct MemTree {
    /// `(height, index)` -> hash, height 0 being leaves.
    nodes: HashMap<(usize, u64), Octet>,
    /// The hash of an all-`EMPTY` subtree of each height.
    empty: Vec<Octet>,
    count: u64,
    /// Where each unspent leaf is.
    position: HashMap<Octet, u64>,
}

impl Default for MemTree {
    fn default() -> Self {
        let empty = crate::state_tree::empty_hashes();
        MemTree {
            nodes: HashMap::new(),
            empty,
            count: 0,
            position: HashMap::new(),
        }
    }
}

impl MemTree {
    pub fn root(&self) -> Octet {
        self.get(DEPTH, 0)
    }

    pub fn count(&self) -> u64 {
        self.count
    }

    fn get(&self, height: usize, index: u64) -> Octet {
        self.nodes.get(&(height, index)).copied().unwrap_or(self.empty[height])
    }

    /// The siblings on the path from leaf `position` up, bottom first.
    pub fn path(&self, position: u64) -> Vec<Octet> {
        (0..DEPTH).map(|h| self.get(h, (position >> h) ^ 1)).collect()
    }

    fn set(&mut self, position: u64, leaf: Octet) {
        self.nodes.insert((0, position), leaf);
        let mut hash = leaf;
        for h in 0..DEPTH {
            let index = position >> h;
            let sibling = self.get(h, index ^ 1);
            hash = if index & 1 == 0 { node(h, &hash, &sibling) } else { node(h, &sibling, &hash) };
            self.nodes.insert((h + 1, index >> 1), hash);
        }
    }

    /// Append an output's leaf; its position.
    pub fn append(&mut self, leaf: Octet) -> u64 {
        let p = self.count;
        self.set(p, leaf);
        self.position.insert(leaf, p);
        self.count += 1;
        p
    }

    /// Put an output's leaf at an empty `position`, at or past `count`
    /// (which then covers it): how a block's chunks fill its window of
    /// positions, in any order.
    pub fn place(&mut self, position: u64, leaf: Octet) {
        self.set(position, leaf);
        self.position.insert(leaf, position);
        self.count = self.count.max(position + 1);
    }

    /// Spend an unspent output, by its leaf; its position, or `None`.
    pub fn spend(&mut self, leaf: &Octet) -> Option<u64> {
        let p = self.position.remove(leaf)?;
        self.set(p, SPENT);
        Some(p)
    }

    pub fn position_of(&self, leaf: &Octet) -> Option<u64> {
        self.position.get(leaf).copied()
    }
}

// ---- the tree, in the circuit -------------------------------------------------

/// `x`'s low `n` bits (asserting there are no more), lowest first.
pub fn bits_of(b: &mut Builder, x: EVar, n: usize) -> Vec<EVar> {
    let mut rest = x;
    let mut bits = Vec::with_capacity(n);
    for _ in 0..n {
        let (half, bit) = b.bit_step(rest);
        bits.push(bit);
        rest = half;
    }
    b.assert_zero(rest);
    bits
}

/// `x`'s 31 bits, lowest first -- its *canonical* value, below p: with
/// only `bits_of`, a value below 2^27 - 1 could also be written as itself
/// plus p (another dataset index than validators pick, say, or another
/// position in the state tree).
pub(crate) fn canonical_bits(b: &mut Builder, x: EVar) -> Vec<EVar> {
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

/// A position's `DEPTH` path bits, lowest first: its canonical value
/// (positions stay below p), so each position has exactly one path.
pub(crate) fn position_bits(b: &mut Builder, position: EVar) -> Vec<EVar> {
    let mut bits = canonical_bits(b, position);
    while bits.len() < DEPTH {
        bits.push(b.zero());
    }
    bits
}

/// The root above `leaf`, given the path's direction bits (1: `leaf`'s
/// side is the right) and siblings.
fn root_from(b: &mut Builder, leaf: OVar, bits: &[EVar], siblings: &[OVar]) -> OVar {
    let mut h = leaf;
    for (level, (&bit, &sibling)) in bits.iter().zip(siblings).enumerate() {
        let cap = b.const_octet(capacity(level));
        h = b.permute(h, sibling, cap, Some(bit))[0];
    }
    h
}

/// Replace `old` by `new` at the position given by `bits`, under `root`:
/// asserts `old` is there, and returns the new root.
pub(crate) fn replace(b: &mut Builder, root: OVar, bits: &[EVar], siblings: &[Octet], old: OVar, new: OVar) -> OVar {
    let siblings: Vec<OVar> = siblings.iter().map(|s| b.witness_octet(*s)).collect();
    let before = root_from(b, old, bits, &siblings);
    b.assert_eq_octet(before, root);
    root_from(b, new, bits, &siblings)
}

/// An unspent output's leaf, `leaf(commitment, nonce)`, in the circuit.
pub fn leaf_hash(b: &mut Builder, commitment: OVar, nonce: OVar) -> OVar {
    let cap = b.const_octet(leaf_capacity());
    b.permute(commitment, nonce, cap, None)[0]
}

/// Spend the output `(commitment, nonce)` at (witness) `position`: the
/// new root.
pub fn spend(b: &mut Builder, root: OVar, commitment: OVar, nonce: OVar, position: u64, siblings: &[Octet]) -> OVar {
    let p = b.witness_ext(Ext::from_base(BabyBear::new(position as u32)));
    let bits = position_bits(b, p);
    let leaf = leaf_hash(b, commitment, nonce);
    let spent = b.const_octet(SPENT);
    replace(b, root, &bits, siblings, leaf, spent)
}

/// Append the output `(commitment, nonce)` at position `count`: the new
/// root and count.
pub fn append(b: &mut Builder, root: OVar, count: EVar, commitment: OVar, nonce: OVar, siblings: &[Octet]) -> (OVar, EVar) {
    let bits = position_bits(b, count);
    let leaf = leaf_hash(b, commitment, nonce);
    let empty = b.const_octet(EMPTY);
    let root = replace(b, root, &bits, siblings, empty, leaf);
    let next = b.add_base(count, BabyBear::ONE);
    (root, next)
}

/// An output as the state sees it: its commitment and nonce limbs.
pub type StateOutput = (Octet, Octet);

fn leaf_of((commitment, nonce): &StateOutput) -> Octet {
    crate::state_tree::compress_leaf(commitment, nonce)
}

/// One block's state transition, in the circuit, against `tree` (which
/// it updates natively along the way, for the witness): spend `inputs`,
/// append `outputs`. Returns the final root and count cells.
pub fn transition(b: &mut Builder, tree: &mut MemTree, inputs: &[StateOutput], outputs: &[StateOutput]) -> (OVar, EVar) {
    let mut root = b.witness_octet(tree.root());
    let mut count = b.witness_ext(Ext::from_base(BabyBear::new(tree.count() as u32)));
    for o in inputs {
        let p = tree.position_of(&leaf_of(o)).expect("spending an unspent output");
        let siblings = tree.path(p);
        let (commitment, nonce) = (b.witness_octet(o.0), b.witness_octet(o.1));
        root = spend(b, root, commitment, nonce, p, &siblings);
        tree.spend(&leaf_of(o));
    }
    for o in outputs {
        let siblings = tree.path(tree.count());
        let (commitment, nonce) = (b.witness_octet(o.0), b.witness_octet(o.1));
        (root, count) = append(b, root, count, commitment, nonce, &siblings);
        tree.append(leaf_of(o));
    }
    (root, count)
}

// ---- variant A: today's byte hashing, in the circuit ---------------------------
//
// (The PMMR and bitmap these measured were replaced by the state tree on
// the strength of these numbers; kept as the record of why.)

/// The old bitmap's page size.
const OLD_PAGE_BYTES: usize = 4096;

/// The low `n` bits of a base value (lowest first), asserting it has no
/// more -- as base cells.
fn byte_bits(b: &mut Builder, x: EVar, n: usize) -> Vec<EVar> {
    bits_of(b, x, n)
}

/// `Σ bits[i]·2^i` as a base cell (one row per bit, Horner from the top).
pub(crate) fn from_bits(b: &mut Builder, bits: &[EVar]) -> EVar {
    let mut acc = b.zero();
    for &bit in bits.iter().rev() {
        let z = BabyBear::ZERO;
        acc = b.arith(z, Some(acc), None, BabyBear::new(2), z, Some(bit), BabyBear::ONE, [z; 4]);
    }
    acc
}

/// Pack base cells into octets, 8 to an octet (zero-padded), via
/// extension cells `Σ v_i X^i`.
pub(crate) fn pack_octets(b: &mut Builder, values: &[EVar]) -> Vec<OVar> {
    let powers: Vec<EVar> = (0..4)
        .map(|i| {
            let mut x = [BabyBear::ZERO; 4];
            x[i] = BabyBear::ONE;
            b.const_ext(Ext(x))
        })
        .collect();
    let mut halves = Vec::new();
    for four in values.chunks(4) {
        let mut acc = b.zero();
        for (i, &v) in four.iter().enumerate() {
            acc = b.mul_add(v, powers[i], acc);
        }
        halves.push(acc);
    }
    if halves.len() % 2 == 1 {
        let z = b.zero();
        halves.push(z);
    }
    halves.chunks(2).map(|h| b.pack(h[0], h[1])).collect()
}

/// `poseidon2::hash_bytes`' sponge (`hash_elements`-style: blocks of 16
/// added into the rate) over base cells, recording `length` bytes.
fn sponge_elements(b: &mut Builder, domain: u32, length: usize, elements: &[EVar]) -> OVar {
    let zero = b.const_octet(EMPTY);
    let mut cap = [BabyBear::ZERO; 8];
    cap[0] = BabyBear::new(domain);
    cap[1] = BabyBear::new(length as u32);
    let mut state = [zero, zero, b.const_octet(cap)];
    for block in elements.chunks(16) {
        let octets = pack_octets(b, block);
        let mut rate = [state[0], state[1]];
        for (k, o) in octets.into_iter().enumerate() {
            let (sl, sh) = b.halves(rate[k]);
            let (ol, oh) = b.halves(o);
            let (l, h) = (b.add(sl, ol), b.add(sh, oh));
            rate[k] = b.pack(l, h);
        }
        state = b.permute(rate[0], rate[1], state[2], None);
    }
    state[0]
}

/// A digest's bytes as bits: each of its 8 elements is 4 little-endian
/// bytes (`digest_to_bytes`), so 32 bits each.
pub(crate) fn digest_bits(b: &mut Builder, d: OVar) -> Vec<EVar> {
    let (lo, hi) = b.halves(d);
    let mut bits = Vec::with_capacity(256);
    for half in [lo, hi] {
        for lane in 0..4 {
            let e = b.lane(half, lane);
            bits.extend(byte_bits(b, e, 32));
        }
    }
    bits
}

/// `hash_bytes` of a byte string given as bits (8 per byte, low first):
/// regrouped into 3-byte elements, then sponged.
pub(crate) fn hash_bits(b: &mut Builder, bits: &[EVar]) -> OVar {
    let elements: Vec<EVar> = bits.chunks(24).map(|c| from_bits(b, c)).collect();
    sponge_elements(b, crate::poseidon2::DOMAIN_BYTES, bits.len() / 8, &elements)
}

/// Today's PMMR node hash, `hash_bytes(pos_le(8) ‖ left ‖ right)`, with
/// `pos` a witness.
pub fn pmmr_node_bytes(b: &mut Builder, pos: u64, left: OVar, right: OVar) -> OVar {
    let mut bits = Vec::new();
    for byte in pos.to_le_bytes() {
        let v = b.witness_ext(Ext::from_base(BabyBear::new(byte as u32)));
        bits.extend(byte_bits(b, v, 8));
    }
    bits.extend(digest_bits(b, left));
    bits.extend(digest_bits(b, right));
    hash_bits(b, &bits)
}

/// Today's bitmap page hash, `hash_bytes(page)` (4096 bytes), with one
/// bit of byte `byte` checked as 0 and set: the old and new page hashes.
/// The page's other 3-byte elements are free witness (the hash binds
/// them); only the changed element is decomposed.
pub fn bitmap_page_update(b: &mut Builder, page: &[u8], byte: usize, bit: usize) -> (OVar, OVar) {
    let elements: Vec<u32> = page.chunks(3).map(|c| c.iter().rev().fold(0u32, |a, &x| (a << 8) | x as u32)).collect();
    let target = byte / 3;
    let cells: Vec<EVar> = elements.iter().map(|&e| b.witness_ext(Ext::from_base(BabyBear::new(e)))).collect();
    let mut bits = byte_bits(b, cells[target], 24);
    b.assert_zero(bits[8 * (byte % 3) + bit]);
    bits[8 * (byte % 3) + bit] = b.one();
    let changed = from_bits(b, &bits);
    let mut new_cells = cells.clone();
    new_cells[target] = changed;
    let old = sponge_elements(b, crate::poseidon2::DOMAIN_BYTES, page.len(), &cells);
    let new = sponge_elements(b, crate::poseidon2::DOMAIN_BYTES, page.len(), &new_cells);
    (old, new)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poseidon2::{digest_from_bytes, hash_bytes, hash_bytes_32};
    use crate::stark;
    use crate::transcript::Transcript;

    fn challenges() -> Vec<Ext> {
        let mut t = Transcript::new(b"state circuit test");
        (0..2).map(|_| t.challenge_ext(b"c")).collect()
    }

    fn commitment(k: u64) -> Octet {
        digest_from_bytes(&hash_bytes_32(&k.to_le_bytes()))
    }

    /// An output for the state: a commitment and some nonce limbs.
    fn output(k: u64) -> StateOutput {
        (commitment(k), commitment(k + 1_000_000))
    }

    const PARAMS: stark::Params = stark::Params {
        log_blowup: 2,
        num_queries: 8,
        grinding_bits: 0,
        hiding: false,
    };

    #[test]
    fn the_native_tree_spends_and_appends() {
        let mut t = MemTree::default();
        let empty_root = t.root();
        let p = t.append(leaf_of(&output(1)));
        assert_eq!((p, t.count()), (0, 1));
        assert_ne!(t.root(), empty_root);
        t.append(leaf_of(&output(2)));
        assert_eq!(t.spend(&leaf_of(&output(1))), Some(0));
        assert_eq!(t.spend(&leaf_of(&output(1))), None, "spent twice");
        assert_eq!(t.spend(&leaf_of(&output(9))), None, "never existed");
        // A different order gives a different root.
        let mut u = MemTree::default();
        u.append(leaf_of(&output(2)));
        u.append(leaf_of(&output(1)));
        u.spend(&leaf_of(&output(1)));
        assert_ne!(u.root(), t.root());
    }

    /// The circuit's roots match the native tree's, and the trace
    /// satisfies its constraints.
    #[test]
    fn a_block_transition_in_the_circuit_matches_the_native_tree() {
        let mut tree = MemTree::default();
        for k in 0..20 {
            tree.append(leaf_of(&output(k)));
        }
        let inputs = [output(3), output(17), output(0)];
        let outputs = [output(100), output(101)];
        let mut b = Builder::new();
        let (root, count) = transition(&mut b, &mut tree, &inputs, &outputs);
        assert_eq!(b.octet_value(root), tree.root());
        assert_eq!(b.ext_value(count), Ext::from_base(BabyBear::new(22)));
        let circuit = b.finish();
        let air = circuit.air(&PARAMS);
        stark::check(&air, &circuit.witness, &challenges()).unwrap();
    }

    /// A spend of something that isn't there can't be laid out (the
    /// path doesn't recompute the root).
    #[test]
    #[should_panic(expected = "assertion fails")]
    fn spending_a_missing_output_fails() {
        let mut tree = MemTree::default();
        tree.append(leaf_of(&output(1)));
        let mut b = Builder::new();
        let root = b.witness_octet(tree.root());
        let (fake, nonce) = (b.witness_octet(output(2).0), b.witness_octet(output(2).1));
        let path = tree.path(0);
        spend(&mut b, root, fake, nonce, 0, &path);
    }

    /// Variant A's primitives match the native byte hashes.
    #[test]
    fn todays_byte_hashes_in_the_circuit_match_native() {
        let mut b = Builder::new();
        let (l, r) = (commitment(1), commitment(2));
        let (lv, rv) = (b.witness_octet(l), b.witness_octet(r));
        let h = pmmr_node_bytes(&mut b, 77, lv, rv);
        let mut bytes = 77u64.to_le_bytes().to_vec();
        bytes.extend(crate::poseidon2::digest_to_bytes(l));
        bytes.extend(crate::poseidon2::digest_to_bytes(r));
        assert_eq!(b.octet_value(h), hash_bytes(&bytes));

        let mut page = vec![0u8; OLD_PAGE_BYTES];
        page[10] = 0b0000_0101;
        let (old, new) = bitmap_page_update(&mut b, &page, 10, 1);
        assert_eq!(b.octet_value(old), hash_bytes(&page));
        page[10] |= 0b10;
        assert_eq!(b.octet_value(new), hash_bytes(&page));
        let circuit = b.finish();
        let air = circuit.air(&PARAMS);
        stark::check(&air, &circuit.witness, &challenges()).unwrap();
    }

    /// The spike's numbers: rows per input and per output for both
    /// variants, and what a 1k- and 10k-transaction block would take.
    /// `cargo test --release -- --ignored --nocapture state_costs`.
    #[test]
    #[ignore]
    fn state_costs() {
        // Variant B, measured: spends and appends against a populated tree.
        let mut tree = MemTree::default();
        for k in 0..1000 {
            tree.append(leaf_of(&output(k)));
        }
        let rows = |inputs: usize, outputs: usize, tree: &mut MemTree| {
            let ins: Vec<StateOutput> = (0..inputs as u64).map(|k| output(k * 7 % 1000)).collect();
            let outs: Vec<StateOutput> = (0..outputs as u64).map(|k| output(2_000_000 + k)).collect();
            let mut b = Builder::new();
            transition(&mut b, tree, &ins, &outs);
            b.rows_used()
        };
        let base = rows(0, 0, &mut tree);
        let per_input = (rows(10, 0, &mut tree) - base) / 10;
        let per_output = (rows(0, 10, &mut tree) - base) / 10;

        // Variant A's primitives, measured.
        let mut b = Builder::new();
        let (l, r) = (b.witness_octet(commitment(1)), b.witness_octet(commitment(2)));
        let before = b.rows_used();
        pmmr_node_bytes(&mut b, 77, l, r);
        let a_node = b.rows_used() - before;
        let page = vec![0u8; OLD_PAGE_BYTES];
        let before = b.rows_used();
        bitmap_page_update(&mut b, &page, 0, 0);
        let a_page = b.rows_used() - before;
        // A spend: PMMR membership (~30 node hashes at a billion outputs)
        // + bitmap: the page check-and-set and 49 levels, old and new path
        // (the bitmap node is `level(4) ‖ left ‖ right`, 68 bytes: about
        // the PMMR node's cost). An append: ~2 node hashes amortized, plus
        // bagging ~30 peaks once per block (ignored here).
        let a_input = 30 * a_node + a_page + 2 * 49 * a_node;
        let a_output = 2 * a_node;

        println!("variant B (fixed-depth state tree, measured): {per_input} rows per input, {per_output} per output");
        println!("variant A (today's PMMR + bitmap, from measured primitives): node hash {a_node} rows, page update {a_page} rows");
        println!("  ~{a_input} rows per input, ~{a_output} per output");
        let block = crate::prover::CHUNK_SHAPE.num_blocks * crate::poseidon2_air::ROWS / crate::prover::CHUNK_SHAPE.inputs;
        println!("for scale: a block proof spends ~{block} rows per input (a full chunk / 10 inputs)");
        for txs in [1_000usize, 10_000] {
            let (i, o) = (txs * 5 / 2, txs * 5 / 2);
            println!(
                "{txs} txs (2.5 in, 2.5 out): B {:.1}M rows, A {:.1}M rows; block proofs ~{:.1}M rows",
                (i * per_input + o * per_output) as f64 / 1e6,
                (i * a_input + o * a_output) as f64 / 1e6,
                (i * block) as f64 / 1e6
            );
        }

        // Time one proof of a variant-B transition, to turn rows into time.
        let mut b = Builder::new();
        transition(&mut b, &mut tree, &[output(500), output(501)], &[output(3_000_000)]);
        let circuit = b.finish_padded(1 << 16);
        let air = circuit.air(&crate::prover::TREE.params);
        let start = std::time::Instant::now();
        let proof = stark::prove(&air, &circuit.witness, &crate::prover::TREE.params, [1; 32]).unwrap();
        println!("proving {} rows (padded): {:.2?}, {} KB", circuit.trace_len, start.elapsed(), proof.to_bytes().len() / 1024);
    }
}
