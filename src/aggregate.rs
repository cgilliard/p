//! Aggregation trees: a block's transactions proven in chunks, the chunk
//! proofs combined into one whose size and verification cost don't depend
//! on how many chunks it covers (see `docs/RECURSION.md`).
//!
//! # Chunks
//!
//! A block's transactions are split into **chunks** of whole transactions,
//! each proven on its own with the block circuit (`block_air`) as
//! `sum(inputs) + a == sum(outputs) + b` for public amounts `a`, `b` --
//! so chunks can be proven as soon as their transactions are known. The
//! amounts carry up the tree, summed; the block balances if the root's
//! totals satisfy `A - B == reward`. A chunk's own `a`, `b` (its fees)
//! never appear outside the tree. All chunks have one `ChunkShape` (padded
//! to it), so one wrap circuit verifies any of them.
//!
//! # Tree
//!
//! Every proof in a tree is of a circuit (`circuit`) with the same trace
//! length and parameters (`TreeParams`), and the same six public inputs,
//! `[vk, data, amounts, root_in, root_out, counts]` -- the last three the
//! chain state (`state_tree`) it moves between (`StateChange`):
//!
//! - A **wrap** circuit (W) verifies one chunk proof; `data` is the hash
//!   of the chunk's statement with its amounts blanked (`chunk_data`), and
//!   `amounts` its `[a limbs, b limbs]`, range-checked. It also **applies
//!   the chunk to the state** (`apply_transition`): each input's output
//!   -- `leaf(commitment, nonce)` at its position -- becomes spent, each
//!   output's leaf is appended, unused slots change nothing. Its `vk`
//!   input is unused.
//! - An **aggregation** circuit (A) verifies two tree proofs; `data` is
//!   the hash of theirs (`data_node`), `amounts` their sum (carried, so it
//!   can't wrap), and the state runs from the left child's start, through
//!   the point where it ends and the right child starts (they must
//!   match), to the right child's end.
//!
//! Since all tree proofs have one shape, A's verifier logic handles any
//! child; *which* circuit a child is of is told by its verifying key, the
//! hash of its preprocessed cap (`vk_digest`). A child must be either W
//! (whose key A has built in) or A itself. A can't build in its *own* key
//! -- that would make its fixed columns depend on their own commitment --
//! so it takes it as the public input `vk` instead, and requires every A
//! child to have carried the same `vk`. Whoever checks the root confirms
//! `vk` is A's real key, which then holds all the way down.
//!
//! The tree over `k` chunks has a canonical shape (`tree_data`): pair
//! neighbours level by level, carrying a lone last node up unpaired.

#![allow(dead_code)]

use std::sync::Arc;

use crate::block_air::BlockAir;
use crate::circuit::{Builder, Circuit, CircuitAir, EVar, OVar, Octet};
use crate::ext::Ext;
use crate::merkle::Hash;
use crate::output::{AMOUNT_LIMBS, amount_limbs};
use crate::poseidon2::{BabyBear, DOMAIN_DATA_LEAF, DOMAIN_DATA_NODE, DOMAIN_VK, digest_from_bytes, hash_octets, hash_pair};
use crate::recursion::{self, RecursiveAir};
use crate::stark::{self, Params, Preprocessed, Proof};
use crate::transcript::octet_of;

#[derive(Debug)]
pub enum Error {
    /// A proof to be verified in-circuit doesn't verify (or isn't of a
    /// shape the verifier circuit handles).
    InvalidProof,
    /// The circuit needs more rows than the tree's trace length.
    TooLarge { rows: usize, trace_len: usize },
    Prove(stark::Error),
}

/// What every proof in a tree shares.
#[derive(Clone, Copy, Debug)]
pub struct TreeParams {
    pub trace_len: usize,
    pub params: Params,
}

/// A verifying key's digest: the hash of a circuit's preprocessed cap.
pub fn vk_digest(cap: &[Hash]) -> Octet {
    let elements: Vec<BabyBear> = cap.iter().flat_map(digest_from_bytes).collect();
    hash_octets(DOMAIN_VK, elements.len(), &elements)
}

/// A tree leaf's data: the hash of a chunk's statement with its amounts
/// blanked (they travel separately, summed).
pub fn chunk_data(chunk: &BlockAir) -> Octet {
    let statement = blanked_statement(chunk);
    hash_octets(DOMAIN_DATA_LEAF, statement.len(), &statement)
}

fn blanked_statement(chunk: &BlockAir) -> Vec<BabyBear> {
    let (_, mut tuples) = chunk.bus().expect("the block circuit has a bus");
    for v in &mut tuples[0].1[3..] {
        *v = BabyBear::ZERO; // the amounts tuple: [tag, 0, 0, a limbs, b limbs]
    }
    recursion::recursive_statement(&chunk.statement_header(), &tuples)
}

/// An internal node's data.
pub fn data_node(left: Octet, right: Octet) -> Octet {
    hash_pair(DOMAIN_DATA_NODE, left, right)
}

/// `[a limbs, b limbs]`.
fn amounts_octet((a, b): (u64, u64)) -> Octet {
    let mut o = [BabyBear::ZERO; 8];
    o[..AMOUNT_LIMBS].copy_from_slice(&amount_limbs(a));
    o[AMOUNT_LIMBS..].copy_from_slice(&amount_limbs(b));
    o
}

/// The canonical tree's root data and summed amounts over leaves given
/// as `(data, amounts)`, or `None` for no leaves (or amounts overflowing
/// 64 bits, which no circuit would accept).
pub fn tree_data(leaves: &[(Octet, (u64, u64))]) -> Option<(Octet, (u64, u64))> {
    let mut level = leaves.to_vec();
    while level.len() > 1 {
        level = level
            .chunks(2)
            .map(|pair| match pair {
                [l, r] => Some((data_node(l.0, r.0), (l.1.0.checked_add(r.1.0)?, l.1.1.checked_add(r.1.1)?))),
                [one] => Some(*one),
                _ => unreachable!(),
            })
            .collect::<Option<_>>()?;
    }
    level.pop()
}

/// A proof in a tree, with what a parent needs to verify it.
pub struct Node {
    pub air: CircuitAir,
    pub proof: Proof,
    pub data: Octet,
    pub amounts: (u64, u64),
    pub state: StateChange,
}

/// The chain state (`state_tree`) a tree proof moves between: root and
/// output count before, and after.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateChange {
    pub root_in: Octet,
    pub count_in: u64,
    pub root_out: Octet,
    pub count_out: u64,
}

impl StateChange {
    /// `[count_in, count_out, 0, ...]`. (Counts stay below 2^31, so each
    /// is one element.)
    fn counts_octet(&self) -> Octet {
        let mut o = [BabyBear::ZERO; 8];
        o[0] = BabyBear::new(self.count_in as u32);
        o[1] = BabyBear::new(self.count_out as u32);
        o
    }
}

/// What a wrap needs, beyond the chunk proof, to apply its chunk to the
/// state: for each input slot (in the statement's order), the spent
/// output's position and recovery nonce and the path to it at its turn;
/// for each output slot, the path at its turn. (Unused slots are no-ops,
/// with the path of position `count` at their turn.)
#[derive(Clone, Debug)]
pub struct ChunkTransition {
    pub change: StateChange,
    pub inputs: Vec<(u64, [u8; crate::recovery::NONCE_LEN], Vec<Octet>)>,
    pub outputs: Vec<Vec<Octet>>,
}

/// The public inputs as bus tuples (`circuit::Builder::with_public`
/// layout: address last, each read once).
fn public_tuples(vk: Octet, data: Octet, amounts: (u64, u64), state: &StateChange) -> Vec<(BabyBear, Vec<BabyBear>)> {
    [vk, data, amounts_octet(amounts), state.root_in, state.root_out, state.counts_octet()]
        .iter()
        .enumerate()
        .map(|(a, v)| {
            let mut tuple = v.to_vec();
            tuple.push(BabyBear::new(a as u32));
            (-BabyBear::ONE, tuple)
        })
        .collect()
}

/// A tree circuit's verifying key: its committed fixed columns (prover
/// side) and their digest.
#[derive(Clone)]
pub struct Key {
    pub preprocessed: Arc<Preprocessed>,
    pub vk: Octet,
}

impl Key {
    pub(crate) fn of(circuit: &Circuit, tree: &TreeParams) -> Key {
        let preprocessed = circuit.commit(&tree.params);
        let vk = vk_digest(&preprocessed.cap);
        Key { preprocessed, vk }
    }
}

/// Pad a laid-out circuit to the tree's trace length.
pub(crate) fn fit(b: Builder, tree: &TreeParams) -> Result<Circuit, Error> {
    let rows = b.rows_used();
    if rows > tree.trace_len {
        return Err(Error::TooLarge { rows, trace_len: tree.trace_len });
    }
    Ok(b.finish_padded(tree.trace_len))
}

// ---- amount gadgets ----------------------------------------------------

/// Assert `x` (a base value) is below 2^16.
fn range16(b: &mut Builder, x: EVar) {
    let mut rest = x;
    for _ in 0..16 {
        rest = b.bit_step(rest).0;
    }
    b.assert_zero(rest);
}

/// The extension cell `l0 + l1·X + l2·X^2 + l3·X^3` from four base cells:
/// half an octet.
fn compose(b: &mut Builder, limbs: &[EVar]) -> EVar {
    let mut acc = limbs[0];
    for (k, &limb) in limbs.iter().enumerate().skip(1) {
        let mut power = [BabyBear::ZERO; 4];
        power[k] = BabyBear::ONE;
        let x_k = b.const_ext(Ext(power));
        acc = b.mul_add(x_k, limb, acc);
    }
    acc
}

/// An amounts octet's eight limbs as base cells.
pub(crate) fn limbs_of(b: &mut Builder, amounts: OVar) -> Vec<EVar> {
    let (lo, hi) = b.halves(amounts);
    (0..8).map(|l| b.lane(if l < 4 { lo } else { hi }, l % 4)).collect()
}

/// `x + y` for 64-bit amounts as four 16-bit limbs (both canonical),
/// carried limb by limb; asserts it doesn't overflow 64 bits.
pub(crate) fn add_amount(b: &mut Builder, x: &[EVar], y: &[EVar]) -> Vec<EVar> {
    let mut carry = b.zero();
    let mut out = Vec::with_capacity(AMOUNT_LIMBS);
    for j in 0..AMOUNT_LIMBS {
        let partial = b.add(x[j], y[j]);
        let total = b.add(partial, carry);
        let value = b.ext_value(total).0[0].value();
        let c = b.witness_ext(Ext::from_base(BabyBear::new(value >> 16)));
        let c2 = b.mul(c, c);
        b.assert_eq(c2, c);
        let z = BabyBear::ZERO;
        let limb = b.arith(z, Some(total), Some(c), BabyBear::ONE, -BabyBear::new(1 << 16), None, z, [z; 4]);
        range16(b, limb);
        out.push(limb);
        carry = c;
    }
    b.assert_zero(carry);
    out
}

/// Pack eight limbs into an amounts octet.
fn amounts_cell(b: &mut Builder, limbs: &[EVar]) -> OVar {
    let lo = compose(b, &limbs[..4]);
    let hi = compose(b, &limbs[4..]);
    b.pack(lo, hi)
}

// ---- wrap ----------------------------------------------------------------

/// Lay out a wrap circuit for a chunk proof.
fn wrap_circuit(chunk: &BlockAir, proof: &Proof, transition: &ChunkTransition, params: &Params, tree: &TreeParams) -> Result<Circuit, Error> {
    fit(wrap_builder(chunk, proof, transition, params)?, tree)
}

/// Rows a wrap circuit uses (before padding), for measurement.
pub fn wrap_rows(chunk: &BlockAir, proof: &Proof, transition: &ChunkTransition, params: &Params) -> Result<usize, Error> {
    Ok(wrap_builder(chunk, proof, transition, params)?.rows_used())
}

fn wrap_builder(chunk: &BlockAir, proof: &Proof, transition: &ChunkTransition, params: &Params) -> Result<Builder, Error> {
    let change = &transition.change;
    let (mut b, public) = Builder::with_public(&[
        [BabyBear::ZERO; 8],
        chunk_data(chunk),
        amounts_octet(chunk.net()),
        change.root_in,
        change.root_out,
        change.counts_octet(),
    ]);
    let statement = recursion::verify(&mut b, chunk, proof, params).ok_or(Error::InvalidProof)?;
    let (ins, outs) = chunk.capacity().ok_or(Error::InvalidProof)?;
    if statement.tuples.len() != 1 + ins + outs || transition.inputs.len() != ins || transition.outputs.len() != outs {
        return Err(Error::InvalidProof);
    }
    apply_transition(&mut b, &statement, ins, outs, transition, [public[3], public[4], public[5]]);

    // The amounts tuple, first: [TAG_NET, 0, 0, a0..a3 | b0..b3, 0, 0, ...].
    let net = &statement.tuples[0];
    let (lo0, hi0) = b.halves(net[0]);
    let (lo1, hi1) = b.halves(net[1]);
    let tag = b.lane(lo0, 0);
    let expected_tag = b.const_base(BabyBear::new(crate::block_air::TAG_NET));
    b.assert_eq(tag, expected_tag);
    for l in [1, 2] {
        let lane = b.lane(lo0, l);
        b.assert_zero(lane);
    }
    let last = b.lane(lo1, 3);
    b.assert_zero(last);
    b.assert_zero(hi1);
    // The rest of the tuple (it's as long as the widest one) is zeros.
    for &octet in &net[2..] {
        let (lo, hi) = b.halves(octet);
        b.assert_zero(lo);
        b.assert_zero(hi);
    }
    let limbs: Vec<EVar> = [(lo0, 3), (hi0, 0), (hi0, 1), (hi0, 2), (hi0, 3), (lo1, 0), (lo1, 1), (lo1, 2)]
        .into_iter()
        .map(|(cell, l)| b.lane(cell, l))
        .collect();
    for &limb in &limbs {
        range16(&mut b, limb);
    }
    let amounts = amounts_cell(&mut b, &limbs);
    b.assert_eq_octet(amounts, public[2]);

    // The data: the statement with the amounts tuple's values blanked
    // (its tag, checked above, stays).
    let blank = b.const_octet(octet_of(BabyBear::new(crate::block_air::TAG_NET)));
    let zero = b.const_octet([BabyBear::ZERO; 8]);
    let octets: Vec<OVar> = statement
        .octets
        .iter()
        .map(|&o| match o {
            o if o == net[0] => blank,
            o if o == net[1] => zero,
            o => o,
        })
        .collect();
    let hash = recursion::hash_octets(&mut b, DOMAIN_DATA_LEAF, 8 * octets.len(), &octets);
    b.assert_eq_octet(hash, public[1]);
    Ok(b)
}

/// Lane `l` of an octet, as a base cell.
pub(crate) fn lane_of(b: &mut Builder, o: OVar, l: usize) -> EVar {
    let (lo, hi) = b.halves(o);
    b.lane(if l < 4 { lo } else { hi }, l % 4)
}

/// `a` where `s` is 0, `x` where `s` is 1 (octets).
fn select_octet(b: &mut Builder, s: EVar, a: OVar, x: OVar) -> OVar {
    let (al, ah) = b.halves(a);
    let (xl, xh) = b.halves(x);
    let (dl, dh) = (b.sub(xl, al), b.sub(xh, ah));
    let (l, h) = (b.mul_add(s, dl, al), b.mul_add(s, dh, ah));
    b.pack(l, h)
}

/// Eight elements of a tuple's octets, starting at element `from`, as one
/// octet.
fn tuple_octet(b: &mut Builder, cells: &[OVar], from: usize) -> OVar {
    let lanes: Vec<EVar> = (from..from + 8).map(|e| lane_of(b, cells[e / 8], e % 8)).collect();
    crate::state_circuit::pack_octets(b, &lanes)[0]
}

/// Apply a chunk's inputs and outputs, as its statement lists them, to
/// the state: `[root_in, root_out, counts]` are the public cells. Each
/// used input slot's output -- `leaf(commitment, nonce)` at its position
/// -- becomes `SPENT`; each used output slot's leaf is appended at the
/// next position. Unused slots (multiplicity 0) change nothing.
fn apply_transition(b: &mut Builder, statement: &recursion::Statement, ins: usize, outs: usize, t: &ChunkTransition, state: [OVar; 3]) {
    use crate::block_air::{TAG_PIN, TAG_POUT};
    use crate::state_circuit::{bits_of, leaf_hash, replace};
    use crate::state_tree::{DEPTH, EMPTY, SPENT};
    let [root_in, root_out, counts] = state;
    let count_in = lane_of(b, counts, 0);
    let count_out = lane_of(b, counts, 1);
    let empty = b.const_octet(EMPTY);
    let spent = b.const_octet(SPENT);
    let mut root = root_in;
    let mut count = count_in;
    for slot in 0..ins + outs {
        let (cells, header) = (&statement.tuples[1 + slot], statement.tuple_headers[1 + slot]);
        let used = lane_of(b, header, 0);
        let used_squared = b.mul(used, used);
        b.assert_eq(used_squared, used);
        let tag = lane_of(b, cells[0], 0);
        let expected = b.const_base(BabyBear::new(if slot < ins { TAG_PIN } else { TAG_POUT }));
        let off = b.sub(tag, expected);
        let gated = b.mul(used, off);
        b.assert_zero(gated);
        let commitment = tuple_octet(b, cells, 3);
        if slot < ins {
            let (position, nonce, siblings) = &t.inputs[slot];
            let nonce = b.witness_octet(crate::output::nonce_limbs(nonce));
            let leaf = leaf_hash(b, commitment, nonce);
            let old = select_octet(b, used, empty, leaf);
            let new = select_octet(b, used, empty, spent);
            let p = b.witness_ext(Ext::from_base(BabyBear::new(*position as u32)));
            let bits = bits_of(b, p, DEPTH);
            root = replace(b, root, &bits, siblings, old, new);
        } else {
            let nonce = tuple_octet(b, cells, 11);
            let leaf = leaf_hash(b, commitment, nonce);
            let new = select_octet(b, used, empty, leaf);
            let bits = bits_of(b, count, DEPTH);
            root = replace(b, root, &bits, &t.outputs[slot - ins], empty, new);
            count = b.add(count, used);
        }
    }
    b.assert_eq_octet(root, root_out);
    b.assert_eq(count, count_out);
}

/// The wrap circuit's key, for chunks shaped like `chunk` (any chunk of
/// the same `ChunkShape` gives the same circuit).
pub fn wrap_key(chunk: &BlockAir, proof: &Proof, transition: &ChunkTransition, params: &Params, tree: &TreeParams) -> Result<Key, Error> {
    Ok(Key::of(&wrap_circuit(chunk, proof, transition, params, tree)?, tree))
}

/// Prove a chunk proof verifies: a tree leaf.
pub fn wrap(
    key: &Key,
    chunk: &BlockAir,
    proof: &Proof,
    transition: &ChunkTransition,
    params: &Params,
    tree: &TreeParams,
    seed: [u8; 32],
) -> Result<Node, Error> {
    let circuit = wrap_circuit(chunk, proof, transition, params, tree)?;
    let circuit_air = circuit.air_with(key.preprocessed.clone());
    let proof = stark::prove(&circuit_air, &circuit.witness, &tree.params, seed).map_err(Error::Prove)?;
    Ok(Node {
        air: circuit_air,
        proof,
        data: chunk_data(chunk),
        amounts: chunk.net(),
        state: transition.change,
    })
}

// ---- aggregate -------------------------------------------------------------

/// Assert `x == y` where `s` is 0 and `x == z` where `s` is 1, for
/// extension cells (`x == y + s·(z - y)`).
pub(crate) fn assert_select(b: &mut Builder, x: EVar, s: EVar, y: EVar, z: EVar) {
    let diff = b.sub(z, y);
    let expected = b.mul_add(s, diff, y);
    b.assert_eq(x, expected);
}

/// Lay out an aggregation circuit over `children`; `self_vk` is the
/// value of its `vk` input, `wrap_vk` the wrap circuit's key.
fn aggregate_circuit(children: [&Node; 2], wrap_vk: Octet, self_vk: Octet, tree: &TreeParams) -> Result<Circuit, Error> {
    let data = data_node(children[0].data, children[1].data);
    let amounts = (
        children[0].amounts.0.checked_add(children[1].amounts.0).ok_or(Error::InvalidProof)?,
        children[0].amounts.1.checked_add(children[1].amounts.1).ok_or(Error::InvalidProof)?,
    );
    let [l, r] = children;
    if l.state.root_out != r.state.root_in || l.state.count_out != r.state.count_in {
        return Err(Error::InvalidProof);
    }
    let state = StateChange {
        root_in: l.state.root_in,
        count_in: l.state.count_in,
        root_out: r.state.root_out,
        count_out: r.state.count_out,
    };
    let (mut b, public) = Builder::with_public(&[self_vk, data, amounts_octet(amounts), state.root_in, state.root_out, state.counts_octet()]);
    let (self_lo, self_hi) = b.halves(public[0]);
    let wrap_vk = b.const_octet(wrap_vk);
    let (wrap_lo, wrap_hi) = b.halves(wrap_vk);
    let mut tuple_header = octet_of(-BabyBear::ONE);
    tuple_header[1] = BabyBear::new(9);
    let tuple_header = b.const_octet(tuple_header);
    let mut child_data = Vec::with_capacity(2);
    let mut child_amounts = Vec::with_capacity(2);
    let mut child_states = Vec::with_capacity(2);
    for child in children {
        let statement = recursion::verify(&mut b, &child.air, &child.proof, &tree.params).ok_or(Error::InvalidProof)?;
        // The child's public inputs: six, read once each, at addresses
        // 0..6.
        if statement.tuples.len() != 6 {
            return Err(Error::InvalidProof);
        }
        for (k, (cells, &header)) in statement.tuples.iter().zip(&statement.tuple_headers).enumerate() {
            b.assert_eq_octet(header, tuple_header);
            let address = b.const_octet(octet_of(BabyBear::new(k as u32)));
            b.assert_eq_octet(cells[1], address);
        }
        let (child_vk, data_cell, amounts_cell) = (statement.tuples[0][0], statement.tuples[1][0], statement.tuples[2][0]);
        // Its key: the wrap circuit's (s = 0) or this circuit's own (s = 1),
        // in which case it carried the same `vk` input.
        let cap = statement.preprocessed_cap.ok_or(Error::InvalidProof)?;
        let cap_octets = recursion::table_octets(&cap);
        let key = recursion::hash_octets(&mut b, DOMAIN_VK, 8 * cap_octets.len(), &cap_octets);
        let is_aggregate = vk_digest(&child.air.preprocessed_commitment().cap) == self_vk;
        let s = b.witness_ext(Ext::from_base(BabyBear::new(is_aggregate as u32)));
        let s_squared = b.mul(s, s);
        b.assert_eq(s_squared, s);
        let (key_lo, key_hi) = b.halves(key);
        assert_select(&mut b, key_lo, s, wrap_lo, self_lo);
        assert_select(&mut b, key_hi, s, wrap_hi, self_hi);
        let (vk_lo, vk_hi) = b.halves(child_vk);
        for (mine, theirs) in [(self_lo, vk_lo), (self_hi, vk_hi)] {
            let d = b.sub(theirs, mine);
            let gated = b.mul(s, d);
            b.assert_zero(gated);
        }
        child_data.push(data_cell);
        child_amounts.push(limbs_of(&mut b, amounts_cell));
        child_states.push([statement.tuples[3][0], statement.tuples[4][0], statement.tuples[5][0]]);
    }
    let mut capacity = [BabyBear::ZERO; 8];
    capacity[0] = BabyBear::new(DOMAIN_DATA_NODE);
    capacity[1] = BabyBear::new(16);
    let capacity = b.const_octet(capacity);
    let node = b.permute(child_data[0], child_data[1], capacity, None)[0];
    b.assert_eq_octet(node, public[1]);

    let (x, y) = (&child_amounts[0], &child_amounts[1]);
    let mut sum = add_amount(&mut b, &x[..4], &y[..4]);
    sum.extend(add_amount(&mut b, &x[4..], &y[4..]));
    let cell = amounts_cell(&mut b, &sum);
    b.assert_eq_octet(cell, public[2]);

    // The state: the left child's ends where the right's starts; this
    // node moves from the left's start to the right's end.
    let [[l_in, l_out, l_counts], [r_in, r_out, r_counts]] = [child_states[0], child_states[1]];
    b.assert_eq_octet(l_out, r_in);
    b.assert_eq_octet(l_in, public[3]);
    b.assert_eq_octet(r_out, public[4]);
    let lanes = |b: &mut Builder, o: OVar| -> [EVar; 2] { [lane_of(b, o, 0), lane_of(b, o, 1)] };
    let [l_count_in, l_count_out] = lanes(&mut b, l_counts);
    let [r_count_in, r_count_out] = lanes(&mut b, r_counts);
    let [count_in, count_out] = lanes(&mut b, public[5]);
    b.assert_eq(l_count_out, r_count_in);
    b.assert_eq(l_count_in, count_in);
    b.assert_eq(r_count_out, count_out);
    for k in 2..8 {
        let rest = lane_of(&mut b, public[5], k);
        b.assert_zero(rest);
    }
    fit(b, tree)
}

/// The aggregation circuit's key. Its fixed columns don't depend on the
/// children's values, so any two wrap proofs serve to lay it out.
pub fn aggregate_key(sample: [&Node; 2], wrap: &Key, tree: &TreeParams) -> Result<Key, Error> {
    let circuit = aggregate_circuit(sample, wrap.vk, [BabyBear::ZERO; 8], tree)?;
    Ok(Key::of(&circuit, tree))
}

/// Prove both children verify: a tree node.
pub fn aggregate(key: &Key, wrap: &Key, children: [&Node; 2], tree: &TreeParams, seed: [u8; 32]) -> Result<Node, Error> {
    let circuit = aggregate_circuit(children, wrap.vk, key.vk, tree)?;
    let air = circuit.air_with(key.preprocessed.clone());
    let proof = stark::prove(&air, &circuit.witness, &tree.params, seed).map_err(Error::Prove)?;
    let [l, r] = children;
    Ok(Node {
        data: data_node(l.data, r.data),
        amounts: (l.amounts.0 + r.amounts.0, l.amounts.1 + r.amounts.1),
        state: StateChange {
            root_in: l.state.root_in,
            count_in: l.state.count_in,
            root_out: r.state.root_out,
            count_out: r.state.count_out,
        },
        air,
        proof,
    })
}

/// Aggregate `leaves` into the canonical tree (`tree_data`'s shape),
/// returning the root.
pub fn aggregate_all(key: &Key, wrap: &Key, leaves: Vec<Node>, tree: &TreeParams, seed: [u8; 32]) -> Result<Node, Error> {
    let mut level = leaves;
    let mut round = 0u8;
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        let mut nodes = level.into_iter();
        while let Some(left) = nodes.next() {
            match nodes.next() {
                Some(right) => {
                    let mut s = seed;
                    s[0] ^= round;
                    s[1] ^= next.len() as u8;
                    next.push(aggregate(key, wrap, [&left, &right], tree, s)?);
                }
                None => next.push(left),
            }
        }
        level = next;
        round += 1;
    }
    level.pop().ok_or(Error::InvalidProof)
}

/// What a block verifier needs to check a tree's root: both circuits'
/// caps (a verifying key) and the tree's parameters.
pub struct VerifyingKey {
    pub wrap_cap: Vec<Hash>,
    pub aggregate_cap: Vec<Hash>,
    pub log_lde: usize,
    pub tree: TreeParams,
}

impl VerifyingKey {
    pub fn new(wrap: &Key, aggregate: &Key, tree: TreeParams) -> Self {
        VerifyingKey {
            wrap_cap: wrap.preprocessed.cap.clone(),
            aggregate_cap: aggregate.preprocessed.cap.clone(),
            log_lde: aggregate.preprocessed.log_lde,
            tree,
        }
    }

    fn circuit(&self, cap: &[Hash], public: Vec<(BabyBear, Vec<BabyBear>)>) -> CircuitAir {
        let preprocessed = Arc::new(Preprocessed::from_cap(crate::circuit::NUM_PREPROCESSED, self.log_lde, cap.to_vec()));
        CircuitAir::new(self.tree.trace_len, preprocessed, public)
    }

    /// Check `proof` proves a block whose chunks have these statements
    /// (in order) and which balances against `reward`: the tree's root,
    /// given its total amounts `(A, B)`, with `A - B == reward`. A
    /// one-chunk block's root is its wrap proof.
    ///
    /// The root also attests the block's state transition, `state`: from
    /// the parent's state root and output count to the new ones.
    pub fn verify_block(&self, chunks: &[BlockAir], amounts: (u64, u64), reward: u64, state: &StateChange, proof: &Proof) -> bool {
        if amounts.0.checked_sub(amounts.1) != Some(reward) {
            return false;
        }
        match self.root(chunks, amounts, state, proof.clone()) {
            Some(root) => stark::verify(&root.air, &root.proof, &self.tree.params),
            None => false,
        }
    }

    /// The tree root `proof` claims to be, for a block with these chunks,
    /// totals and state change: the node a chain step verifies
    /// (`chain_step`). Unchecked -- `verify_block` checks it.
    pub fn root(&self, chunks: &[BlockAir], amounts: (u64, u64), state: &StateChange, proof: Proof) -> Option<Node> {
        let leaves: Vec<(Octet, (u64, u64))> = chunks.iter().map(|c| (chunk_data(c), (0, 0))).collect();
        let (data, _) = tree_data(&leaves)?;
        let air = if chunks.len() == 1 {
            self.circuit(&self.wrap_cap, public_tuples([BabyBear::ZERO; 8], data, amounts, state))
        } else {
            self.circuit(&self.aggregate_cap, public_tuples(vk_digest(&self.aggregate_cap), data, amounts, state))
        };
        Some(Node {
            air,
            proof,
            data,
            amounts,
            state: *state,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_air::{ChunkShape, Witness};
    use crate::output::Output;
    use crate::prover::REWARD;
    use crate::stark::Air;
    use crate::transaction::Transaction;

    fn key(seed: u8, k: u8) -> (crate::wots::SecretKey, crate::wots::PublicKey) {
        crate::wots::keygen(&[seed.wrapping_mul(16).wrapping_add(k); 32])
    }

    /// State transitions for `chunks`, applied in order to a tree that
    /// already holds every chunk's inputs (with zero nonces): each chunk's
    /// witness, and the whole change.
    fn transitions(chunks: &[&BlockAir]) -> (Vec<ChunkTransition>, StateChange) {
        use crate::state_circuit::MemTree;
        use crate::state_tree::compress_leaf;
        let zero = crate::output::nonce_limbs(&[0; crate::recovery::NONCE_LEN]);
        let mut tree = MemTree::default();
        for c in chunks {
            for input in c.public_inputs() {
                tree.append(compress_leaf(input, &zero));
            }
        }
        let (root_in, count_in) = (tree.root(), tree.count());
        let mut out = Vec::new();
        for c in chunks {
            let (ins, outs) = c.capacity().unwrap();
            let (root, count) = (tree.root(), tree.count());
            let mut inputs = Vec::new();
            for slot in 0..ins {
                match c.public_inputs().get(slot) {
                    Some(input) => {
                        let leaf = compress_leaf(input, &zero);
                        let p = tree.position_of(&leaf).unwrap();
                        inputs.push((p, [0; crate::recovery::NONCE_LEN], tree.path(p)));
                        tree.spend(&leaf);
                    }
                    None => inputs.push((tree.count(), [0; crate::recovery::NONCE_LEN], tree.path(tree.count()))),
                }
            }
            let mut outputs = Vec::new();
            for slot in 0..outs {
                outputs.push(tree.path(tree.count()));
                if let (Some(o), Some(n)) = (c.public_outputs().get(slot), c.public_nonces().get(slot)) {
                    tree.append(compress_leaf(o, n));
                }
            }
            out.push(ChunkTransition {
                change: StateChange { root_in: root, count_in: count, root_out: tree.root(), count_out: tree.count() },
                inputs,
                outputs,
            });
        }
        let whole = StateChange { root_in, count_in, root_out: tree.root(), count_out: tree.count() };
        (out, whole)
    }

    /// One input of `amount` spent to `outputs`; whatever's left is fee.
    fn spend(seed: u8, amount: u64, outputs: &[u64]) -> Transaction {
        let (sk, pk) = key(seed, 1);
        let mut tx = Transaction::new();
        tx.add_input(&pk, amount).unwrap();
        for (k, &v) in outputs.iter().enumerate() {
            tx.add_output(Output::new(&key(seed, 2 + k as u8).1, v)).unwrap();
        }
        assert!(tx.sign_input(&pk, &sk));
        tx
    }

    fn reward(seed: u8, amount: u64) -> Transaction {
        let mut tx = Transaction::new();
        tx.add_output(Output::new(&key(seed, 9).1, amount)).unwrap();
        tx
    }

    /// A one-spend chunk shape: room for one spend's section.
    const SHAPE: ChunkShape = ChunkShape {
        num_blocks: 512,
        inputs: 1,
        outputs: 2,
    };

    /// A block in three chunks: the reward (claiming the fees too), a
    /// spend paying a fee of 50, and a spend paying none.
    fn chunks() -> Vec<Witness> {
        vec![
            crate::block_air::build_chunk(&[reward(1, REWARD + 50)], (REWARD + 50, 0), SHAPE).unwrap(),
            crate::block_air::build_chunk(&[spend(2, 700, &[500, 150])], (0, 50), SHAPE).unwrap(),
            crate::block_air::build_chunk(&[spend(3, 400, &[300, 100])], (0, 0), SHAPE).unwrap(),
        ]
    }

    #[test]
    fn chunks_of_one_shape_share_a_statement_layout_and_balance_with_public_amounts() {
        let chunks = chunks();
        let len = chunks[0].air.statement().len();
        assert!(chunks.iter().all(|c| c.air.statement().len() == len && c.air.trace_len() == SHAPE.num_blocks * 32));
        let challenges = {
            let mut t = crate::transcript::Transcript::new(b"chunk test");
            [t.challenge_ext(b"c"), t.challenge_ext(b"c")]
        };
        for c in &chunks {
            stark::check(&c.air, &c.trace, &challenges).unwrap();
        }
        // The fee chunk claiming a different fee doesn't balance.
        assert!(matches!(
            crate::block_air::build_chunk(&[spend(2, 700, &[500, 150])], (0, 49), SHAPE),
            Err(crate::block_air::WitnessError::Unbalanced)
        ));
        // Too much for the shape.
        assert!(crate::block_air::build_chunk(&[spend(2, 700, &[500, 100, 50])], (0, 50), SHAPE).is_err());
    }

    #[test]
    fn tree_data_pairs_neighbours_and_carries_a_lone_node() {
        let leaf = |v: u32| (octet_of(BabyBear::new(v)), (v as u64, 1));
        let (data, amounts) = tree_data(&[leaf(1), leaf(2), leaf(3)]).unwrap();
        assert_eq!(data, data_node(data_node(leaf(1).0, leaf(2).0), leaf(3).0));
        assert_eq!(amounts, (6, 3));
        assert_eq!(tree_data(&[leaf(7)]).unwrap(), leaf(7));
        assert!(tree_data(&[]).is_none());
        assert!(tree_data(&[(leaf(1).0, (u64::MAX, 0)), (leaf(2).0, (1, 0))]).is_none());
    }

    #[test]
    fn data_hashes_are_order_and_domain_sensitive() {
        let (a, b) = (octet_of(BabyBear::ONE), octet_of(BabyBear::new(2)));
        assert_ne!(data_node(a, b), data_node(b, a));
        assert_ne!(data_node(a, b), hash_pair(crate::poseidon2::DOMAIN_MERKLE_NODE + 1, a, b));
    }

    /// A chunk's data doesn't depend on its amounts (they're summed in the
    /// tree instead), but does on everything else.
    #[test]
    fn chunk_data_blanks_only_the_amounts() {
        let c = &chunks()[1];
        let same = BlockAir::chunk(
            c.air.num_blocks(),
            c.air.public_inputs().to_vec(),
            c.air.public_outputs().to_vec(),
            c.air.public_nonces().to_vec(),
            (7, 7),
            Some((SHAPE.inputs, SHAPE.outputs)),
        );
        assert_eq!(chunk_data(&c.air), chunk_data(&same));
        let other = BlockAir::chunk(
            c.air.num_blocks(),
            c.air.public_inputs().to_vec(),
            vec![c.air.public_outputs()[0]],
            vec![c.air.public_nonces()[0]],
            c.air.net(),
            Some((SHAPE.inputs, SHAPE.outputs)),
        );
        assert_ne!(chunk_data(&c.air), chunk_data(&other));
    }

    /// The amount gadgets: sums with carries, refusing overflow.
    #[test]
    fn amounts_add_with_carries_in_circuit() {
        let check = |x: (u64, u64), y: (u64, u64)| {
            let mut b = Builder::new();
            let (xs, ys) = (b.witness_octet(amounts_octet(x)), b.witness_octet(amounts_octet(y)));
            let (xl, yl) = (limbs_of(&mut b, xs), limbs_of(&mut b, ys));
            let mut sum = add_amount(&mut b, &xl[..4], &yl[..4]);
            sum.extend(add_amount(&mut b, &xl[4..], &yl[4..]));
            let cell = amounts_cell(&mut b, &sum);
            assert_eq!(b.octet_value(cell), amounts_octet((x.0 + y.0, x.1 + y.1)));
            let circuit = b.finish();
            let air = circuit.air(&Params { log_blowup: 1, num_queries: 2, grinding_bits: 0, hiding: true });
            let mut t = crate::transcript::Transcript::new(b"amounts");
            stark::check(&air, &circuit.witness, &[t.challenge_ext(b"c"), t.challenge_ext(b"c")]).unwrap();
        };
        check((0xffff, 1), (1, 0xffff_ffff));
        check((u64::MAX - 5, 0), (5, 123));
        let overflow = std::panic::catch_unwind(|| check((u64::MAX, 0), (1, 0)));
        assert!(overflow.is_err());
    }

    /// Light parameters throughout: checks the mechanism, not the
    /// security level.
    const INNER: Params = Params {
        log_blowup: 2,
        num_queries: 4,
        grinding_bits: 2,
        hiding: true,
    };

    /// A block's three chunks proven, wrapped and aggregated as
    /// ((W1, W2), W3) -- both kinds of child -- and checked against the
    /// block's statements and reward. Slow in a debug build; run with
    /// `cargo test --release -- --ignored --nocapture chunked_block`.
    #[test]
    #[ignore]
    fn chunked_block() {
        let tree = TreeParams {
            trace_len: 1 << 17,
            params: Params {
                log_blowup: 1,
                num_queries: 8,
                grinding_bits: 4,
                hiding: true,
            },
        };
        let time = std::time::Instant::now;
        let chunks = chunks();
        let start = time();
        let proofs: Vec<Proof> = chunks.iter().map(|w| stark::prove(&w.air, &w.trace, &INNER, [7; 32]).unwrap()).collect();
        println!("3 chunk proofs: {:.2?}", start.elapsed());

        let start = time();
        let (ts, state) = transitions(&chunks.iter().map(|c| &c.air).collect::<Vec<_>>());
        let wrap_key = wrap_key(&chunks[0].air, &proofs[0], &ts[0], &INNER, &tree).unwrap();
        let wraps: Vec<Node> = chunks
            .iter()
            .zip(&proofs)
            .zip(&ts)
            .map(|((w, p), t)| wrap(&wrap_key, &w.air, p, t, &INNER, &tree, [8; 32]).unwrap())
            .collect();
        println!("wrap key + 3 wraps: {:.2?}", start.elapsed());
        let start = time();
        let key = aggregate_key([&wraps[0], &wraps[1]], &wrap_key, &tree).unwrap();
        let root = aggregate_all(&key, &wrap_key, wraps, &tree, [9; 32]).unwrap();
        println!("aggregation key + 2 aggregations: {:.2?}", start.elapsed());
        assert_eq!(root.amounts, (REWARD + 50, 50));

        let vk = VerifyingKey::new(&wrap_key, &key, tree);
        let airs: Vec<BlockAir> = chunks.into_iter().map(|w| w.air).collect();
        let start = time();
        assert_eq!(root.state, state);
        assert!(vk.verify_block(&airs, root.amounts, REWARD, &state, &root.proof));
        println!("verified in {:.2?}; root proof {} KB", start.elapsed(), root.proof.to_bytes().len() / 1024);

        // Claiming more reward, other totals, chunks in another order, or
        // another state change is refused.
        assert!(!vk.verify_block(&airs, (REWARD + 51, 50), REWARD + 1, &state, &root.proof));
        assert!(!vk.verify_block(&airs, (REWARD + 60, 60), REWARD, &state, &root.proof));
        let mut other = state;
        other.count_out += 1;
        assert!(!vk.verify_block(&airs, root.amounts, REWARD, &other, &root.proof));
        let mut other = state;
        other.root_out[0] = other.root_out[0] + BabyBear::ONE;
        assert!(!vk.verify_block(&airs, root.amounts, REWARD, &other, &root.proof));
        let mut reordered = airs;
        reordered.swap(1, 2);
        assert!(!vk.verify_block(&reordered, root.amounts, REWARD, &state, &root.proof));
    }

    /// Not a correctness test: where a secure wrap proof's time goes. Run
    /// with `STARK_PROFILE=1 cargo test --release -- --ignored --nocapture
    /// profile_wrap`.
    #[test]
    #[ignore]
    fn profile_wrap() {
        let consensus = crate::prover::PARAMS;
        // HIDING=0 profiles a tree layer without zero-knowledge blinding.
        let hiding = std::env::var("HIDING").map_or(true, |v| v != "0");
        let tree = TreeParams {
            trace_len: 1 << 18,
            params: Params { hiding, ..consensus },
        };
        println!("tree parameters: {:?}", tree.params);
        let chunk = crate::block_air::build_chunk(&[spend(2, 700, &[500, 150])], (0, 50), SHAPE).unwrap();
        let proof = stark::prove(&chunk.air, &chunk.trace, &consensus, [7; 32]).unwrap();
        let start = std::time::Instant::now();
        let (ts, _) = transitions(&[&chunk.air]);
        let circuit = wrap_circuit(&chunk.air, &proof, &ts[0], &consensus, &tree).unwrap();
        println!("wrap circuit laid out: {:.2?}", start.elapsed());
        let start = std::time::Instant::now();
        let key = Key::of(&circuit, &tree);
        println!("key: {:.2?}", start.elapsed());
        eprintln!("wrap proof phases:");
        let start = std::time::Instant::now();
        let air = circuit.air_with(key.preprocessed.clone());
        stark::prove(&air, &circuit.witness, &tree.params, [8; 32]).unwrap();
        println!("wrap proof: {:.2?}", start.elapsed());
    }

    /// Not a correctness test: a two-chunk block with every layer at the
    /// consensus parameters -- what a secure tree costs. Run with
    /// `cargo test --release -- --ignored --nocapture secure_aggregation`.
    #[test]
    #[ignore]
    fn secure_aggregation() {
        let consensus = crate::prover::PARAMS;
        // HIDING=0: tree layers without blinding; TREE_LOG: their size.
        let hiding = std::env::var("HIDING").map_or(true, |v| v != "0");
        let log = std::env::var("TREE_LOG").ok().and_then(|v| v.parse().ok()).unwrap_or(18);
        let tree = TreeParams {
            trace_len: 1 << log,
            params: Params { hiding, ..consensus },
        };
        println!("tree: 2^{log} rows, {:?}", tree.params);
        let kb = |p: &Proof| p.to_bytes().len() as f64 / 1024.0;
        let time = std::time::Instant::now;
        let chunks = vec![
            crate::block_air::build_chunk(&[reward(1, REWARD + 50)], (REWARD + 50, 0), SHAPE).unwrap(),
            crate::block_air::build_chunk(&[spend(2, 700, &[500, 150])], (0, 50), SHAPE).unwrap(),
        ];
        let start = time();
        let proofs: Vec<Proof> = chunks.iter().map(|w| stark::prove(&w.air, &w.trace, &consensus, [7; 32]).unwrap()).collect();
        println!("2 chunk proofs: {:.2?} ({:.1} KB each)", start.elapsed(), kb(&proofs[0]));
        let start = time();
        let (ts, state) = transitions(&chunks.iter().map(|c| &c.air).collect::<Vec<_>>());
        let wrap_key = wrap_key(&chunks[0].air, &proofs[0], &ts[0], &consensus, &tree).unwrap();
        println!("wrap key (one-time): {:.2?}", start.elapsed());
        let mut wraps = Vec::new();
        for ((w, p), t) in chunks.iter().zip(&proofs).zip(&ts) {
            let start = time();
            wraps.push(wrap(&wrap_key, &w.air, p, t, &consensus, &tree, [8; 32]).unwrap());
            println!("wrap: {:.2?} ({:.1} KB)", start.elapsed(), kb(&wraps.last().unwrap().proof));
        }
        let start = time();
        let key = match aggregate_key([&wraps[0], &wraps[1]], &wrap_key, &tree) {
            Ok(key) => key,
            Err(e) => panic!("{e:?}"),
        };
        println!("aggregation key (one-time): {:.2?}", start.elapsed());
        let start = time();
        let root = aggregate_all(&key, &wrap_key, wraps, &tree, [9; 32]).unwrap();
        println!("aggregate: {:.2?} ({:.1} KB)", start.elapsed(), kb(&root.proof));
        let vk = VerifyingKey::new(&wrap_key, &key, tree);
        let airs: Vec<BlockAir> = chunks.into_iter().map(|w| w.air).collect();
        let start = time();
        assert!(vk.verify_block(&airs, root.amounts, REWARD, &state, &root.proof));
        println!("verify root: {:.2?}", start.elapsed());
    }
}
