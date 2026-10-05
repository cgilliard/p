//! Aggregation trees: many proofs combined into one, whose size and
//! verification cost don't depend on how many it covers (see
//! `docs/RECURSION.md`).
//!
//! # Shape
//!
//! Every proof in a tree is of a circuit (`circuit`) with the same trace
//! length and parameters (`TreeParams`), and the same two public inputs,
//! `[vk, data]`:
//!
//! - A **wrap** circuit (W) verifies one proof of some other AIR -- a
//!   block proof -- and sets `data` to the hash of that proof's statement
//!   (`data_leaf`). Its `vk` input is unused.
//! - An **aggregation** circuit (A) verifies two tree proofs and sets
//!   `data` to the hash of their `data` (`data_node`).
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
//! So a root proof with public inputs `[vk_A, data]` shows: there is a
//! tree of valid proofs whose leaves are proofs, valid for W's wrapped
//! AIR, of statements whose hashes combine to `data`.

#![allow(dead_code)]

use std::sync::Arc;

use crate::circuit::{Builder, Circuit, CircuitAir, EVar, Octet};
use crate::merkle::Hash;
use crate::poseidon2::{BabyBear, DOMAIN_DATA_LEAF, DOMAIN_DATA_NODE, DOMAIN_VK, digest_from_bytes, hash_octets, hash_pair};
use crate::recursion::{self, RecursiveAir};
use crate::stark::{self, Params, Preprocessed, Proof};

#[derive(Debug)]
pub enum Error {
    /// A proof to be verified in-circuit doesn't verify (or isn't of a
    /// shape the verifier circuit handles).
    InvalidProof,
    /// The circuit needs more rows than the tree's trace length.
    TooLarge { rows: usize, trace_len: usize },
    Prove(stark::Error),
}

/// Pad a laid-out circuit to the tree's trace length.
fn fit(b: Builder, tree: &TreeParams) -> Result<Circuit, Error> {
    let rows = b.rows_used();
    if rows > tree.trace_len {
        return Err(Error::TooLarge { rows, trace_len: tree.trace_len });
    }
    Ok(b.finish_padded(tree.trace_len))
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

/// A tree leaf's data: the hash of the statement its wrapped proof proves.
pub fn data_leaf(statement: &[BabyBear]) -> Octet {
    hash_octets(DOMAIN_DATA_LEAF, statement.len(), statement)
}

/// An internal node's data.
pub fn data_node(left: Octet, right: Octet) -> Octet {
    hash_pair(DOMAIN_DATA_NODE, left, right)
}

/// A proof in a tree, with what a parent needs to verify it.
pub struct Node {
    pub air: CircuitAir,
    pub proof: Proof,
    pub data: Octet,
}

/// The two public inputs as bus tuples (`circuit::Builder::with_public`
/// layout: address last, each read once).
fn public_tuples(vk: Octet, data: Octet) -> Vec<(BabyBear, Vec<BabyBear>)> {
    [vk, data]
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
pub struct Key {
    pub preprocessed: Arc<Preprocessed>,
    pub vk: Octet,
}

impl Key {
    fn of(circuit: &Circuit, tree: &TreeParams) -> Key {
        let preprocessed = circuit.commit(&tree.params);
        let vk = vk_digest(&preprocessed.cap);
        Key { preprocessed, vk }
    }
}

/// Lay out a wrap circuit for `proof` (of `air`, at `params`).
fn wrap_circuit<A: RecursiveAir>(air: &A, proof: &Proof, params: &Params, tree: &TreeParams) -> Result<Circuit, Error> {
    let statement = air.statement();
    let data = data_leaf(&statement);
    let (mut b, public) = Builder::with_public(&[[BabyBear::ZERO; 8], data]);
    let child = recursion::verify(&mut b, air, proof, params).ok_or(Error::InvalidProof)?;
    let hash = recursion::hash_octets(&mut b, DOMAIN_DATA_LEAF, statement.len(), &child.octets);
    b.assert_eq_octet(hash, public[1]);
    fit(b, tree)
}

/// The wrap circuit's key, for proofs shaped like `proof` (any proof of
/// the same AIR shape gives the same circuit).
pub fn wrap_key<A: RecursiveAir>(air: &A, proof: &Proof, params: &Params, tree: &TreeParams) -> Result<Key, Error> {
    Ok(Key::of(&wrap_circuit(air, proof, params, tree)?, tree))
}

/// Prove `proof` (of `air`, at `params`) verifies: a tree leaf.
pub fn wrap<A: RecursiveAir>(
    key: &Key,
    air: &A,
    proof: &Proof,
    params: &Params,
    tree: &TreeParams,
    seed: [u8; 32],
) -> Result<Node, Error> {
    let circuit = wrap_circuit(air, proof, params, tree)?;
    let circuit_air = circuit.air_with(key.preprocessed.clone());
    let proof = stark::prove(&circuit_air, &circuit.witness, &tree.params, seed).map_err(Error::Prove)?;
    Ok(Node {
        air: circuit_air,
        proof,
        data: data_leaf(&air.statement()),
    })
}

/// Assert `x == y` where `s` is 0 and `x == z` where `s` is 1, for
/// extension cells (`x == y + s·(z - y)`).
fn assert_select(b: &mut Builder, x: EVar, s: EVar, y: EVar, z: EVar) {
    let diff = b.sub(z, y);
    let expected = b.mul_add(s, diff, y);
    b.assert_eq(x, expected);
}

/// Lay out an aggregation circuit over `children`; `self_vk` is the
/// value of its `vk` input, `wrap_vk` the wrap circuit's key.
fn aggregate_circuit(children: [&Node; 2], wrap_vk: Octet, self_vk: Octet, tree: &TreeParams) -> Result<Circuit, Error> {
    let data = data_node(children[0].data, children[1].data);
    let (mut b, public) = Builder::with_public(&[self_vk, data]);
    let (self_lo, self_hi) = b.halves(public[0]);
    let wrap_vk = b.const_octet(wrap_vk);
    let (wrap_lo, wrap_hi) = b.halves(wrap_vk);
    let mut child_data = Vec::with_capacity(2);
    for child in children {
        let statement = recursion::verify(&mut b, &child.air, &child.proof, &tree.params).ok_or(Error::InvalidProof)?;
        // The child's public inputs, at addresses 0 and 1.
        for (k, cells) in statement.tuples.iter().enumerate() {
            let address = b.const_octet(crate::transcript::octet_of(BabyBear::new(k as u32)));
            b.assert_eq_octet(cells[1], address);
        }
        let (child_vk, child_data_cell) = (statement.tuples[0][0], statement.tuples[1][0]);
        // Its key: the wrap circuit's (s = 0) or this circuit's own (s = 1),
        // in which case it carried the same `vk` input.
        let cap = statement.preprocessed_cap.ok_or(Error::InvalidProof)?;
        let cap_octets = recursion::table_octets(&cap);
        let key = recursion::hash_octets(&mut b, DOMAIN_VK, 8 * cap_octets.len(), &cap_octets);
        let is_aggregate = vk_digest(&child.air.preprocessed_commitment().cap) == self_vk;
        let s = b.witness_ext(crate::ext::Ext::from_base(BabyBear::new(is_aggregate as u32)));
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
        child_data.push(child_data_cell);
    }
    let mut capacity = [BabyBear::ZERO; 8];
    capacity[0] = BabyBear::new(DOMAIN_DATA_NODE);
    capacity[1] = BabyBear::new(16);
    let capacity = b.const_octet(capacity);
    let node = b.permute(child_data[0], child_data[1], capacity, None)[0];
    b.assert_eq_octet(node, public[1]);
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
    Ok(Node {
        data: data_node(children[0].data, children[1].data),
        air,
        proof,
    })
}

/// Check a root proof: it's a proof of the aggregation circuit with key
/// `vk` (from its cap, all a verifier needs), with public inputs `vk`
/// and `data`.
pub fn verify_root(aggregation_cap: &[Hash], log_lde: usize, proof: &Proof, data: Octet, tree: &TreeParams) -> bool {
    let vk = vk_digest(aggregation_cap);
    let preprocessed = Arc::new(Preprocessed::from_cap(
        crate::circuit::NUM_PREPROCESSED,
        log_lde,
        aggregation_cap.to_vec(),
    ));
    let air = CircuitAir::new(tree.trace_len, preprocessed, public_tuples(vk, data));
    stark::verify(&air, proof, &tree.params)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::Air;

    fn block(seed: u8) -> crate::block_air::Witness {
        let (_, pk) = crate::wots::keygen(&[seed; 32]);
        let mut tx = crate::transaction::Transaction::new();
        tx.add_output(crate::output::Output::new(&pk, crate::prover::REWARD)).unwrap();
        crate::block_air::build(&[tx], crate::prover::REWARD).unwrap()
    }

    /// Light parameters throughout: this checks the mechanism, not the
    /// security level.
    const INNER: Params = Params {
        log_blowup: 2,
        num_queries: 4,
        grinding_bits: 2,
    };

    /// Three block proofs, wrapped, aggregated as ((W1, W2), W3): exercises
    /// both kinds of child. Slow in a debug build; run with
    /// `cargo test --release -- --ignored --nocapture aggregation_tree`.
    #[test]
    #[ignore]
    fn aggregation_tree() {
        let tree = TreeParams {
            trace_len: 1 << 17,
            params: Params {
                log_blowup: 1,
                num_queries: 8,
                grinding_bits: 4,
            },
        };
        let start = std::time::Instant::now();
        let blocks: Vec<_> = (1..=3).map(block).collect();
        let proofs: Vec<Proof> = blocks
            .iter()
            .map(|w| stark::prove(&w.air, &w.trace, &INNER, [7; 32]).unwrap())
            .collect();
        println!("block proofs: {:.2?}", start.elapsed());

        let start = std::time::Instant::now();
        let wrap_key = wrap_key(&blocks[0].air, &proofs[0], &INNER, &tree).unwrap();
        let wraps: Vec<Node> = blocks
            .iter()
            .zip(&proofs)
            .map(|(w, p)| wrap(&wrap_key, &w.air, p, &INNER, &tree, [8; 32]).unwrap())
            .collect();
        println!("wrap key + 3 wraps: {:.2?}", start.elapsed());

        let start = std::time::Instant::now();
        let key = aggregate_key([&wraps[0], &wraps[1]], &wrap_key, &tree).unwrap();
        println!("aggregation key: {:.2?}", start.elapsed());
        let start = std::time::Instant::now();
        let inner = aggregate(&key, &wrap_key, [&wraps[0], &wraps[1]], &tree, [9; 32]).unwrap();
        let root = aggregate(&key, &wrap_key, [&inner, &wraps[2]], &tree, [10; 32]).unwrap();
        println!(
            "2 aggregations: {:.2?}; root proof {} KB",
            start.elapsed(),
            root.proof.to_bytes().len() / 1024
        );

        // The root verifier needs A's cap and the blocks' statements.
        let leaves: Vec<Octet> = blocks.iter().map(|w| data_leaf(&w.air.statement())).collect();
        let data = data_node(data_node(leaves[0], leaves[1]), leaves[2]);
        let cap = key.preprocessed.cap.clone();
        let log_lde = key.preprocessed.log_lde;
        let start = std::time::Instant::now();
        assert!(verify_root(&cap, log_lde, &root.proof, data, &tree));
        println!("root verified in {:.2?}", start.elapsed());

        // Wrong data (blocks in another order), or the wrap key claimed as
        // the aggregation key, are refused.
        let swapped = data_node(data_node(leaves[1], leaves[0]), leaves[2]);
        assert!(!verify_root(&cap, log_lde, &root.proof, swapped, &tree));
        assert!(!verify_root(&wrap_key.preprocessed.cap, log_lde, &root.proof, data, &tree));
    }

    /// A block with one spend (one input, two outputs) plus the reward.
    fn spend_block(seed: u8) -> crate::block_air::Witness {
        use crate::output::Output;
        use crate::transaction::Transaction;
        let key = |k: u8| crate::wots::keygen(&[seed.wrapping_mul(16).wrapping_add(k); 32]);
        let ((sk_a, pk_a), (_, pk_b), (_, pk_c), (_, pk_m)) = (key(1), key(2), key(3), key(4));
        let mut spend = Transaction::new();
        spend.add_input(&pk_a, 700).unwrap();
        spend.add_output(Output::new(&pk_b, 500)).unwrap();
        spend.add_output(Output::new(&pk_c, 150)).unwrap();
        assert!(spend.sign_input(&pk_a, &sk_a));
        let mut reward = Transaction::new();
        reward.add_output(Output::new(&pk_m, crate::prover::REWARD + 50)).unwrap();
        crate::block_air::build(&[spend, reward], crate::prover::REWARD).unwrap()
    }

    /// Not a correctness test: the costs for one-spend blocks --
    /// (a) the block proof at the consensus parameters; (b) that proof
    /// verified in a wrap circuit proven at the consensus parameters, i.e.
    /// a published-style recursive proof; (c) two such blocks wrapped and
    /// aggregated at light tree parameters (mechanics and cost shape, not
    /// security). Run with
    /// `cargo test --release -- --ignored --nocapture one_spend_costs`.
    #[test]
    #[ignore]
    fn one_spend_costs() {
        let consensus = crate::prover::PARAMS;
        let kb = |p: &Proof| p.to_bytes().len() as f64 / 1024.0;
        let timed = |label: &str, f: &mut dyn FnMut()| {
            let start = std::time::Instant::now();
            f();
            println!("  {label}: {:.2?}", start.elapsed());
        };

        println!("(a) block proofs, consensus parameters {consensus:?}");
        let blocks: Vec<_> = (1..=2).map(spend_block).collect();
        let mut proofs = Vec::new();
        for w in &blocks {
            timed(&format!("prove ({} rows)", w.air.trace_len()), &mut || {
                proofs.push(stark::prove(&w.air, &w.trace, &consensus, [7; 32]).unwrap())
            });
        }
        timed("verify", &mut || assert!(stark::verify(&blocks[0].air, &proofs[0], &consensus)));
        println!("  size: {:.1} KB", kb(&proofs[0]));

        println!("(b) one block proof verified in a wrap circuit, proven at consensus parameters");
        let tree = TreeParams { trace_len: 1 << 17, params: consensus };
        let circuit = wrap_circuit(&blocks[0].air, &proofs[0], &consensus, &tree).unwrap();
        let mut key = None;
        timed(&format!("commit fixed columns ({} rows, one-time)", circuit.trace_len), &mut || {
            key = Some(Key::of(&circuit, &tree))
        });
        let key = key.unwrap();
        let mut node = None;
        timed("prove", &mut || {
            node = Some(wrap(&key, &blocks[0].air, &proofs[0], &consensus, &tree, [8; 32]).unwrap())
        });
        let node = node.unwrap();
        let verifier = CircuitAir::new(
            tree.trace_len,
            Arc::new(Preprocessed::from_cap(crate::circuit::NUM_PREPROCESSED, key.preprocessed.log_lde, key.preprocessed.cap.clone())),
            public_tuples([BabyBear::ZERO; 8], node.data),
        );
        timed("verify", &mut || assert!(stark::verify(&verifier, &node.proof, &consensus)));
        println!("  size: {:.1} KB", kb(&node.proof));
        drop((node, key, circuit));

        let light = TreeParams {
            trace_len: 1 << 17,
            params: Params { log_blowup: 1, num_queries: 8, grinding_bits: 4 },
        };
        println!("(c) two blocks wrapped and aggregated, light tree parameters {:?}", light.params);
        let mut wrap_key_ = None;
        timed("wrap key (one-time)", &mut || {
            wrap_key_ = Some(wrap_key(&blocks[0].air, &proofs[0], &consensus, &light).unwrap())
        });
        let wrap_key_ = wrap_key_.unwrap();
        let mut wraps = Vec::new();
        for (w, p) in blocks.iter().zip(&proofs) {
            timed("wrap", &mut || wraps.push(wrap(&wrap_key_, &w.air, p, &consensus, &light, [8; 32]).unwrap()));
        }
        let mut agg_key = None;
        timed("aggregation key (one-time)", &mut || {
            agg_key = Some(aggregate_key([&wraps[0], &wraps[1]], &wrap_key_, &light).unwrap())
        });
        let agg_key = agg_key.unwrap();
        let mut root = None;
        timed("aggregate", &mut || {
            root = Some(aggregate(&agg_key, &wrap_key_, [&wraps[0], &wraps[1]], &light, [9; 32]).unwrap())
        });
        let root = root.unwrap();
        let data = data_node(data_leaf(&blocks[0].air.statement()), data_leaf(&blocks[1].air.statement()));
        let (cap, log_lde) = (agg_key.preprocessed.cap.clone(), agg_key.preprocessed.log_lde);
        timed("verify root", &mut || assert!(verify_root(&cap, log_lde, &root.proof, data, &light)));
        println!("  root size: {:.1} KB", kb(&root.proof));
    }

    /// Not a correctness test: two one-spend blocks proven, wrapped and
    /// aggregated with every layer at the consensus parameters -- what a
    /// secure tree costs. Run with
    /// `cargo test --release -- --ignored --nocapture secure_aggregation`.
    #[test]
    #[ignore]
    fn secure_aggregation() {
        let consensus = crate::prover::PARAMS;
        let tree = TreeParams { trace_len: 1 << 18, params: consensus };
        let kb = |p: &Proof| p.to_bytes().len() as f64 / 1024.0;
        let time = std::time::Instant::now;

        let blocks: Vec<_> = (1..=2).map(spend_block).collect();
        let start = time();
        let proofs: Vec<Proof> = blocks
            .iter()
            .map(|w| stark::prove(&w.air, &w.trace, &consensus, [7; 32]).unwrap())
            .collect();
        println!("2 block proofs: {:.2?} ({:.1} KB each)", start.elapsed(), kb(&proofs[0]));

        let start = time();
        let wrap_key = wrap_key(&blocks[0].air, &proofs[0], &consensus, &tree).unwrap();
        println!("wrap key (one-time): {:.2?}", start.elapsed());
        let mut wraps = Vec::new();
        for (w, p) in blocks.iter().zip(&proofs) {
            let start = time();
            wraps.push(wrap(&wrap_key, &w.air, p, &consensus, &tree, [8; 32]).unwrap());
            println!("wrap: {:.2?} ({:.1} KB)", start.elapsed(), kb(&wraps.last().unwrap().proof));
        }
        let start = time();
        let key = match aggregate_key([&wraps[0], &wraps[1]], &wrap_key, &tree) {
            Ok(key) => key,
            Err(e) => panic!("{e:?}"),
        };
        println!("aggregation key (one-time): {:.2?}", start.elapsed());
        let start = time();
        let root = aggregate(&key, &wrap_key, [&wraps[0], &wraps[1]], &tree, [9; 32]).unwrap();
        println!("aggregate: {:.2?} ({:.1} KB)", start.elapsed(), kb(&root.proof));

        let data = data_node(data_leaf(&blocks[0].air.statement()), data_leaf(&blocks[1].air.statement()));
        let (cap, log_lde) = (key.preprocessed.cap.clone(), key.preprocessed.log_lde);
        let start = time();
        assert!(verify_root(&cap, log_lde, &root.proof, data, &tree));
        println!("verify root: {:.2?}", start.elapsed());
    }

    #[test]
    fn data_hashes_are_order_and_domain_sensitive() {
        let (a, b) = (data_leaf(&[BabyBear::ONE]), data_leaf(&[BabyBear::new(2)]));
        assert_ne!(a, b);
        assert_ne!(data_node(a, b), data_node(b, a));
        assert_ne!(data_node(a, b), hash_pair(crate::poseidon2::DOMAIN_MERKLE_NODE + 1, a, b));
    }
}
