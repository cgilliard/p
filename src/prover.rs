//! A block's zero-knowledge proof: the one thing that attests a block
//! body's commitments are properly authorized and that everything
//! balances, without revealing any of the plaintext (pubkeys, amounts,
//! signatures) behind them. See `block`'s and `chain`'s module docs for
//! why that check belongs here, permanently, rather than anywhere in
//! plaintext.
//!
//! The statement proven is `block_air`'s: for the body's public input
//! and output commitment lists, there are transactions such that every
//! input carries its owner's valid WOTS signature over its transaction,
//! every commitment is correctly formed, and `sum(inputs) + REWARD ==
//! sum(outputs)` exactly. The proof is a two-phase, zero-knowledge
//! `stark` proof of that circuit, at `PARAMS`.
//!
//! Deliberately generic over raw commitment lists (`inputs`/`outputs` as
//! `&[[u8; 32]]`), not `block::BlockBody` -- same layering discipline
//! already used by `pmmr`/`bitmap`: this module doesn't need to know
//! `BlockBody`'s specific shape, just the commitments it's attesting
//! about. It also avoids a dependency cycle: `BlockBody` holds a `Proof`
//! (see that module's docs), so `Proof` can't be defined in terms of
//! `BlockBody`.
//!
//! The miner proves every transaction in its block itself, from their
//! plaintext -- see `docs/BLOCK_TODO.md` #1.

#![allow(dead_code)]

use crate::block_air::{self, BlockAir};
use crate::poseidon2::{BabyBear, P, digest_from_bytes, hash_bytes_32};
use crate::poseidon2_air::ROWS;
use crate::stark::{self, Params};
use crate::transaction::Transaction;

/// Every block's reward: a flat 1,000,000,000 units at every height
/// (`docs/BLOCK_TODO.md` #1). A consensus constant -- the proof enforces
/// `sum(inputs) + REWARD == sum(outputs)` exactly.
pub const REWARD: u64 = 1_000_000_000;

/// The proof system's parameters -- consensus constants, since a verifier
/// must check every block at the same ones. Chosen for small proofs and
/// fast verification over prover speed (blocks are minutes apart in
/// production): blowup 16 gives 4 bits per query, so 20 queries plus 20
/// bits of grinding come to 100 bits of (conjectured) soundness.
/// Challenges themselves come from the ~124-bit extension field.
pub const PARAMS: Params = Params {
    log_blowup: 4,
    num_queries: 20,
    grinding_bits: 20,
};

/// An encoded block proof: the trace's block count (`u32`, little-endian),
/// then the `stark::Proof`. Kept as bytes -- what's published and hashed
/// into `body_hash` -- and decoded only to verify.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Proof {
    bytes: Vec<u8>,
}

/// Whether `commitment` is eight canonical field elements (each 4-byte
/// group below P). Every commitment a proof can attest to is; anything
/// else is a second byte string for the same elements, which the proof
/// can't tell apart but the UTXO set would treat as a different output.
pub fn is_canonical(commitment: &[u8; 32]) -> bool {
    commitment
        .chunks_exact(4)
        .all(|c| u32::from_le_bytes(c.try_into().unwrap()) < P)
}

fn elements(list: &[[u8; 32]]) -> Vec<[BabyBear; 8]> {
    list.iter().map(digest_from_bytes).collect()
}

impl Proof {
    pub fn from_bytes(bytes: Vec<u8>) -> Self {
        Proof { bytes }
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    /// An empty stand-in proof, for tests about everything *but* proofs
    /// (forks, retargeting, sync), whose chains skip proof checks.
    #[cfg(test)]
    pub fn placeholder() -> Self {
        Proof::default()
    }

    /// What `BlockBody::body_hash` folds in to commit to the proof.
    pub fn commitment_hash(&self) -> [u8; 32] {
        hash_bytes_32(&self.bytes)
    }

    /// Whether this proves the block statement for exactly these public
    /// commitment lists.
    pub fn verify(&self, inputs: &[[u8; 32]], outputs: &[[u8; 32]]) -> bool {
        let Some(header) = self.bytes.get(..4) else {
            return false;
        };
        let num_blocks = u32::from_le_bytes(header.try_into().unwrap()) as usize;
        let max_blocks = (1 << block_air::max_log_rows(&PARAMS)) / ROWS;
        if !num_blocks.is_power_of_two() || num_blocks < 2 || num_blocks > max_blocks {
            return false;
        }
        if !inputs.iter().chain(outputs).all(is_canonical) {
            return false;
        }
        let Some(proof) = stark::Proof::from_bytes(&self.bytes[4..]) else {
            return false;
        };
        let air = BlockAir::new(num_blocks, elements(inputs), elements(outputs), REWARD);
        stark::verify(&air, &proof, &PARAMS)
    }
}

/// Prove the block statement for `transactions` (each fully signed),
/// whose commitments must come out to exactly `inputs` and `outputs` --
/// the lists the block body will publish. `seed` must be fresh random
/// bytes for every proof: it's what keeps the proof zero-knowledge (see
/// `stark`'s docs). `None` if the transactions don't verify, don't
/// balance against `REWARD`, or don't match the lists.
pub fn prove_block(inputs: &[[u8; 32]], outputs: &[[u8; 32]], transactions: &[Transaction], seed: [u8; 32]) -> Option<Proof> {
    let witness = block_air::build(transactions, REWARD).ok()?;
    if witness.air.public_inputs() != elements(inputs) || witness.air.public_outputs() != elements(outputs) {
        return None;
    }
    let proof = stark::prove(&witness.air, &witness.trace, &PARAMS, seed).ok()?;
    let mut bytes = (witness.air.num_blocks() as u32).to_le_bytes().to_vec();
    bytes.extend(proof.to_bytes());
    Some(Proof { bytes })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block::BlockBody;
    use crate::output::Output;
    use crate::wots;

    fn reward_block() -> (Vec<[u8; 32]>, Vec<[u8; 32]>, Vec<Transaction>) {
        let (_, pk) = wots::keygen(&[1; 32]);
        let mut tx = Transaction::new();
        tx.add_output(Output::new(&pk, REWARD)).unwrap();
        let body = BlockBody::from_transactions(std::slice::from_ref(&tx)).unwrap();
        (body.inputs, body.outputs, vec![tx])
    }

    #[test]
    fn a_reward_proof_verifies_against_its_lists_and_no_others() {
        let (inputs, outputs, txs) = reward_block();
        let proof = prove_block(&inputs, &outputs, &txs, [1; 32]).unwrap();
        assert!(proof.verify(&inputs, &outputs));

        let mut other = outputs.clone();
        other[0][0] ^= 1;
        assert!(!proof.verify(&inputs, &other));
        assert!(!proof.verify(&inputs, &[]));
    }

    #[test]
    fn proving_refuses_lists_that_dont_match_the_transactions() {
        let (inputs, mut outputs, txs) = reward_block();
        outputs[0][0] ^= 1;
        assert!(prove_block(&inputs, &outputs, &txs, [1; 32]).is_none());
    }

    #[test]
    fn proving_refuses_a_block_that_overclaims_the_reward() {
        let (_, pk) = wots::keygen(&[1; 32]);
        let mut tx = Transaction::new();
        tx.add_output(Output::new(&pk, REWARD + 1)).unwrap();
        let body = BlockBody::from_transactions(std::slice::from_ref(&tx)).unwrap();
        assert!(prove_block(&body.inputs, &body.outputs, &[tx], [1; 32]).is_none());
    }

    #[test]
    fn garbage_and_placeholder_proofs_dont_verify() {
        let (inputs, outputs, _) = reward_block();
        assert!(!Proof::placeholder().verify(&inputs, &outputs));
        assert!(!Proof::from_bytes(vec![4, 0, 0, 0, 1, 2, 3]).verify(&inputs, &outputs));
        assert!(!Proof::from_bytes(vec![3, 0, 0, 0]).verify(&inputs, &outputs));
    }

    #[test]
    fn non_canonical_commitments_are_refused() {
        assert!(is_canonical(&[0u8; 32]));
        let mut bad = [0u8; 32];
        bad[..4].copy_from_slice(&P.to_le_bytes());
        assert!(!is_canonical(&bad));
    }
}
