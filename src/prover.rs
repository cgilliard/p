//! The future ZK proof: the one thing that will attest a block body's
//! commitments are properly authorized and that everything balances,
//! without revealing any of the plaintext (pubkeys, amounts) behind
//! them. See `block`'s and `chain`'s module docs for why that check
//! belongs here, permanently, rather than anywhere in plaintext.
//!
//! **Both `Proof::verify` and `prove_block` are pure stubs right now.**
//! There's no STARK circuit yet -- encoding WOTS verification and the
//! balance equation as AIR constraints is its own large undertaking,
//! deliberately deferred until the surrounding plumbing (this module's
//! shape, and how `block`/`chain` integrate against it) is settled.
//! `verify` always reports a proof valid; `prove_block` always succeeds,
//! producing the one and only value `Proof` currently has. Neither
//! checks anything real yet.
//!
//! Deliberately generic over raw commitment lists (`inputs`/`outputs`
//! as `&[[u8; 32]]`), not `block::BlockBody` -- same layering discipline
//! already used by `pmmr`/`bitmap`: this module doesn't need to know
//! `BlockBody`'s specific shape, just the commitments it's attesting
//! about. It also avoids a dependency cycle: `BlockBody` holds a
//! `Proof` (see that module's docs), so `Proof` can't be defined in
//! terms of `BlockBody`.

#![allow(dead_code)]

use crate::poseidon2::hash_bytes_32;
use crate::transaction::Transaction;

/// A stand-in for the real succinct proof object. Carries no data at
/// all yet -- there's nothing real to carry until the actual circuit
/// exists, so every `Proof` value is currently identical.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Proof;

impl Proof {
    /// Stub: always reports valid, regardless of `inputs`/`outputs`.
    /// The real implementation will cryptographically verify this
    /// proof's claims against them.
    pub fn verify(&self, _inputs: &[[u8; 32]], _outputs: &[[u8; 32]]) -> bool {
        true
    }

    /// What `BlockBody::body_hash` folds in to commit to the proof
    /// alongside the rest of the body. A fixed value for now, since the
    /// stub carries no actual data to hash -- the real implementation
    /// will hash the real proof bytes instead.
    pub fn commitment_hash(&self) -> [u8; 32] {
        hash_bytes_32(b"prover::Proof stub")
    }
}

/// Stub: always "succeeds," producing the placeholder `Proof` with no
/// actual checking of `transactions` against `inputs`/`outputs`. The
/// real implementation will verify every transaction and the balance
/// equation (reward and fees included), returning `None` if the claim
/// doesn't actually hold -- a dishonest prover should never be able to
/// produce a proof for a false statement.
pub fn prove_block(_inputs: &[[u8; 32]], _outputs: &[[u8; 32]], _transactions: &[Transaction]) -> Option<Proof> {
    Some(Proof)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verify_stub_always_reports_valid() {
        let proof = Proof;
        assert!(proof.verify(&[], &[]));
        assert!(proof.verify(&[[1u8; 32]], &[[2u8; 32]]));
    }

    #[test]
    fn prove_block_stub_always_succeeds() {
        assert_eq!(prove_block(&[], &[], &[]), Some(Proof));
        assert_eq!(prove_block(&[[1u8; 32]], &[[2u8; 32]], &[]), Some(Proof));
    }

    #[test]
    fn commitment_hash_is_deterministic() {
        assert_eq!(Proof.commitment_hash(), Proof.commitment_hash());
    }
}
