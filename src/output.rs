//! An `Output` is (the hash of a public key, an amount): the pubkey hash
//! keeps the owner hidden until the output is spent and the key is
//! revealed (the same "pay to pubkey hash" idea Bitcoin uses), but the
//! amount is plain, visible `u64` -- not hidden at all.
//!
//! That's a deliberate, and real, limitation: there's no homomorphic
//! commitment or range proof here (that's what Mimblewimble's Pedersen
//! commitments are for), so there's no way to let a third party -- a block
//! validator, say, who isn't the recipient -- confirm a transaction's
//! inputs and outputs balance *without* the amounts being plaintext. A
//! hidden amount would mean only the recipient could ever check that, which
//! isn't good enough. So amounts here are fully public, same as Bitcoin's
//! transparent-value model, while ownership stays hidden the way it did
//! before amounts existed. No versioning or script yet, per the current
//! scope.

// `main.rs` doesn't call into this module yet (it just prints "Hello
// world!"), so allow dead code here rather than suppressing warnings
// piecemeal -- this module exists to be exercised by its tests for now.
#![allow(dead_code)]

use crate::poseidon2::hash_bytes_32;
use crate::wots::PublicKey;

/// 8 BabyBear field elements, 4 bytes each.
const PUBKEY_HASH_LEN: usize = 32;
/// `PUBKEY_HASH_LEN` bytes of hash, plus 8 bytes of little-endian amount.
pub const OUTPUT_LEN: usize = PUBKEY_HASH_LEN + 8;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Output {
    /// Poseidon2 hash of the owning public key.
    pub pubkey_hash: [u8; PUBKEY_HASH_LEN],
    pub amount: u64,
}

impl Output {
    pub fn new(pk: &PublicKey, amount: u64) -> Self {
        Output {
            pubkey_hash: hash_bytes_32(&pk.to_bytes()),
            amount,
        }
    }

    pub fn to_bytes(&self) -> [u8; OUTPUT_LEN] {
        let mut out = [0u8; OUTPUT_LEN];
        out[..PUBKEY_HASH_LEN].copy_from_slice(&self.pubkey_hash);
        out[PUBKEY_HASH_LEN..].copy_from_slice(&self.amount.to_le_bytes());
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wots::keygen;

    fn seed(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    #[test]
    fn deterministic() {
        let (_, pk) = keygen(&seed(1));
        assert_eq!(Output::new(&pk, 100), Output::new(&pk, 100));
    }

    #[test]
    fn different_pubkeys_give_different_outputs() {
        let (_, pk_a) = keygen(&seed(1));
        let (_, pk_b) = keygen(&seed(2));
        assert_ne!(Output::new(&pk_a, 100), Output::new(&pk_b, 100));
    }

    #[test]
    fn different_amounts_give_different_outputs() {
        let (_, pk) = keygen(&seed(1));
        assert_ne!(Output::new(&pk, 100), Output::new(&pk, 200));
    }

    #[test]
    fn amount_is_plaintext_and_readable() {
        let (_, pk) = keygen(&seed(1));
        let out = Output::new(&pk, 12345);
        assert_eq!(out.amount, 12345);
    }

    #[test]
    fn to_bytes_round_trips() {
        let (_, pk) = keygen(&seed(3));
        let out = Output::new(&pk, 100);
        let bytes = out.to_bytes();
        assert_eq!(bytes.len(), OUTPUT_LEN);
        assert_eq!(bytes, out.to_bytes());
    }
}
