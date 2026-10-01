//! An `Output` names a destination by the hash of its public key, not the
//! key itself -- the same "pay to pubkey hash" idea Bitcoin uses, and a
//! natural fit for a WOTS-based system: a commitment can point at an
//! `Output` without the actual (potentially large) WOTS public key ever
//! needing to appear until the output is spent/revealed.
//!
//! For now this wraps exactly one thing: `Poseidon2::hash(pubkey_bytes)`.
//! There's no versioning, script, or amount here yet -- just the pubkey
//! hash, per the current scope.

// `main.rs` doesn't call into this module yet (it just prints "Hello
// world!"), so allow dead code here rather than suppressing warnings
// piecemeal -- this module exists to be exercised by its tests for now.
#![allow(dead_code)]

use crate::poseidon2::hash_bytes_32;
use crate::wots::PublicKey;

/// 8 BabyBear field elements, 4 bytes each.
pub const OUTPUT_LEN: usize = 32;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Output([u8; OUTPUT_LEN]);

impl Output {
    /// Derive an `Output` as the Poseidon2 hash of a WOTS public key's
    /// serialized bytes (`PublicKey::to_bytes`).
    pub fn from_pubkey(pk: &PublicKey) -> Self {
        Output(hash_bytes_32(&pk.to_bytes()))
    }

    pub fn to_bytes(&self) -> [u8; OUTPUT_LEN] {
        self.0
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
        assert_eq!(
            Output::from_pubkey(&pk).to_bytes(),
            Output::from_pubkey(&pk).to_bytes()
        );
    }

    #[test]
    fn different_pubkeys_give_different_outputs() {
        let (_, pk_a) = keygen(&seed(1));
        let (_, pk_b) = keygen(&seed(2));
        assert_ne!(Output::from_pubkey(&pk_a), Output::from_pubkey(&pk_b));
    }

    #[test]
    fn to_bytes_round_trips() {
        let (_, pk) = keygen(&seed(3));
        let out = Output::from_pubkey(&pk);
        let bytes = out.to_bytes();
        assert_eq!(bytes.len(), OUTPUT_LEN);
        // to_bytes is a plain accessor, not a fresh hash -- confirm it's
        // stable across repeated calls on the same Output.
        assert_eq!(bytes, out.to_bytes());
    }
}
