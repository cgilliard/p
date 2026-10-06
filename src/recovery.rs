//! The 16-byte recovery nonce every output carries, so a wallet can find
//! and read back its outputs from the chain with nothing but its seed
//! (`docs/RECOVERY.md`, step 2).
//!
//! An output on chain is only `H(pubkey_hash ‖ amount)`; without the
//! amount the owner can't recognise it. So each output also carries its
//! key index and amount, encrypted to the owner's view key:
//!
//! ```text
//! plaintext (16 B) = index (u32 LE) ‖ amount (u64 LE) ‖ MAGIC
//! pad       (16 B) = hash_bytes_32(DOMAIN ‖ view_key ‖ commitment)[..16]
//! nonce            = plaintext XOR pad
//! ```
//!
//! The commitment is unique per output (fresh one-time key; consensus
//! refuses a duplicate live output), so no pad is used twice. `open`
//! recognises an output as probably ours by `MAGIC` (a stranger's output
//! matches by chance with probability 2^-32); `identify` makes it certain
//! by re-deriving the key and recomputing the commitment.

#![allow(dead_code)]

use crate::keychain::{KeyId, Keychain};
use crate::poseidon2::hash_bytes_32;

pub const NONCE_LEN: usize = 16;

const DOMAIN: &[u8] = b"tabernacle-recovery-v1";
const MAGIC: [u8; 4] = *b"TBN1";

/// A wallet's view key: finds and reads its outputs' nonces, but can't
/// spend (spending keys come from the seed by a different derivation).
/// Still a secret -- whoever holds it sees every output the wallet
/// receives, and its amount.
pub struct ViewKey(pub(crate) [u8; 32]);

impl Drop for ViewKey {
    /// Best-effort, as for `Keychain`'s seed.
    fn drop(&mut self) {
        for b in self.0.iter_mut() {
            unsafe { std::ptr::write_volatile(b, 0) };
        }
    }
}

impl std::fmt::Debug for ViewKey {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str("ViewKey(..)")
    }
}

fn pad(view_key: &ViewKey, commitment: &[u8; 32]) -> [u8; NONCE_LEN] {
    let full = hash_bytes_32(&[DOMAIN, &view_key.0, commitment].concat());
    full[..NONCE_LEN].try_into().unwrap()
}

/// The nonce for an output with this `commitment`, owned by key `index`
/// of the wallet whose view key is `view_key`.
pub fn seal(view_key: &ViewKey, commitment: &[u8; 32], index: u32, amount: u64) -> [u8; NONCE_LEN] {
    let mut nonce = [0u8; NONCE_LEN];
    nonce[..4].copy_from_slice(&index.to_le_bytes());
    nonce[4..12].copy_from_slice(&amount.to_le_bytes());
    nonce[12..].copy_from_slice(&MAGIC);
    for (n, p) in nonce.iter_mut().zip(pad(view_key, commitment)) {
        *n ^= p;
    }
    nonce
}

/// The `(index, amount)` in `nonce`, if it was sealed with `view_key` for
/// this `commitment` -- probably; `identify` confirms.
pub fn open(view_key: &ViewKey, commitment: &[u8; 32], nonce: &[u8; NONCE_LEN]) -> Option<(u32, u64)> {
    let mut plain = *nonce;
    for (n, p) in plain.iter_mut().zip(pad(view_key, commitment)) {
        *n ^= p;
    }
    if plain[12..] != MAGIC {
        return None;
    }
    Some((u32::from_le_bytes(plain[..4].try_into().unwrap()), u64::from_le_bytes(plain[4..12].try_into().unwrap())))
}

/// Whether the output `(commitment, nonce)` is `keychain`'s (in
/// `account`): its key and amount if so. Certain: the nonce must open
/// *and* the key it names, with the amount, must make this commitment.
pub fn identify(keychain: &Keychain, view_key: &ViewKey, account: u32, commitment: &[u8; 32], nonce: &[u8; NONCE_LEN]) -> Option<(KeyId, u64)> {
    let (index, amount) = open(view_key, commitment, nonce)?;
    let key = KeyId::new(account, index);
    (keychain.output(key, amount).commitment() == *commitment).then_some((key, amount))
}

/// Filler for outputs whose owner doesn't want them recoverable: random,
/// and indistinguishable on chain from a sealed nonce.
pub fn random_nonce() -> [u8; NONCE_LEN] {
    crate::keychain::random_bytes()[..NONCE_LEN].try_into().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn setup(label: &str) -> (Keychain, ViewKey) {
        let k = Keychain::test(label);
        let v = k.view_key();
        (k, v)
    }

    #[test]
    fn nonces_open_with_the_right_view_key_and_commitment_only() {
        let (alice, view) = setup("recovery alice");
        let (_, other_view) = setup("recovery bob");
        let key = KeyId::new(0, 41);
        let amount = 123_456_789_000;
        let c = alice.output(key, amount).commitment();
        let nonce = seal(&view, &c, key.index, amount);
        assert_eq!(open(&view, &c, &nonce), Some((41, amount)));
        assert_eq!(identify(&alice, &view, 0, &c, &nonce), Some((key, amount)));
        // Someone else's view key, or the nonce moved to another output.
        assert_eq!(open(&other_view, &c, &nonce), None);
        let c2 = alice.output(KeyId::new(0, 42), amount).commitment();
        assert_eq!(open(&view, &c2, &nonce), None);
        // Wrong account: opens, but the commitment doesn't match.
        assert_eq!(identify(&alice, &view, 1, &c, &nonce), None);
        // Any flipped bit breaks it (the magic, or the confirmation).
        for bit in 0..NONCE_LEN * 8 {
            let mut bad = nonce;
            bad[bit / 8] ^= 1 << (bit % 8);
            assert_eq!(identify(&alice, &view, 0, &c, &bad), None, "bit {bit}");
        }
    }

    #[test]
    fn the_same_amount_and_index_look_different_on_every_output() {
        // Nonces reveal nothing linkable: equal contents under different
        // commitments are unrelated bytes.
        let (alice, view) = setup("recovery unlinkable");
        let a = seal(&view, &alice.output(KeyId::new(0, 1), 5).commitment(), 7, 5);
        let b = seal(&view, &alice.output(KeyId::new(0, 2), 5).commitment(), 7, 5);
        assert_ne!(a, b);
        assert_ne!(a[12..], b[12..], "the magic doesn't show through");
    }

    #[test]
    fn strangers_outputs_and_random_filler_are_not_ours() {
        let (alice, view) = setup("recovery scan");
        let (bob, bob_view) = setup("recovery scan bob");
        let mut found = 0;
        for i in 0..64u32 {
            let key = KeyId::new(0, i);
            // Bob's outputs, sealed for Bob; and Alice-key outputs with
            // random filler instead of a nonce.
            let c = bob.output(key, i as u64 + 1).commitment();
            assert_eq!(identify(&alice, &view, 0, &c, &seal(&bob_view, &c, i, i as u64 + 1)), None);
            let c = alice.output(key, 9).commitment();
            assert_eq!(identify(&alice, &view, 0, &c, &random_nonce()), None);
            found += identify(&alice, &view, 0, &c, &seal(&view, &c, i, 9)).is_some() as usize;
        }
        assert_eq!(found, 64);
    }
}
