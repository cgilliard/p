//! A keychain: every key a wallet will ever use, derived from one 32-byte
//! seed.
//!
//! Keys are WOTS one-time keys (`wots`), so a wallet needs a *new* key for
//! every output it receives -- payments, change, mining rewards. Rather
//! than storing them, each is derived on demand:
//!
//! ```text
//! key seed(account, index) = hash_bytes_32("tabernacle-keychain-v1" ‖ seed ‖ account ‖ index)
//! (secret key, public key) = wots::keygen(key seed)
//! ```
//!
//! so backing up the seed backs up every key. Hash-based keys have no
//! public derivation (no BIP32-style "xpub"): only the seed holder can
//! derive keys, including public ones.
//!
//! **Each key may sign only once.** The keychain derives; it doesn't track
//! which keys are used -- that's the wallet's job (hand each `KeyId` out
//! once, and never sign a second, different message with a key that has
//! already signed).
//!
//! `Keychain::random` is for real wallets (OS randomness); `Keychain::
//! from_phrase` restores one from its 24 backup words (`mnemonic`), and
//! `from_seed` from the raw seed; tests use `Keychain::test`, a fixed seed per
//! label, so each test's keys are reproducible and distinct from other
//! tests'.

#![allow(dead_code)]

use crate::output::Output;
use crate::poseidon2::hash_bytes_32;
use crate::wots::{self, PublicKey, SecretKey};

const DOMAIN: &[u8] = b"tabernacle-keychain-v1";
const VIEW_DOMAIN: &[u8] = b"tabernacle-view-v1";

/// Which key: an account (a separate sequence of keys, e.g. for different
/// purposes) and an index within it.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct KeyId {
    pub account: u32,
    pub index: u32,
}

impl KeyId {
    pub const fn new(account: u32, index: u32) -> Self {
        KeyId { account, index }
    }

    pub fn to_bytes(self) -> [u8; 8] {
        let mut out = [0u8; 8];
        out[..4].copy_from_slice(&self.account.to_le_bytes());
        out[4..].copy_from_slice(&self.index.to_le_bytes());
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let bytes: [u8; 8] = bytes.try_into().ok()?;
        Some(KeyId {
            account: u32::from_le_bytes(bytes[..4].try_into().unwrap()),
            index: u32::from_le_bytes(bytes[4..].try_into().unwrap()),
        })
    }
}

impl std::fmt::Display for KeyId {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}/{}", self.account, self.index)
    }
}

pub struct Keychain {
    seed: [u8; 32],
}

/// 32 bytes of OS randomness.
pub fn random_bytes() -> [u8; 32] {
    use std::io::Read;
    let mut out = [0u8; 32];
    std::fs::File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut out))
        .expect("failed to read /dev/urandom");
    out
}

impl Keychain {
    /// A new keychain with a fresh random seed.
    pub fn random() -> Self {
        Keychain { seed: random_bytes() }
    }

    /// The keychain for `seed` (restoring a backup).
    pub fn from_seed(seed: [u8; 32]) -> Self {
        Keychain { seed }
    }

    /// A keychain for tests: a fixed seed derived from `label`, so keys
    /// are reproducible and distinct between differently-labelled tests.
    /// Never for real funds.
    pub fn test(label: &str) -> Self {
        Keychain {
            seed: hash_bytes_32(&[b"tabernacle-test-keychain:", label.as_bytes()].concat()),
        }
    }

    /// The seed, for backup. Anyone holding it can spend everything.
    pub fn seed(&self) -> &[u8; 32] {
        &self.seed
    }

    pub fn seed_hex(&self) -> String {
        self.seed.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// The seed as 24 backup words (`mnemonic`). Anyone holding them can
    /// spend everything.
    pub fn phrase(&self) -> String {
        crate::mnemonic::to_phrase(&self.seed)
    }

    /// The view key (`recovery`): reads this wallet's outputs' recovery
    /// nonces, can't spend.
    ///
    /// ```text
    /// view_key = hash_bytes_32("tabernacle-view-v1" ‖ seed)
    /// ```
    pub fn view_key(&self) -> crate::recovery::ViewKey {
        crate::recovery::ViewKey(hash_bytes_32(&[VIEW_DOMAIN, &self.seed].concat()))
    }

    /// A keychain from its 24 backup words.
    pub fn from_phrase(phrase: &str) -> Result<Self, crate::mnemonic::Error> {
        Ok(Keychain {
            seed: crate::mnemonic::from_phrase(phrase)?,
        })
    }

    /// A keychain from a 64-character hex seed.
    pub fn from_seed_hex(hex: &str) -> Option<Self> {
        let hex = hex.trim();
        if hex.len() != 64 || !hex.is_ascii() {
            return None;
        }
        let mut seed = [0u8; 32];
        for (i, byte) in seed.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).ok()?;
        }
        Some(Keychain { seed })
    }

    fn key_seed(&self, id: KeyId) -> [u8; 32] {
        hash_bytes_32(&[DOMAIN, &self.seed, &id.to_bytes()].concat())
    }

    /// The key pair at `id`.
    pub fn derive(&self, id: KeyId) -> (SecretKey, PublicKey) {
        wots::keygen(&self.key_seed(id))
    }

    pub fn public_key(&self, id: KeyId) -> PublicKey {
        self.derive(id).1
    }

    pub fn secret_key(&self, id: KeyId) -> SecretKey {
        self.derive(id).0
    }

    /// An output paying `amount` to the key at `id`.
    pub fn output(&self, id: KeyId, amount: u64) -> Output {
        Output::new(&self.public_key(id), amount)
    }
}

impl Drop for Keychain {
    /// Best-effort: don't leave the seed lying around in freed memory.
    fn drop(&mut self) {
        for b in self.seed.iter_mut() {
            // A volatile write, so it isn't optimized away.
            unsafe { std::ptr::write_volatile(b, 0) };
        }
    }
}

impl std::fmt::Debug for Keychain {
    /// Never prints the seed.
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str("Keychain(..)")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn derivation_is_deterministic_and_keys_are_distinct() {
        let a = Keychain::test("keychain");
        let again = Keychain::from_seed(*a.seed());
        let id = KeyId::new(0, 7);
        assert_eq!(a.public_key(id), again.public_key(id));
        // Different index, account, or seed: different keys.
        assert_ne!(a.public_key(id), a.public_key(KeyId::new(0, 8)));
        assert_ne!(a.public_key(id), a.public_key(KeyId::new(1, 7)));
        assert_ne!(a.public_key(id), Keychain::test("other").public_key(id));
    }

    #[test]
    fn derived_keys_sign_and_verify() {
        let k = Keychain::test("signing");
        let (sk, pk) = k.derive(KeyId::new(0, 0));
        let message = wots::hash_message(b"hello");
        let sig = wots::sign(&sk, message).unwrap();
        assert!(wots::verify(&pk, message, &sig));
        assert!(!wots::verify(&k.public_key(KeyId::new(0, 1)), message, &sig));
    }

    #[test]
    fn seeds_round_trip_through_hex_and_never_print() {
        let k = Keychain::random();
        let restored = Keychain::from_seed_hex(&k.seed_hex()).unwrap();
        assert_eq!(restored.seed(), k.seed());
        assert!(Keychain::from_seed_hex("abc").is_none());
        assert!(Keychain::from_seed_hex(&"zz".repeat(32)).is_none());
        assert_eq!(format!("{k:?}"), "Keychain(..)");
        assert_ne!(Keychain::random().seed(), k.seed());
    }

    #[test]
    fn key_ids_round_trip() {
        let id = KeyId::new(3, 0xdead_beef);
        assert_eq!(KeyId::from_bytes(&id.to_bytes()), Some(id));
        assert_eq!(id.to_string(), "3/3735928559");
        assert!(KeyId::from_bytes(&[0; 7]).is_none());
    }

    #[test]
    fn backup_words_restore_the_same_keys() {
        let original = Keychain::random();
        let restored = Keychain::from_phrase(&original.phrase()).unwrap();
        assert_eq!(restored.seed(), original.seed());
        let id = KeyId::new(0, 7);
        assert_eq!(restored.output(id, 5).commitment(), original.output(id, 5).commitment());
        assert!(Keychain::from_phrase("abandon abandon").is_err());
    }

}
