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

use crate::poseidon2::{BabyBear, DOMAIN_COMMITMENT, digest_from_bytes, digest_to_bytes, hash_elements};
use crate::wots::PublicKey;

/// 8 BabyBear field elements, 4 bytes each.
const PUBKEY_HASH_LEN: usize = 32;
/// `PUBKEY_HASH_LEN` bytes of hash, plus 8 bytes of little-endian amount.
pub const OUTPUT_LEN: usize = PUBKEY_HASH_LEN + 8;

/// Bits per amount limb in a commitment -- see `Output::commitment`.
pub const AMOUNT_LIMB_BITS: u32 = 16;
/// Limbs per amount: 64 bits / 16.
pub const AMOUNT_LIMBS: usize = 4;

/// `amount` as four 16-bit limbs, least-significant first.
pub fn amount_limbs(amount: u64) -> [BabyBear; AMOUNT_LIMBS] {
    std::array::from_fn(|i| BabyBear::new(((amount >> (AMOUNT_LIMB_BITS as usize * i)) & 0xffff) as u32))
}

/// Base units per coin: amounts are integers, shown with 9 decimals (the
/// block reward is 1 coin).
pub const UNITS_PER_COIN: u64 = 1_000_000_000;

/// `amount` base units as coins: `2.500000000`.
pub fn format_amount(amount: u64) -> String {
    format!("{}.{:09}", amount / UNITS_PER_COIN, amount % UNITS_PER_COIN)
}

/// Coins (`2.5`, `2.500000000`, `3`) as base units -- exactly, with no
/// floating point; `None` for anything else, more than 9 decimals, or
/// more than a `u64` holds.
pub fn parse_amount(text: &str) -> Option<u64> {
    let text = text.trim();
    let digits = |s: &str| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit());
    let (whole, frac) = match text.split_once('.') {
        Some((whole, frac)) if digits(frac) => (whole, frac),
        Some(_) => return None,
        None => (text, ""),
    };
    if !digits(whole) || frac.len() > 9 {
        return None;
    }
    let units = format!("{frac:0<9}").parse::<u64>().ok()?;
    whole.parse::<u64>().ok()?.checked_mul(UNITS_PER_COIN)?.checked_add(units)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Output {
    /// Poseidon2 hash of the owning public key.
    pub pubkey_hash: [u8; PUBKEY_HASH_LEN],
    pub amount: u64,
}

impl Output {
    pub fn new(pk: &PublicKey, amount: u64) -> Self {
        Output {
            pubkey_hash: digest_to_bytes(pk.hash()),
            amount,
        }
    }

    /// The commitment published for this output (and, when it's spent,
    /// for the input spending it): `hash_elements` over the public-key
    /// hash's 8 elements and the amount as four 16-bit limbs,
    /// least-significant first.
    ///
    /// Limbs, rather than the amount's raw bytes, so every `u64` amount
    /// has exactly one encoding: a 32-bit half of the amount can exceed
    /// BabyBear's prime and would wrap around if taken as one element, so
    /// two different amounts could share a commitment -- spendable as the
    /// larger one. 16-bit limbs never wrap, and a circuit range-checks
    /// them directly.
    pub fn commitment(&self) -> [u8; 32] {
        let mut elements = digest_from_bytes(&self.pubkey_hash).to_vec();
        elements.extend(amount_limbs(self.amount));
        digest_to_bytes(hash_elements(DOMAIN_COMMITMENT, &elements))
    }

    pub fn to_bytes(&self) -> [u8; OUTPUT_LEN] {
        let mut out = [0u8; OUTPUT_LEN];
        out[..PUBKEY_HASH_LEN].copy_from_slice(&self.pubkey_hash);
        out[PUBKEY_HASH_LEN..].copy_from_slice(&self.amount.to_le_bytes());
        out
    }

    /// Decode from bytes, the inverse of `to_bytes`. `pubkey_hash` is
    /// opaque bytes and `amount` is a plain `u64`, so the only way this
    /// can fail is `bytes` not being exactly `OUTPUT_LEN` long --
    /// checked explicitly here (rather than taking a `[u8; OUTPUT_LEN]`
    /// and pushing that check onto every caller) so decoding a buffer of
    /// untrusted or attacker-controlled length -- a block read off the
    /// wire, say -- can never panic, only return `None`.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let bytes: [u8; OUTPUT_LEN] = bytes.try_into().ok()?;
        let mut pubkey_hash = [0u8; PUBKEY_HASH_LEN];
        pubkey_hash.copy_from_slice(&bytes[..PUBKEY_HASH_LEN]);
        let amount = u64::from_le_bytes(bytes[PUBKEY_HASH_LEN..].try_into().unwrap());
        Some(Output { pubkey_hash, amount })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn amounts_format_and_parse_exactly() {
        assert_eq!(format_amount(2_500_000_000), "2.500000000");
        assert_eq!(format_amount(1), "0.000000001");
        assert_eq!(format_amount(u64::MAX), "18446744073.709551615");
        for (text, units) in [("2.5", 2_500_000_000), ("3", 3_000_000_000), ("0.000000001", 1), ("18446744073.709551615", u64::MAX)] {
            assert_eq!(parse_amount(text), Some(units), "{text}");
            assert_eq!(parse_amount(&format_amount(units)), Some(units));
        }
        for bad in ["", ".", "1.", ".5", "1.0000000001", "-1", "1e9", "18446744073.709551616", "1,5", "abc"] {
            assert_eq!(parse_amount(bad), None, "{bad}");
        }
    }

    /// The collision the old byte encoding allowed: one 32-bit half of the
    /// amount past BabyBear's prime wrapped onto a smaller amount.
    #[test]
    fn amounts_that_used_to_collide_get_different_commitments() {
        let (_, pk) = crate::wots::keygen(&[1; 32]);
        let small = 2_147_483_648u64 - crate::poseidon2::P as u64; // 134,217,727
        let large = 2_147_483_648u64;
        assert_ne!(Output::new(&pk, small).commitment(), Output::new(&pk, large).commitment());
    }

    #[test]
    fn limbs_reassemble_to_the_amount() {
        for amount in [0, 1, 0xffff, 0x1_0000, 1_000_000_000, u64::MAX] {
            let limbs = amount_limbs(amount);
            let back = limbs
                .iter()
                .enumerate()
                .fold(0u64, |acc, (i, l)| acc | ((l.value() as u64) << (16 * i)));
            assert_eq!(back, amount);
            assert!(limbs.iter().all(|l| l.value() < 1 << 16));
        }
    }

    #[test]
    fn the_commitment_binds_both_owner_and_amount() {
        let (_, pk_a) = crate::wots::keygen(&[1; 32]);
        let (_, pk_b) = crate::wots::keygen(&[2; 32]);
        let base = Output::new(&pk_a, 50).commitment();
        assert_ne!(base, Output::new(&pk_a, 51).commitment());
        assert_ne!(base, Output::new(&pk_b, 50).commitment());
        assert_eq!(base, Output::new(&pk_a, 50).commitment());
    }
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

    #[test]
    fn from_bytes_round_trips_to_bytes() {
        let (_, pk) = keygen(&seed(4));
        let out = Output::new(&pk, 54321);
        assert_eq!(Output::from_bytes(&out.to_bytes()).unwrap(), out);
    }

    #[test]
    fn from_bytes_rejects_wrong_length() {
        let (_, pk) = keygen(&seed(5));
        let bytes = Output::new(&pk, 1).to_bytes();
        assert!(Output::from_bytes(&bytes[..bytes.len() - 1]).is_none());
        let mut too_long = bytes.to_vec();
        too_long.push(0);
        assert!(Output::from_bytes(&too_long).is_none());
    }
}
