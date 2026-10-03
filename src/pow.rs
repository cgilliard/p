//! Proof of work: a cheap-to-check, expensive-to-produce puzzle a block
//! header's nonce must solve, so that producing a valid header costs real
//! computation -- the mechanism (independent of anything STARK/FRI-related
//! elsewhere in this crate) that makes it costly to spam the chain with
//! headers or rewrite history, by requiring real work per header.
//!
//! The puzzle: hash `header_bytes || nonce` with Poseidon2, and the result
//! must be no larger than a given `max_hash`, compared as a 256-bit
//! big-endian integer -- which is exactly lexicographic `[u8; 32]`
//! comparison, so no actual big-integer type is needed. A smaller
//! `max_hash` means fewer of the 2^256 possible outputs qualify, so
//! finding a satisfying nonce takes more expected attempts; this is the
//! same target-based design Bitcoin uses, just with Poseidon2 in place of
//! double-SHA256.
//!
//! `header_bytes` is opaque here -- whatever the eventual `Block`/header
//! type serializes everything-but-the-nonce into, this module just hashes
//! whatever bytes it's handed. No dependency on `block` or anything else
//! in this crate besides `poseidon2`.
//!
//! The nonce itself is a full 32 bytes, not a `u64` -- deliberately wider
//! than any attempt budget `mine` could plausibly need, so the field's
//! on-the-wire width never has to change later for a reason as mundane as
//! "ran out of nonce space." `mine`'s search loop still just increments a
//! plain `u64` counter internally and encodes it into the low 8 bytes of
//! the 32-byte field each attempt (the rest stay zero) -- nothing about
//! how mining actually works depends on the wider type.

#![allow(dead_code)]

use crate::poseidon2::hash_bytes_32;

pub type Nonce = [u8; 32];

fn nonce_from_counter(counter: u64) -> Nonce {
    let mut nonce = [0u8; 32];
    nonce[..8].copy_from_slice(&counter.to_le_bytes());
    nonce
}

/// `Poseidon2(header_bytes || nonce)`.
pub fn pow_hash(header_bytes: &[u8], nonce: Nonce) -> [u8; 32] {
    let mut bytes = Vec::with_capacity(header_bytes.len() + nonce.len());
    bytes.extend_from_slice(header_bytes);
    bytes.extend_from_slice(&nonce);
    hash_bytes_32(&bytes)
}

/// Whether `hash` satisfies the target `max_hash` -- true exactly when
/// `hash <= max_hash`, treating both as 256-bit big-endian integers.
/// `[u8; 32]`'s derived `Ord` already compares lexicographically
/// byte-by-byte from index 0, which *is* big-endian integer comparison,
/// so there's nothing to implement beyond the `<=` itself.
pub fn meets_target(hash: &[u8; 32], max_hash: &[u8; 32]) -> bool {
    hash <= max_hash
}

/// Check whether `nonce` is a valid proof of work for `header_bytes`
/// under target `max_hash`.
pub fn verify(header_bytes: &[u8], nonce: Nonce, max_hash: &[u8; 32]) -> bool {
    meets_target(&pow_hash(header_bytes, nonce), max_hash)
}

/// Search nonces starting at 0, returning the first `(nonce, hash)` that
/// meets `max_hash`, or `None` if none of the first `max_attempts` do. A
/// real miner would keep searching indefinitely (or until outrun by a
/// competing block); the cap here exists only so callers -- tests,
/// especially -- can bound the work instead of looping forever against an
/// unreachable target.
pub fn mine(header_bytes: &[u8], max_hash: &[u8; 32], max_attempts: u64) -> Option<(Nonce, [u8; 32])> {
    for counter in 0..max_attempts {
        let nonce = nonce_from_counter(counter);
        let hash = pow_hash(header_bytes, nonce);
        if meets_target(&hash, max_hash) {
            return Some((nonce, hash));
        }
    }
    None
}

/// Multiply `value`, treated as a 256-bit big-endian integer, by the
/// plain scalar `multiplier`. Returns the low 256 bits of the product
/// plus whether the true product actually needed more than that (i.e.
/// whether it overflowed) -- long multiplication, one byte at a time
/// from the least significant end, carrying in a `u128` (comfortably
/// wide enough for a `u8 * u64` partial product plus carry).
fn mul_small(value: [u8; 32], multiplier: u64) -> ([u8; 32], bool) {
    let mut out = [0u8; 32];
    let mut carry: u128 = 0;
    for i in (0..32).rev() {
        let product = value[i] as u128 * multiplier as u128 + carry;
        out[i] = (product & 0xff) as u8;
        carry = product >> 8;
    }
    (out, carry != 0)
}

/// Divide `value`, treated as a 256-bit big-endian integer, by the
/// plain scalar `divisor` (floor division). Long division, one byte at
/// a time from the most significant end, carrying the remainder
/// forward.
fn div_small(value: [u8; 32], divisor: u64) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut remainder: u128 = 0;
    for i in 0..32 {
        let dividend = (remainder << 8) | value[i] as u128;
        out[i] = (dividend / divisor as u128) as u8;
        remainder = dividend % divisor as u128;
    }
    out
}

/// Scale `target`, treated as a 256-bit big-endian integer, by
/// `numerator / denominator` -- multiply then divide, each exactly
/// (only the final division's remainder is ever lost, same as real
/// integer division), saturating to the maximum representable value
/// instead of wrapping if the intermediate product overflows 256 bits.
/// What `chain`'s difficulty retargeting uses to scale the PoW target
/// by how an actual window's elapsed time compared to how long it was
/// supposed to take -- see that module's docs.
pub fn scale(target: [u8; 32], numerator: u64, denominator: u64) -> [u8; 32] {
    let (product, overflowed) = mul_small(target, numerator);
    if overflowed {
        return [0xffu8; 32];
    }
    div_small(product, denominator)
}

/// A `max_hash` with exactly `zero_bits` leading zero bits (clamped to
/// 256) and every bit after that set to 1 -- the easiest (largest)
/// value with that many leading zero bits, so a uniformly random
/// 256-bit value meets it with probability almost exactly `2^-zero_bits`.
///
/// Generalizes the "first N bytes zero, rest 0xff" pattern used
/// elsewhere in this crate (`block::INITIAL_MAX_HASH` is exactly
/// `max_hash_with_leading_zero_bits(8)`) to arbitrary *bit*
/// granularity instead of whole bytes -- each whole byte is a 256x
/// jump in difficulty, too coarse to dial in a starting point by hand.
/// `max_hash_with_leading_zero_bits(20)`, for instance, sits precisely
/// between 16 and 24 zero bits (two and three zero bytes).
pub fn max_hash_with_leading_zero_bits(zero_bits: u32) -> [u8; 32] {
    let zero_bits = zero_bits.min(256);
    let full_zero_bytes = (zero_bits / 8) as usize;
    let remaining_bits = zero_bits % 8;

    let mut out = [0xffu8; 32];
    for byte in out.iter_mut().take(full_zero_bytes) {
        *byte = 0x00;
    }
    if full_zero_bytes < 32 && remaining_bits > 0 {
        // Zero just the top `remaining_bits` bits of the next byte,
        // leaving the rest of it set.
        out[full_zero_bytes] = 0xffu8 >> remaining_bits;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pow_hash_differs_across_nonces() {
        assert_ne!(
            pow_hash(b"abc", nonce_from_counter(0)),
            pow_hash(b"abc", nonce_from_counter(1))
        );
    }

    #[test]
    fn pow_hash_differs_across_headers() {
        assert_ne!(
            pow_hash(b"abc", nonce_from_counter(0)),
            pow_hash(b"xyz", nonce_from_counter(0))
        );
    }

    #[test]
    fn meets_target_boundary_behavior() {
        let h = [5u8; 32];

        // Equal to the target passes.
        assert!(meets_target(&h, &h));

        // Strictly larger than the target fails.
        let mut lower_target = h;
        lower_target[31] -= 1;
        assert!(!meets_target(&h, &lower_target));

        // Strictly smaller than the target passes.
        let mut higher_target = h;
        higher_target[31] += 1;
        assert!(meets_target(&h, &higher_target));
    }

    #[test]
    fn verify_accepts_a_hash_used_as_its_own_target() {
        let header = b"block header bytes";
        let nonce = nonce_from_counter(42);
        let hash = pow_hash(header, nonce);
        // hash <= hash is always true, so this is valid regardless of how
        // hard the target actually is.
        assert!(verify(header, nonce, &hash));
    }

    #[test]
    fn verify_rejects_hash_above_an_unreachable_target() {
        let header = b"block header bytes";
        let max_hash = [0u8; 32]; // only an exactly-zero hash would pass
        assert!(!verify(header, nonce_from_counter(0), &max_hash));
    }

    #[test]
    fn mine_finds_a_solution_under_a_trivial_target() {
        let header = b"block header";
        let max_hash = [0xffu8; 32]; // every possible hash qualifies
        let (nonce, hash) = mine(header, &max_hash, 10).expect("should find a solution");
        assert_eq!(nonce, nonce_from_counter(0));
        assert_eq!(hash, pow_hash(header, nonce_from_counter(0)));
        assert!(verify(header, nonce, &max_hash));
    }

    /// `mine` must return the *smallest* nonce that satisfies the target,
    /// not just any satisfying nonce -- checked by setting the target to
    /// exactly counter 3's hash (so that nonce is guaranteed to satisfy
    /// it) and confirming mining stops at or before it.
    #[test]
    fn mine_returns_the_smallest_satisfying_nonce() {
        let header = b"abc";
        let target = pow_hash(header, nonce_from_counter(3));
        let (nonce, hash) = mine(header, &target, 10).expect("counter 3 itself satisfies the target");
        assert!(u64::from_le_bytes(nonce[..8].try_into().unwrap()) <= 3);
        assert_eq!(hash, pow_hash(header, nonce));
        assert!(meets_target(&hash, &target));
    }

    #[test]
    fn mine_returns_none_when_attempts_are_exhausted_under_an_impossible_target() {
        let header = b"abc";
        let max_hash = [0u8; 32];
        assert!(mine(header, &max_hash, 1000).is_none());
    }

    #[test]
    fn nonce_from_counter_zero_pads_the_upper_bytes() {
        let nonce = nonce_from_counter(0x0102030405060708);
        assert_eq!(&nonce[..8], &0x0102030405060708u64.to_le_bytes());
        assert!(nonce[8..].iter().all(|&b| b == 0));
    }

    #[test]
    fn scale_by_one_over_one_is_identity() {
        let target = {
            let mut b = [0xffu8; 32];
            b[0] = 0x00;
            b
        };
        assert_eq!(scale(target, 1, 1), target);
    }

    /// Hand-traced: byte 0 is `0x00` so nothing carries into the
    /// multiply; dividing by 2 after multiplying by 1 is a plain right
    /// shift -- byte 1's low bit (`0xff` is odd) carries into byte 2's
    /// new high bit, and every byte after that is `0xff >> 1 | 0x80 ==
    /// 0xff` again, so the carry just propagates to the end.
    #[test]
    fn scale_by_one_over_two_matches_a_hand_traced_halving() {
        let target = {
            let mut b = [0xffu8; 32];
            b[0] = 0x00;
            b
        };
        let mut expected = [0xffu8; 32];
        expected[0] = 0x00;
        expected[1] = 0x7f;
        assert_eq!(scale(target, 1, 2), expected);
    }

    #[test]
    fn scale_by_two_over_one_matches_a_hand_traced_doubling() {
        let target = {
            let mut b = [0x00u8; 32];
            b[1] = 0x7f;
            b
        };
        let mut expected = [0x00u8; 32];
        expected[1] = 0xfe;
        assert_eq!(scale(target, 2, 1), expected);
    }

    #[test]
    fn scale_saturates_instead_of_wrapping_on_overflow() {
        let target = {
            let mut b = [0u8; 32];
            b[0] = 0x80; // top bit set -- doubling overflows past bit 255
            b
        };
        assert_eq!(scale(target, 2, 1), [0xffu8; 32]);
    }

    /// A ratio that isn't a power of two, to confirm this is genuinely
    /// doing proportional arithmetic and not secretly just a bit shift
    /// in disguise. `0xff == 255 == 5 * 51`, with no remainder, so
    /// every byte of `[0xff; 32]` divides down to exactly `0x33` (51)
    /// with nothing left over to carry between bytes.
    #[test]
    fn scale_computes_a_non_power_of_two_ratio() {
        assert_eq!(scale([0xffu8; 32], 1, 5), [0x33u8; 32]);
    }

    #[test]
    fn zero_leading_zero_bits_is_the_maximum_possible_value() {
        assert_eq!(max_hash_with_leading_zero_bits(0), [0xffu8; 32]);
    }

    #[test]
    fn whole_byte_counts_match_the_first_n_bytes_zero_pattern() {
        let mut one_byte = [0xffu8; 32];
        one_byte[0] = 0x00;
        assert_eq!(max_hash_with_leading_zero_bits(8), one_byte);

        let mut two_bytes = [0xffu8; 32];
        two_bytes[0] = 0x00;
        two_bytes[1] = 0x00;
        assert_eq!(max_hash_with_leading_zero_bits(16), two_bytes);
    }

    /// The whole point: a count that isn't a multiple of 8 lands
    /// strictly between the two whole-byte values on either side of
    /// it, instead of jumping straight from one to the other.
    #[test]
    fn partial_byte_counts_land_strictly_between_the_adjacent_whole_bytes() {
        let sixteen = max_hash_with_leading_zero_bits(16);
        let twenty = max_hash_with_leading_zero_bits(20);
        let twenty_four = max_hash_with_leading_zero_bits(24);
        assert!(twenty < sixteen);
        assert!(twenty_four < twenty);

        // Hand-traced: 16 full zero bits is bytes 0-1; the next 4 bits
        // zero out the top nibble of byte 2 (0xff >> 4 == 0x0f),
        // leaving the rest (bytes 2's low nibble, and bytes 3..31) set.
        let mut expected = [0xffu8; 32];
        expected[0] = 0x00;
        expected[1] = 0x00;
        expected[2] = 0x0f;
        assert_eq!(twenty, expected);
    }

    #[test]
    fn two_hundred_fifty_six_leading_zero_bits_is_the_minimum_possible_value() {
        assert_eq!(max_hash_with_leading_zero_bits(256), [0x00u8; 32]);
    }

    #[test]
    fn counts_above_256_clamp_rather_than_panic() {
        assert_eq!(max_hash_with_leading_zero_bits(1000), [0x00u8; 32]);
    }
}
