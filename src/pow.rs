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
//! whatever bytes it's handed. No dependency on `block` (doesn't exist
//! yet) or anything else in this crate besides `poseidon2`.

#![allow(dead_code)]

use crate::poseidon2::hash_bytes_32;

/// `Poseidon2(header_bytes || nonce)`, with `nonce` appended as 8
/// little-endian bytes.
pub fn pow_hash(header_bytes: &[u8], nonce: u64) -> [u8; 32] {
    let mut bytes = Vec::with_capacity(header_bytes.len() + 8);
    bytes.extend_from_slice(header_bytes);
    bytes.extend_from_slice(&nonce.to_le_bytes());
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
pub fn verify(header_bytes: &[u8], nonce: u64, max_hash: &[u8; 32]) -> bool {
    meets_target(&pow_hash(header_bytes, nonce), max_hash)
}

/// Search nonces starting at 0, returning the first `(nonce, hash)` that
/// meets `max_hash`, or `None` if none of `0..max_attempts` do. A real
/// miner would keep searching indefinitely (or until outrun by a
/// competing block); the cap here exists only so callers -- tests,
/// especially -- can bound the work instead of looping forever against an
/// unreachable target.
pub fn mine(header_bytes: &[u8], max_hash: &[u8; 32], max_attempts: u64) -> Option<(u64, [u8; 32])> {
    for nonce in 0..max_attempts {
        let hash = pow_hash(header_bytes, nonce);
        if meets_target(&hash, max_hash) {
            return Some((nonce, hash));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pow_hash_differs_across_nonces() {
        assert_ne!(pow_hash(b"abc", 0), pow_hash(b"abc", 1));
    }

    #[test]
    fn pow_hash_differs_across_headers() {
        assert_ne!(pow_hash(b"abc", 0), pow_hash(b"xyz", 0));
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
        let hash = pow_hash(header, 42);
        // hash <= hash is always true, so this is valid regardless of how
        // hard the target actually is.
        assert!(verify(header, 42, &hash));
    }

    #[test]
    fn verify_rejects_hash_above_an_unreachable_target() {
        let header = b"block header bytes";
        let max_hash = [0u8; 32]; // only an exactly-zero hash would pass
        assert!(!verify(header, 0, &max_hash));
    }

    #[test]
    fn mine_finds_a_solution_under_a_trivial_target() {
        let header = b"block header";
        let max_hash = [0xffu8; 32]; // every possible hash qualifies
        let (nonce, hash) = mine(header, &max_hash, 10).expect("should find a solution");
        assert_eq!(nonce, 0);
        assert_eq!(hash, pow_hash(header, 0));
        assert!(verify(header, nonce, &max_hash));
    }

    /// `mine` must return the *smallest* nonce that satisfies the target,
    /// not just any satisfying nonce -- checked by setting the target to
    /// exactly nonce 3's hash (so 3 is guaranteed to satisfy it) and
    /// confirming the nonce returned is no larger.
    #[test]
    fn mine_returns_the_smallest_satisfying_nonce() {
        let header = b"abc";
        let target = pow_hash(header, 3);
        let (nonce, hash) = mine(header, &target, 10).expect("nonce 3 itself satisfies the target");
        assert!(nonce <= 3);
        assert_eq!(hash, pow_hash(header, nonce));
        assert!(meets_target(&hash, &target));
    }

    #[test]
    fn mine_returns_none_when_attempts_are_exhausted_under_an_impossible_target() {
        let header = b"abc";
        let max_hash = [0u8; 32];
        assert!(mine(header, &max_hash, 1000).is_none());
    }
}
