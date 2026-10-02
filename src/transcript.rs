//! A Fiat-Shamir transcript: turns an interactive protocol (verifier sends
//! random challenges, prover responds) into a non-interactive one, by
//! deriving every "random" challenge deterministically from a running hash
//! of everything absorbed into the transcript so far. The prover can't
//! learn a challenge before committing the data it depends on, and can't
//! change that data afterward without changing every challenge downstream
//! of it -- as long as the hash behaves like a random oracle, which is the
//! standard (heuristic, not proven) assumption this transform relies on.
//!
//! Built as a simple sequential hash chain over Poseidon2, in the style of
//! a Merlin transcript: every `absorb` folds new data into the running
//! state, and every `challenge_*` derives output from the state and then
//! ratchets the state forward (by hashing the output back in) so two
//! squeezes never produce correlated output from the same state, and a
//! past squeeze can't be used to predict a future one.
//!
//! No FRI-specific (or any other protocol's) knowledge here -- this is a
//! general "absorb labeled bytes, get a pseudorandom field element or
//! bounded index" primitive. Whatever protocol uses it (FRI, eventually
//! others) is the thing that knows which bytes mean what, and picks the
//! labels that keep its own absorbs/challenges from colliding with each
//! other.

#![allow(dead_code)]

use crate::poseidon2::{BabyBear, hash_bytes_32};

pub struct Transcript {
    state: [u8; 32],
}

impl Transcript {
    /// Start a new transcript, seeded with a domain-separation label so
    /// transcripts for different protocols (or different uses within the
    /// same protocol) never collide even if they go on to absorb the same
    /// bytes afterward.
    pub fn new(label: &[u8]) -> Self {
        Transcript {
            state: hash_bytes_32(label),
        }
    }

    /// Fold `data` into the running state, tagged with `label` so the
    /// transcript can't confuse, say, "a commitment root" with "a final
    /// value" just because both happen to be 32 bytes.
    pub fn absorb(&mut self, label: &[u8], data: &[u8]) {
        let mut bytes = Vec::with_capacity(self.state.len() + label.len() + data.len());
        bytes.extend_from_slice(&self.state);
        bytes.extend_from_slice(label);
        bytes.extend_from_slice(data);
        self.state = hash_bytes_32(&bytes);
    }

    /// Derive 32 pseudorandom bytes from the current state, then ratchet
    /// the state (fold the output back in) so the next call is
    /// independent of this one.
    fn squeeze(&mut self, label: &[u8]) -> [u8; 32] {
        let mut bytes = Vec::with_capacity(self.state.len() + label.len());
        bytes.extend_from_slice(&self.state);
        bytes.extend_from_slice(label);
        let out = hash_bytes_32(&bytes);
        self.state = hash_bytes_32(&out);
        out
    }

    /// A pseudorandom field element challenge. Taking the low 4 bytes of a
    /// uniform 32-byte string and reducing mod BabyBear's prime (via
    /// `BabyBear::from_bytes`) is very slightly biased -- `2^32` isn't a
    /// multiple of `p` -- but the bias is on the order of `2^-31`,
    /// cryptographically negligible, and standard practice for this kind
    /// of challenge (unlike the query-index case below, where the bound is
    /// small enough that the same shortcut would matter).
    pub fn challenge_field(&mut self, label: &[u8]) -> BabyBear {
        let out = self.squeeze(label);
        BabyBear::from_bytes([out[0], out[1], out[2], out[3]])
    }

    /// A pseudorandom index in `0..bound`. `bound` must be a power of two
    /// (every caller in this codebase is indexing into a FRI domain, which
    /// always is one) -- then masking a uniform 32-bit value down to
    /// `log2(bound)` bits is exactly uniform, with no modulo bias and no
    /// need for rejection sampling.
    pub fn challenge_index(&mut self, label: &[u8], bound: usize) -> usize {
        assert!(
            bound.is_power_of_two(),
            "bound must be a power of two, got {bound}"
        );
        let out = self.squeeze(label);
        let candidate = u32::from_le_bytes([out[0], out[1], out[2], out[3]]);
        (candidate as usize) & (bound - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn same_history_gives_the_same_challenge() {
        let mut a = Transcript::new(b"test");
        let mut b = Transcript::new(b"test");
        a.absorb(b"x", b"hello");
        b.absorb(b"x", b"hello");
        assert_eq!(a.challenge_field(b"c"), b.challenge_field(b"c"));
    }

    #[test]
    fn different_absorbed_data_gives_different_challenges() {
        let mut a = Transcript::new(b"test");
        let mut b = Transcript::new(b"test");
        a.absorb(b"x", b"hello");
        b.absorb(b"x", b"goodbye");
        assert_ne!(a.challenge_field(b"c"), b.challenge_field(b"c"));
    }

    #[test]
    fn different_seed_labels_give_different_challenges() {
        let mut a = Transcript::new(b"protocol-a");
        let mut b = Transcript::new(b"protocol-b");
        assert_ne!(a.challenge_field(b"c"), b.challenge_field(b"c"));
    }

    #[test]
    fn different_absorb_labels_give_different_challenges() {
        let mut a = Transcript::new(b"test");
        let mut b = Transcript::new(b"test");
        a.absorb(b"label-one", b"same bytes");
        b.absorb(b"label-two", b"same bytes");
        assert_ne!(a.challenge_field(b"c"), b.challenge_field(b"c"));
    }

    #[test]
    fn successive_squeezes_differ() {
        let mut t = Transcript::new(b"test");
        let first = t.challenge_field(b"c");
        let second = t.challenge_field(b"c");
        assert_ne!(first, second);
    }

    #[test]
    fn different_challenge_labels_decorrelate_output() {
        // Same state, two different labels -- used e.g. to keep a
        // fold-challenge squeeze and a query-index squeeze from ever
        // producing related output.
        let mut a = Transcript::new(b"test");
        let mut b = Transcript::new(b"test");
        let field_challenge = a.challenge_field(b"field");
        let index_challenge = b.challenge_field(b"index");
        assert_ne!(field_challenge, index_challenge);
    }

    #[test]
    fn index_always_within_bound() {
        let mut t = Transcript::new(b"test");
        for _ in 0..200 {
            let idx = t.challenge_index(b"idx", 64);
            assert!(idx < 64);
        }
    }

    #[test]
    fn index_takes_on_more_than_one_value() {
        // A sanity check against a degenerate implementation that always
        // returns the same index -- not a rigorous uniformity test.
        let mut t = Transcript::new(b"test");
        let values: std::collections::HashSet<usize> =
            (0..50).map(|_| t.challenge_index(b"idx", 1024)).collect();
        assert!(values.len() > 1);
    }

    #[test]
    #[should_panic]
    fn challenge_index_rejects_non_power_of_two_bound() {
        let mut t = Transcript::new(b"test");
        t.challenge_index(b"idx", 100);
    }
}
