//! A Fiat-Shamir transcript: turns an interactive protocol (verifier sends
//! random challenges, prover responds) into a non-interactive one, by
//! deriving every "random" challenge deterministically from everything
//! absorbed into the transcript so far. The prover can't learn a challenge
//! before committing the data it depends on, and can't change that data
//! afterward without changing every challenge downstream of it -- as long
//! as the permutation behaves like a random one, which is the standard
//! (heuristic) assumption this transform relies on.
//!
//! # Algebraic, so a circuit can replay it
//!
//! Built as a duplex sponge directly over Poseidon2 *field elements*
//! (width 24: rate 16, capacity 8) -- the construction Plonky3's duplex
//! challenger uses -- rather than over bytes. Proofs are verified inside
//! other proofs (see `docs/RECURSION.md`), and a verifying circuit has to
//! re-run this transcript exactly: over elements that's just Poseidon2
//! permutations, while bytes would mean unpacking and repacking every value
//! in-circuit.
//!
//! Everything moves in whole **octets** (8 elements, half the rate), the
//! unit a circuit's memory cells hold, so a circuit never has to shift
//! elements between cells:
//!
//! - **Absorbing** queues octets; every two fill the rate (overwriting it)
//!   and are permuted. A label is one octet `[label, 0, ...]`; data is
//!   zero-padded to whole octets (digests are exactly one; two extension
//!   values make one).
//! - **Sampling** first permutes if anything is queued (a lone queued octet
//!   overwrites just the rate's first half) or the output is used up, then
//!   hands out the rate a half-octet (4 elements) at a time. Every
//!   challenge absorbs its label first, so it's always the first half of a
//!   fresh output.
//! - **Labels** are each one constant element derived from their bytes
//!   (`label_element`) -- a lookup natively, a free constant in a circuit.
//! - **Indices** are the low bits of a challenge's first coefficient.
//!   BabyBear's `p = 15 · 2^27 + 1`, so for bounds up to 2^27 every residue
//!   is equally likely except one, which is likelier by
//!   ~1 / (15 · 2^(27 - bits)) -- negligible, and standard practice.
//!
//! No FRI-specific (or any other protocol's) knowledge here: the protocol
//! using this decides what each absorbed value means, and picks labels
//! that keep its absorbs and challenges apart.

#![allow(dead_code)]

use crate::ext::Ext;
use crate::poseidon2::{BabyBear, P, digest_from_bytes, hash_bytes, perm24};

const RATE: usize = 16;
const WIDTH: usize = 24;

/// Marks a transcript's initial state (in the capacity), apart from every
/// other Poseidon2 use.
pub(crate) const TRANSCRIPT_DOMAIN: u32 = 0x7472;

/// A label as one field element: the first element of its hash. Distinct
/// labels collide only by hash collision.
pub fn label_element(label: &[u8]) -> BabyBear {
    hash_bytes(label)[0]
}

pub type Octet = [BabyBear; 8];

#[derive(Clone)]
pub struct Transcript {
    state: [BabyBear; WIDTH],
    /// Octets absorbed since the last permutation (at most one: two
    /// trigger a permutation).
    queued: Vec<Octet>,
    /// Half-octets of the current output handed out so far (4 = used up).
    halves_used: usize,
}

/// `[x, 0, 0, 0, 0, 0, 0, 0]`.
pub fn octet_of(x: BabyBear) -> Octet {
    let mut o = [BabyBear::ZERO; 8];
    o[0] = x;
    o
}

/// `elements` zero-padded to whole octets.
pub fn octets(elements: &[BabyBear]) -> Vec<Octet> {
    elements
        .chunks(8)
        .map(|chunk| {
            let mut o = [BabyBear::ZERO; 8];
            o[..chunk.len()].copy_from_slice(chunk);
            o
        })
        .collect()
}

impl Transcript {
    /// Start a new transcript, seeded with a domain-separation label so
    /// transcripts for different protocols never collide even if they go
    /// on to absorb the same values.
    pub fn new(label: &[u8]) -> Self {
        let mut state = [BabyBear::ZERO; WIDTH];
        state[RATE] = BabyBear::new(TRANSCRIPT_DOMAIN);
        let mut t = Transcript {
            state,
            queued: Vec::with_capacity(2),
            halves_used: 4,
        };
        t.observe(octet_of(label_element(label)));
        t
    }

    /// Overwrite the rate with the queued octets (in order) and permute.
    fn duplex(&mut self) {
        for (k, o) in self.queued.drain(..).enumerate() {
            self.state[8 * k..8 * k + 8].copy_from_slice(&o);
        }
        self.state = perm24().permute(self.state);
        self.halves_used = 0;
    }

    fn observe(&mut self, o: Octet) {
        self.queued.push(o);
        if self.queued.len() == 2 {
            self.duplex();
        } else {
            // Output from before this absorb must never be handed out.
            self.halves_used = 4;
        }
    }

    /// The next 4 output elements.
    fn sample(&mut self) -> [BabyBear; 4] {
        if !self.queued.is_empty() || self.halves_used == 4 {
            self.duplex();
        }
        let h = self.halves_used;
        self.halves_used += 1;
        self.state[4 * h..4 * h + 4].try_into().unwrap()
    }

    /// Absorb field elements under `label`.
    pub fn absorb(&mut self, label: &[u8], elements: &[BabyBear]) {
        self.observe(octet_of(label_element(label)));
        for o in octets(elements) {
            self.observe(o);
        }
    }

    /// Absorb extension elements (as their coefficients) under `label`.
    pub fn absorb_ext(&mut self, label: &[u8], values: &[Ext]) {
        let elements: Vec<BabyBear> = values.iter().flat_map(|v| v.0).collect();
        self.absorb(label, &elements);
    }

    /// Absorb digests -- a Merkle cap, say -- each as its 8 elements.
    pub fn absorb_digests(&mut self, label: &[u8], digests: &[[u8; 32]]) {
        let elements: Vec<BabyBear> = digests.iter().flat_map(digest_from_bytes).collect();
        self.absorb(label, &elements);
    }

    /// A pseudorandom field element (an extension challenge's first
    /// coefficient).
    pub fn challenge_field(&mut self, label: &[u8]) -> BabyBear {
        self.challenge_ext(label).0[0]
    }

    /// A pseudorandom extension-field element -- what every STARK and FRI
    /// challenge actually needs (see `ext`'s docs on why base-field
    /// challenges are too small).
    pub fn challenge_ext(&mut self, label: &[u8]) -> Ext {
        self.observe(octet_of(label_element(label)));
        Ext(self.sample())
    }

    /// A pseudorandom index in `0..bound`, from a sampled element's low
    /// bits. `bound` must be a power of two, at most 2^27.
    pub fn challenge_index(&mut self, label: &[u8], bound: usize) -> usize {
        assert!(
            bound.is_power_of_two() && bound <= 1 << 27,
            "bound must be a power of two up to 2^27, got {bound}"
        );
        (self.challenge_field(label).value() as usize) & (bound - 1)
    }

    /// Whether `nonce` is a valid proof of work here: absorbing it (under
    /// `label`, as one octet) and sampling gives an element whose low
    /// `bits` bits are all zero. Doesn't change this transcript. Nonces are
    /// field elements, so one at or above P is never valid.
    pub fn check_grind(&self, label: &[u8], nonce: u64, bits: u32) -> bool {
        if nonce >= P as u64 || bits > 27 {
            return false;
        }
        let mut t = self.clone();
        t.absorb(label, &[BabyBear::new(nonce as u32)]);
        let mask = (1u32 << bits) - 1;
        t.sample()[0].value() & mask == 0
    }

    /// Find a nonce passing `check_grind` -- about `2^bits` permutations,
    /// spread across every core (thread `t` tries `t`, `t + T`, ...). The
    /// smallest passing nonce found wins, so the result doesn't depend on
    /// thread timing.
    pub fn grind(&self, label: &[u8], bits: u32) -> u64 {
        use std::sync::atomic::{AtomicU64, Ordering};
        let threads = crate::parallel::threads() as u64;
        let best = AtomicU64::new(u64::MAX);
        std::thread::scope(|scope| {
            for t in 0..threads {
                let best = &best;
                scope.spawn(move || {
                    let mut nonce = t;
                    while nonce < best.load(Ordering::Relaxed) && nonce < P as u64 {
                        if self.check_grind(label, nonce, bits) {
                            best.fetch_min(nonce, Ordering::Relaxed);
                            return;
                        }
                        nonce += threads;
                    }
                });
            }
        });
        best.into_inner()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn e(v: u32) -> BabyBear {
        BabyBear::new(v)
    }

    #[test]
    fn same_history_gives_the_same_challenge() {
        let mut a = Transcript::new(b"test");
        let mut b = Transcript::new(b"test");
        a.absorb(b"data", &[e(1), e(2), e(3)]);
        b.absorb(b"data", &[e(1), e(2), e(3)]);
        assert_eq!(a.challenge_ext(b"c"), b.challenge_ext(b"c"));
    }

    #[test]
    fn different_absorbed_data_gives_different_challenges() {
        let mut a = Transcript::new(b"test");
        let mut b = Transcript::new(b"test");
        a.absorb(b"data", &[e(1)]);
        b.absorb(b"data", &[e(2)]);
        assert_ne!(a.challenge_ext(b"c"), b.challenge_ext(b"c"));
    }

    #[test]
    fn different_seed_labels_give_different_challenges() {
        let mut a = Transcript::new(b"one");
        let mut b = Transcript::new(b"two");
        assert_ne!(a.challenge_ext(b"c"), b.challenge_ext(b"c"));
    }

    #[test]
    fn different_absorb_labels_give_different_challenges() {
        let mut a = Transcript::new(b"test");
        let mut b = Transcript::new(b"test");
        a.absorb(b"x", &[e(1)]);
        b.absorb(b"y", &[e(1)]);
        assert_ne!(a.challenge_ext(b"c"), b.challenge_ext(b"c"));
    }

    /// Absorbing across a full rate's worth (and more) works, and where
    /// the boundary between two absorbs falls still matters.
    #[test]
    fn long_absorbs_are_order_and_split_sensitive() {
        let values: Vec<BabyBear> = (0..40).map(e).collect();
        let mut a = Transcript::new(b"test");
        a.absorb(b"x", &values);
        let mut b = Transcript::new(b"test");
        b.absorb(b"x", &values[..20]);
        b.absorb(b"x", &values[20..]);
        let mut c = Transcript::new(b"test");
        let mut reversed = values.clone();
        reversed.reverse();
        c.absorb(b"x", &reversed);
        let (ca, cb, cc) = (a.challenge_ext(b"c"), b.challenge_ext(b"c"), c.challenge_ext(b"c"));
        assert_ne!(ca, cb);
        assert_ne!(ca, cc);
    }

    #[test]
    fn successive_challenges_differ() {
        let mut t = Transcript::new(b"test");
        let first = t.challenge_ext(b"c");
        let second = t.challenge_ext(b"c");
        assert_ne!(first, second);
    }

    #[test]
    fn digests_and_extension_values_absorb_as_their_elements() {
        let digest = crate::poseidon2::digest_to_bytes([e(1), e(2), e(3), e(4), e(5), e(6), e(7), e(8)]);
        let mut a = Transcript::new(b"test");
        a.absorb_digests(b"d", &[digest]);
        let mut b = Transcript::new(b"test");
        b.absorb(b"d", &(1..=8).map(e).collect::<Vec<_>>());
        assert_eq!(a.challenge_field(b"c"), b.challenge_field(b"c"));

        let value = Ext([e(9), e(10), e(11), e(12)]);
        let mut a = Transcript::new(b"test");
        a.absorb_ext(b"v", &[value]);
        let mut b = Transcript::new(b"test");
        b.absorb(b"v", &value.0);
        assert_eq!(a.challenge_field(b"c"), b.challenge_field(b"c"));
    }

    #[test]
    fn index_always_within_bound_and_varies() {
        let mut t = Transcript::new(b"test");
        let mut seen = std::collections::HashSet::new();
        for _ in 0..200 {
            let i = t.challenge_index(b"i", 16);
            assert!(i < 16);
            seen.insert(i);
        }
        assert!(seen.len() > 8);
    }

    #[test]
    #[should_panic]
    fn challenge_index_rejects_non_power_of_two_bound() {
        Transcript::new(b"test").challenge_index(b"i", 10);
    }

    #[test]
    fn grinding_finds_a_nonce_that_checks_and_others_mostly_dont() {
        let t = Transcript::new(b"grind");
        let nonce = t.grind(b"pow", 8);
        assert!(t.check_grind(b"pow", nonce, 8));
        let failures = (1..=64u64).filter(|&d| !t.check_grind(b"pow", nonce + d, 8)).count();
        assert!(failures > 50);
        assert!(!t.check_grind(b"pow", P as u64 + nonce, 8));
    }
}
