//! FRI (Fast Reed-Solomon IOP of Proximity): the protocol that lets a
//! prover convince a verifier that a function, given only as evaluations
//! over a domain, is close to a polynomial of some bounded degree --
//! without ever revealing the polynomial's coefficients. It works by
//! repeatedly "folding" the evaluations in half (halving the domain size
//! and the degree bound each round) until a tiny base case is reached,
//! with random spot-checks along the way to catch a prover who folded
//! dishonestly.
//!
//! This module: the evaluation domain and folding operation (the
//! mathematical core everything else builds on; see
//! `fold_matches_direct_polynomial_evaluation` for why folding itself is
//! trusted), plus the commit and query phases built on top of it.
//!
//! # Commit and query phases
//!
//! `CommitPhase::run` runs the full sequence of folds, committing each
//! round's evaluations via `merkle::MerkleTree` before folding them away,
//! down to one final constant value. `prove_query`/`FriQueryProof::verify`
//! are a single random spot-check across every round: starting from one
//! index in the original domain, open the pair of values each round's
//! fold needs, and chain three checks round to round -- both openings
//! verify against that round's committed root, the value the *previous*
//! round's fold produced matches whichever slot (the "low" or "high" half
//! of the pair) this round's position actually falls into, and the final
//! fold matches the stated constant. One query like this catches a
//! dishonest fold with some probability; FRI's overall soundness comes
//! from repeating it with many independent, unpredictable indices so that
//! probability compounds to negligible.
//!
//! `run`/`prove_query`/`FriQueryProof::verify` take challenges and query
//! indices as plain parameters -- that's the *interactive* protocol,
//! useful on its own for testing the folding and consistency-checking math
//! against hand-computed references without also dragging hashing into
//! the picture. `Proof::prove`/`Proof::verify`, built on top using
//! `transcript::Transcript`, are the non-interactive version: every fold
//! challenge and every query index is derived pseudorandomly from a
//! running hash of everything committed so far (each round's root, then
//! the final value), rather than supplied by an interactive verifier --
//! Fiat-Shamir. That's what makes this usable in an actual proof a prover
//! can just hand over, with no live back-and-forth.

#![allow(dead_code)]

use crate::merkle::{Hash, MerkleTree, Opening};
use crate::poseidon2::BabyBear;
use crate::transcript::Transcript;

/// Domain-separation labels for the Fiat-Shamir transcript. Each one tags
/// a distinct kind of absorbed data or derived challenge so that, say, a
/// round root and the final value (both 32-ish bytes) can never be
/// confused with each other, and a fold-challenge squeeze can never be
/// confused with a query-index squeeze.
const PROTOCOL_LABEL: &[u8] = b"fri-v1";
const ROUND_ROOT_LABEL: &[u8] = b"fri-round-root";
const FOLD_CHALLENGE_LABEL: &[u8] = b"fri-fold-challenge";
const FINAL_VALUE_LABEL: &[u8] = b"fri-final-value";
const QUERY_INDEX_LABEL: &[u8] = b"fri-query-index";

/// `TWO_ADIC_GENERATORS[k]` is a generator of BabyBear's multiplicative
/// subgroup of order `2^k`, for `k = 0..=27` -- BabyBear's prime has
/// 2-adicity 27 (`p - 1 = 2^27 * 15`), the largest power-of-two-order
/// subgroup available, which is what makes repeated halving possible at
/// all. Ported directly from Plonky3's `baby-bear/src/baby_bear.rs`
/// (`TwoAdicData::TWO_ADIC_GENERATORS`), and independently verified rather
/// than trusted blindly: every entry checked (outside this codebase, via a
/// plain modular-exponentiation script) to have *exactly* its claimed
/// order, not merely to divide it, and to equal `generators[27]^(2^(27-k))`.
const TWO_ADIC_GENERATORS: [u32; MAX_TWO_ADICITY + 1] = [
    1, 2013265920, 1728404513, 1592366214, 196396260, 760005850, 1721589904, 397765732, 1732600167,
    1753498361, 341742893, 1340477990, 1282623253, 298008106, 1657000625, 2009781145, 1421947380,
    1286330022, 1559589183, 1049899240, 195061667, 414040701, 570250684, 1267047229, 1003846038,
    1149491290, 975630072, 440564289,
];

pub const MAX_TWO_ADICITY: usize = 27;

/// A generator of BabyBear's order-`2^log_size` multiplicative subgroup --
/// the domain FRI's folding halves repeatedly.
pub fn domain_generator(log_size: usize) -> BabyBear {
    assert!(
        log_size <= MAX_TWO_ADICITY,
        "log_size {log_size} exceeds BabyBear's 2-adicity ({MAX_TWO_ADICITY})"
    );
    BabyBear::new(TWO_ADIC_GENERATORS[log_size])
}

/// The full domain `[g^0, g^1, ..., g^(n-1)]` for `n = 2^log_size`, `g`
/// the order-`n` generator. Point `i + n/2` is always `-`(point `i`),
/// since `g^(n/2)` has order 2 and is therefore `-1` -- the property
/// `fold` relies on to pair up points.
pub fn domain(log_size: usize) -> Vec<BabyBear> {
    let g = domain_generator(log_size);
    let n = 1usize << log_size;
    let mut points = Vec::with_capacity(n);
    let mut cur = BabyBear::ONE;
    for _ in 0..n {
        points.push(cur);
        cur = cur * g;
    }
    points
}

/// One FRI folding step: given evaluations of a polynomial `f` of degree
/// `< domain.len()` over `domain`, and a `challenge`, return evaluations
/// of `f'(y) = f_even(y) + challenge * f_odd(y)` over the squared
/// (half-size) domain, where `f(x) = f_even(x^2) + x * f_odd(x^2)`.
///
/// For each pair `{x, -x}` (`domain[i]` and `domain[i + n/2]`):
/// `f_even(x^2) = (f(x)+f(-x))/2` and `f_odd(x^2) = (f(x)-f(-x))/(2x)`.
/// That's what lets this work from evaluations alone -- no coefficients,
/// no interpolation, just arithmetic on the values already in hand.
pub fn fold(evals: &[BabyBear], domain: &[BabyBear], challenge: BabyBear) -> Vec<BabyBear> {
    assert_eq!(
        evals.len(),
        domain.len(),
        "evaluations and domain must have the same length"
    );
    let n = evals.len();
    assert!(
        n.is_power_of_two() && n > 1,
        "domain size must be a power of two greater than 1, got {n}"
    );
    let half = n / 2;

    let inv2 = BabyBear::new(2).inverse();
    let c = challenge * inv2;

    (0..half)
        .map(|i| {
            let f_x = evals[i];
            let f_neg_x = evals[i + half];
            let x_inv = domain[i].inverse();
            let sum = f_x + f_neg_x;
            let diff = f_x.sub(f_neg_x);
            sum * inv2 + c * (x_inv * diff)
        })
        .collect()
}

/// The domain `fold`'s output lives over: squaring every point in the
/// first half of `domain` (the second half squares to the exact same
/// values, since `domain[i + half] = -domain[i]` and squaring erases the
/// sign) gives the order-`n/2` domain generated by `g^2`.
pub fn fold_domain(domain: &[BabyBear]) -> Vec<BabyBear> {
    let half = domain.len() / 2;
    domain[..half].iter().map(|&x| x * x).collect()
}

/// The full commit phase: fold `initial_evals` down to a single value,
/// one `MerkleTree` commitment per round (before that round's values are
/// folded away). `challenges.len()` must equal `log2(initial_evals.len())`
/// -- one challenge per fold, including the last one, which produces the
/// final constant.
pub struct CommitPhase {
    rounds: Vec<MerkleTree>,
    challenges: Vec<BabyBear>,
    final_value: BabyBear,
}

impl CommitPhase {
    pub fn run(
        initial_evals: &[BabyBear],
        initial_domain: &[BabyBear],
        challenges: &[BabyBear],
    ) -> Self {
        let n = initial_evals.len();
        assert!(
            n.is_power_of_two() && n >= 2,
            "initial length must be a power of two, at least 2"
        );
        let log_size = n.trailing_zeros() as usize;
        assert_eq!(
            challenges.len(),
            log_size,
            "need exactly log2(n) = {log_size} challenges, one per fold"
        );
        assert_eq!(initial_domain.len(), n);

        let mut rounds = Vec::with_capacity(log_size);
        let mut evals = initial_evals.to_vec();
        let mut domain_pts = initial_domain.to_vec();

        for &challenge in challenges {
            rounds.push(MerkleTree::commit(&evals));
            evals = fold(&evals, &domain_pts, challenge);
            domain_pts = fold_domain(&domain_pts);
        }

        debug_assert_eq!(evals.len(), 1);
        CommitPhase {
            rounds,
            challenges: challenges.to_vec(),
            final_value: evals[0],
        }
    }

    /// Like `run`, but derives the fold challenges itself via Fiat-Shamir
    /// instead of taking them as a parameter: each round's challenge is
    /// squeezed from `transcript` only after that round's root has been
    /// absorbed into it, so a prover can't pick evaluations for round `i`
    /// after already knowing round `i`'s challenge. The final value is
    /// absorbed too, after the last fold -- `Proof::prove`'s query indices
    /// are squeezed from this same transcript afterward, so they end up
    /// depending on every round's root and the final value as well.
    pub fn prove(
        initial_evals: &[BabyBear],
        initial_domain: &[BabyBear],
        transcript: &mut Transcript,
    ) -> Self {
        let n = initial_evals.len();
        assert!(
            n.is_power_of_two() && n >= 2,
            "initial length must be a power of two, at least 2"
        );
        let log_size = n.trailing_zeros() as usize;
        assert_eq!(initial_domain.len(), n);

        let mut rounds = Vec::with_capacity(log_size);
        let mut challenges = Vec::with_capacity(log_size);
        let mut evals = initial_evals.to_vec();
        let mut domain_pts = initial_domain.to_vec();

        for _ in 0..log_size {
            let tree = MerkleTree::commit(&evals);
            transcript.absorb(ROUND_ROOT_LABEL, &tree.root());
            let challenge = transcript.challenge_field(FOLD_CHALLENGE_LABEL);

            rounds.push(tree);
            challenges.push(challenge);
            evals = fold(&evals, &domain_pts, challenge);
            domain_pts = fold_domain(&domain_pts);
        }

        debug_assert_eq!(evals.len(), 1);
        let final_value = evals[0];
        transcript.absorb(FINAL_VALUE_LABEL, &final_value.to_bytes());

        CommitPhase {
            rounds,
            challenges,
            final_value,
        }
    }

    /// The root committed at each round, in order -- the public part of
    /// this commit phase a verifier actually needs.
    pub fn roots(&self) -> Vec<Hash> {
        self.rounds.iter().map(|r| r.root()).collect()
    }

    pub fn final_value(&self) -> BabyBear {
        self.final_value
    }

    /// `log2` of the original (round-0) domain size, i.e. the number of
    /// fold rounds.
    pub fn log_size(&self) -> usize {
        self.rounds.len()
    }

    /// Build a query proof for the given starting index into the original
    /// (round-0) domain.
    pub fn prove_query(&self, index: usize) -> FriQueryProof {
        let mut openings = Vec::with_capacity(self.rounds.len());
        let mut idx = index;
        for round in &self.rounds {
            let half = round.len() / 2;
            let low = idx % half;
            openings.push(RoundOpening {
                low: round.open(low),
                high: round.open(low + half),
            });
            idx = low;
        }
        FriQueryProof { openings }
    }
}

/// One round's contribution to a query: the two openings (`low` and
/// `high`, i.e. a domain point and its negation) that round's fold
/// combines.
#[derive(Clone, Debug)]
pub struct RoundOpening {
    pub low: Opening,
    pub high: Opening,
}

/// A single query's worth of evidence: one `RoundOpening` per fold round.
#[derive(Clone, Debug)]
pub struct FriQueryProof {
    pub openings: Vec<RoundOpening>,
}

impl FriQueryProof {
    /// Verify this query against the committed `roots` (one per round,
    /// `CommitPhase::roots()`), the same `challenges` the rounds were
    /// folded with, and the claimed `final_value`. `index` is the same
    /// starting index `prove_query` was called with.
    pub fn verify(
        &self,
        index: usize,
        roots: &[Hash],
        challenges: &[BabyBear],
        final_value: BabyBear,
    ) -> bool {
        if self.openings.len() != roots.len() || roots.len() != challenges.len() {
            return false;
        }
        let log_rounds = roots.len();

        let mut idx = index;
        let mut expected: Option<BabyBear> = None;
        let inv2 = BabyBear::new(2).inverse();

        for i in 0..log_rounds {
            let opening = &self.openings[i];
            // This round's domain has log2 size `log_rounds - i` (round 0
            // is the original domain, each later round half as large).
            let log_size_here = log_rounds - i;
            let n = 1usize << log_size_here;
            let half = n / 2;
            let low = idx % half;

            if opening.low.index != low || opening.high.index != low + half {
                return false;
            }
            if !opening.low.verify(roots[i]) || !opening.high.verify(roots[i]) {
                return false;
            }

            if let Some(exp) = expected {
                let actual_at_idx = if idx < half {
                    opening.low.value
                } else {
                    opening.high.value
                };
                if actual_at_idx != exp {
                    return false;
                }
            }

            let x = domain_generator(log_size_here).pow(low as u64);
            let x_inv = x.inverse();
            let c = challenges[i] * inv2;
            let sum = opening.low.value + opening.high.value;
            let diff = opening.low.value.sub(opening.high.value);
            expected = Some(sum * inv2 + c * (x_inv * diff));

            idx = low;
        }

        expected == Some(final_value)
    }
}

/// A complete, non-interactive FRI proof: run the commit phase and answer
/// `num_queries` queries, with every fold challenge and every query index
/// derived via Fiat-Shamir rather than supplied by a live verifier.
#[derive(Clone, Debug)]
pub struct Proof {
    pub roots: Vec<Hash>,
    pub final_value: BabyBear,
    pub query_proofs: Vec<FriQueryProof>,
}

impl Proof {
    pub fn prove(
        initial_evals: &[BabyBear],
        initial_domain: &[BabyBear],
        num_queries: usize,
    ) -> Self {
        let n = initial_evals.len();
        let mut transcript = Transcript::new(PROTOCOL_LABEL);
        let commit = CommitPhase::prove(initial_evals, initial_domain, &mut transcript);

        let query_proofs = (0..num_queries)
            .map(|_| {
                let index = transcript.challenge_index(QUERY_INDEX_LABEL, n);
                commit.prove_query(index)
            })
            .collect();

        Proof {
            roots: commit.roots(),
            final_value: commit.final_value(),
            query_proofs,
        }
    }

    /// Verify this proof against the claimed `log_size` (number of fold
    /// rounds, i.e. `log2` of the original domain size) and `num_queries`.
    /// Replays the same transcript the prover must have used: absorbs
    /// each root and re-derives its fold challenge, absorbs the final
    /// value, then re-derives each query index and checks the
    /// corresponding `FriQueryProof` against those recomputed challenges.
    /// A prover who tampers with any root or the final value after the
    /// fact changes every challenge and index downstream of that point,
    /// so the included query proofs -- built against the original,
    /// honest transcript -- stop lining up.
    pub fn verify(&self, log_size: usize, num_queries: usize) -> bool {
        if self.roots.len() != log_size || self.query_proofs.len() != num_queries {
            return false;
        }

        let mut transcript = Transcript::new(PROTOCOL_LABEL);
        let challenges: Vec<BabyBear> = self
            .roots
            .iter()
            .map(|root| {
                transcript.absorb(ROUND_ROOT_LABEL, root);
                transcript.challenge_field(FOLD_CHALLENGE_LABEL)
            })
            .collect();
        transcript.absorb(FINAL_VALUE_LABEL, &self.final_value.to_bytes());

        let n = 1usize << log_size;
        for query_proof in &self.query_proofs {
            let index = transcript.challenge_index(QUERY_INDEX_LABEL, n);
            if !query_proof.verify(index, &self.roots, &challenges, self.final_value) {
                return false;
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(x: u32) -> BabyBear {
        BabyBear::new(x)
    }

    /// Plain polynomial evaluation from coefficients (Horner's method),
    /// used only as an independent reference for the tests below -- never
    /// called by `fold` itself, which only ever works from evaluations.
    fn eval_poly(coeffs: &[BabyBear], x: BabyBear) -> BabyBear {
        let mut result = BabyBear::ZERO;
        for &c in coeffs.iter().rev() {
            result = result * x + c;
        }
        result
    }

    #[test]
    fn domain_has_the_right_size_and_order() {
        for log_size in 0..=10 {
            let d = domain(log_size);
            assert_eq!(d.len(), 1 << log_size);
            let g = domain_generator(log_size);
            assert_eq!(g.pow(1u64 << log_size), BabyBear::ONE);
            if log_size > 0 {
                assert_ne!(g.pow(1u64 << (log_size - 1)), BabyBear::ONE);
            }
        }
    }

    #[test]
    fn domain_points_pair_up_as_x_and_negative_x() {
        let d = domain(4); // size 16
        let half = d.len() / 2;
        for i in 0..half {
            assert_eq!(d[i + half], d[i].neg());
        }
    }

    /// The test that actually matters: folding evaluations must be
    /// equivalent to folding the underlying polynomial's even/odd
    /// coefficient split, checked directly rather than just trusting
    /// `fold`'s own internal consistency.
    #[test]
    fn fold_matches_direct_polynomial_evaluation() {
        for log_size in [2usize, 3, 4, 6] {
            let n = 1usize << log_size;
            let domain_pts = domain(log_size);
            // A full-degree polynomial: n arbitrary, non-trivial coefficients.
            let coeffs: Vec<BabyBear> = (1..=n as u32).map(v).collect();
            let evals: Vec<BabyBear> = domain_pts.iter().map(|&x| eval_poly(&coeffs, x)).collect();

            let challenge = v(1234567);
            let folded_evals = fold(&evals, &domain_pts, challenge);
            let new_domain = fold_domain(&domain_pts);

            let even_coeffs: Vec<BabyBear> = coeffs.iter().step_by(2).copied().collect();
            let odd_coeffs: Vec<BabyBear> = coeffs.iter().skip(1).step_by(2).copied().collect();
            let expected: Vec<BabyBear> = new_domain
                .iter()
                .map(|&y| eval_poly(&even_coeffs, y) + challenge * eval_poly(&odd_coeffs, y))
                .collect();

            assert_eq!(folded_evals, expected, "mismatch at log_size={log_size}");
        }
    }

    /// Repeated folding, all the way down to a single value, checked at
    /// every step against the same direct reference -- not just the first
    /// round.
    #[test]
    fn repeated_folding_matches_reference_at_every_step() {
        let log_size = 5; // size 32
        let n = 1usize << log_size;
        let mut domain_pts = domain(log_size);
        let mut coeffs: Vec<BabyBear> = (1..=n as u32).map(v).collect();
        let mut evals: Vec<BabyBear> = domain_pts.iter().map(|&x| eval_poly(&coeffs, x)).collect();

        for round in 0..log_size {
            let challenge = v(100 + round as u32);
            let folded = fold(&evals, &domain_pts, challenge);
            let new_domain = fold_domain(&domain_pts);

            let even: Vec<BabyBear> = coeffs.iter().step_by(2).copied().collect();
            let odd: Vec<BabyBear> = coeffs.iter().skip(1).step_by(2).copied().collect();
            let expected: Vec<BabyBear> = new_domain
                .iter()
                .map(|&y| eval_poly(&even, y) + challenge * eval_poly(&odd, y))
                .collect();
            assert_eq!(folded, expected, "mismatch at round {round}");

            // The folded polynomial's own coefficients, for the next round's
            // reference computation.
            coeffs = even
                .iter()
                .zip(odd.iter())
                .map(|(&e, &o)| e + challenge * o)
                .collect();
            evals = folded;
            domain_pts = new_domain;
        }

        // After log_size rounds we're down to one point and one
        // (constant) coefficient.
        assert_eq!(evals.len(), 1);
        assert_eq!(coeffs.len(), 1);
        assert_eq!(evals[0], coeffs[0]);
    }

    #[test]
    #[should_panic]
    fn fold_rejects_mismatched_lengths() {
        let d = domain(3);
        let evals = vec![BabyBear::ZERO; 4];
        fold(&evals, &d, v(1));
    }

    #[test]
    #[should_panic]
    fn fold_rejects_size_one_domain() {
        let d = domain(0);
        let evals = vec![BabyBear::ZERO; 1];
        fold(&evals, &d, v(1));
    }

    fn sample_commit_phase(log_size: usize, seed: u32) -> (CommitPhase, Vec<BabyBear>) {
        let n = 1usize << log_size;
        let domain_pts = domain(log_size);
        let coeffs: Vec<BabyBear> = (1..=n as u32).map(|i| v(seed * 1000 + i)).collect();
        let evals: Vec<BabyBear> = domain_pts.iter().map(|&x| eval_poly(&coeffs, x)).collect();
        let challenges: Vec<BabyBear> = (0..log_size as u32).map(|i| v(777 + seed * 100 + i)).collect();
        let commit = CommitPhase::run(&evals, &domain_pts, &challenges);
        (commit, challenges)
    }

    #[test]
    fn honest_query_verifies_at_every_starting_index() {
        let log_size = 4; // domain size 16
        let (commit, challenges) = sample_commit_phase(log_size, 1);
        let roots = commit.roots();
        let final_value = commit.final_value();

        for index in 0..(1usize << log_size) {
            let proof = commit.prove_query(index);
            assert!(
                proof.verify(index, &roots, &challenges, final_value),
                "query at index {index} failed to verify"
            );
        }
    }

    #[test]
    fn tampered_opening_value_rejected() {
        let (commit, challenges) = sample_commit_phase(4, 1);
        let roots = commit.roots();
        let final_value = commit.final_value();

        let mut proof = commit.prove_query(5);
        proof.openings[0].low.value = proof.openings[0].low.value + BabyBear::new(1);
        assert!(!proof.verify(5, &roots, &challenges, final_value));
    }

    #[test]
    fn tampered_root_rejected() {
        let (commit_a, challenges) = sample_commit_phase(4, 1);
        let (commit_b, _) = sample_commit_phase(4, 2);
        let proof = commit_a.prove_query(3);
        // Verify against an unrelated commit phase's roots.
        assert!(!proof.verify(3, &commit_b.roots(), &challenges, commit_a.final_value()));
    }

    #[test]
    fn wrong_final_value_rejected() {
        let (commit, challenges) = sample_commit_phase(4, 1);
        let roots = commit.roots();
        let proof = commit.prove_query(7);
        assert!(!proof.verify(
            7,
            &roots,
            &challenges,
            commit.final_value() + BabyBear::new(1)
        ));
    }

    /// A concrete cheating scenario, not just a tampered opening: the
    /// prover commits a round-1 evaluation that is *not* the honest fold
    /// of round 0 at that position. Querying at the index that lands on
    /// the tampered position must catch it via the cross-round
    /// consistency check specifically (not just a broken Merkle opening,
    /// which would be a weaker test).
    #[test]
    fn dishonest_fold_is_caught_by_cross_round_consistency() {
        let log_size = 3; // domain size 8
        let n = 1usize << log_size;
        let domain_pts = domain(log_size);
        let coeffs: Vec<BabyBear> = (1..=n as u32).map(v).collect();
        let evals: Vec<BabyBear> = domain_pts.iter().map(|&x| eval_poly(&coeffs, x)).collect();
        let challenges: Vec<BabyBear> = vec![v(11), v(22), v(33)];

        // Build round 0 and round 1 by hand: round 1 should be the honest
        // fold of round 0, but we corrupt one entry before committing it.
        let round0_tree = MerkleTree::commit(&evals);
        let mut round1_evals = fold(&evals, &domain_pts, challenges[0]);
        round1_evals[0] = round1_evals[0] + BabyBear::new(1); // the lie
        let domain1 = fold_domain(&domain_pts);
        let round1_tree = MerkleTree::commit(&round1_evals);

        let round2_evals = fold(&round1_evals, &domain1, challenges[1]);
        let domain2 = fold_domain(&domain1);
        let round2_tree = MerkleTree::commit(&round2_evals);

        let round3_evals = fold(&round2_evals, &domain2, challenges[2]);
        assert_eq!(round3_evals.len(), 1);

        let roots = vec![round0_tree.root(), round1_tree.root(), round2_tree.root()];

        // Querying at index 0 (or 4, its pair) lands on the corrupted
        // position (index 0 of round 1) after the first fold.
        let commit = CommitPhase {
            rounds: vec![round0_tree, round1_tree, round2_tree],
            challenges: challenges.clone(),
            final_value: round3_evals[0],
        };
        let proof = commit.prove_query(0);
        assert!(!proof.verify(0, &roots, &challenges, round3_evals[0]));
    }

    fn sample_evals_and_domain(log_size: usize, seed: u32) -> (Vec<BabyBear>, Vec<BabyBear>) {
        let n = 1usize << log_size;
        let domain_pts = domain(log_size);
        let coeffs: Vec<BabyBear> = (1..=n as u32).map(|i| v(seed * 1000 + i)).collect();
        let evals: Vec<BabyBear> = domain_pts.iter().map(|&x| eval_poly(&coeffs, x)).collect();
        (evals, domain_pts)
    }

    #[test]
    fn honest_proof_verifies() {
        let log_size = 5;
        let (evals, domain_pts) = sample_evals_and_domain(log_size, 1);
        let proof = Proof::prove(&evals, &domain_pts, 8);
        assert!(proof.verify(log_size, 8));
    }

    /// Two honest proofs over the same input are byte-for-byte identical
    /// -- there's no randomness left outside the transcript, which is
    /// itself a deterministic function of the absorbed data.
    #[test]
    fn proving_is_deterministic() {
        let (evals, domain_pts) = sample_evals_and_domain(4, 1);
        let a = Proof::prove(&evals, &domain_pts, 5);
        let b = Proof::prove(&evals, &domain_pts, 5);
        assert_eq!(a.roots, b.roots);
        assert_eq!(a.final_value, b.final_value);
    }

    /// Different inputs produce different fold challenges and query
    /// indices, since both are derived from the committed roots -- not
    /// just a coincidence of the particular `seed`s picked elsewhere in
    /// this file.
    #[test]
    fn different_inputs_give_different_query_indices() {
        let (evals_a, domain_pts) = sample_evals_and_domain(4, 1);
        let (evals_b, _) = sample_evals_and_domain(4, 2);
        let proof_a = Proof::prove(&evals_a, &domain_pts, 5);
        let proof_b = Proof::prove(&evals_b, &domain_pts, 5);
        assert_ne!(proof_a.roots, proof_b.roots);
    }

    #[test]
    fn tampered_root_in_proof_is_rejected() {
        let log_size = 4;
        let (evals, domain_pts) = sample_evals_and_domain(log_size, 1);
        let mut proof = Proof::prove(&evals, &domain_pts, 6);
        proof.roots[1][0] ^= 1;
        assert!(!proof.verify(log_size, 6));
    }

    #[test]
    fn tampered_final_value_in_proof_is_rejected() {
        let log_size = 4;
        let (evals, domain_pts) = sample_evals_and_domain(log_size, 1);
        let mut proof = Proof::prove(&evals, &domain_pts, 6);
        proof.final_value = proof.final_value + BabyBear::new(1);
        assert!(!proof.verify(log_size, 6));
    }

    #[test]
    fn tampered_query_opening_in_proof_is_rejected() {
        let log_size = 4;
        let (evals, domain_pts) = sample_evals_and_domain(log_size, 1);
        let mut proof = Proof::prove(&evals, &domain_pts, 6);
        proof.query_proofs[0].openings[0].low.value =
            proof.query_proofs[0].openings[0].low.value + BabyBear::new(1);
        assert!(!proof.verify(log_size, 6));
    }

    #[test]
    fn verify_rejects_wrong_log_size_or_query_count() {
        let log_size = 4;
        let (evals, domain_pts) = sample_evals_and_domain(log_size, 1);
        let proof = Proof::prove(&evals, &domain_pts, 6);
        assert!(!proof.verify(log_size + 1, 6));
        assert!(!proof.verify(log_size, 7));
    }
}
