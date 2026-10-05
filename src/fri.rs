//! FRI (Fast Reed-Solomon IOP of Proximity): the protocol that lets a
//! prover convince a verifier that a function, given only as evaluations
//! over a domain, is close to a polynomial of some bounded degree --
//! without ever revealing the polynomial's coefficients. It works by
//! repeatedly "folding" the evaluations (shrinking the domain and the
//! degree bound together), with random spot-checks along the way to catch
//! a prover who folded dishonestly.
//!
//! # What's being proven, exactly
//!
//! Evaluations of `f` over a domain of size `n = 2^log_size`, claimed to
//! be a polynomial of degree `< n / 2^log_blowup`. Each binary fold halves
//! both the domain and the degree bound, so after `log_size - log_blowup`
//! of them an honest `f` has become a *constant*, still evaluated over
//! `2^log_blowup` points. The prover states that constant (`final_value`),
//! and every query checks its folding path lands on it.
//!
//! Stopping there -- rather than folding down to one point -- is the whole
//! point: *any* function on `n` points is some polynomial of degree `< n`,
//! so folding to a single value would prove nothing about degree. It's the
//! leftover `2^log_blowup`-fold redundancy, all required to agree on one
//! constant, that a high-degree function can't fake (see
//! `random_high_degree_evaluations_are_rejected`). Each query catches a
//! function far from low-degree with probability roughly
//! `1 - 2^-log_blowup`, so soundness is about `log_blowup * num_queries`
//! bits, plus `grinding_bits` (below).
//!
//! # Shape: an implicit first layer, then arity-8 rounds
//!
//! - **The first layer is never committed.** FRI is run on a function the
//!   caller can already evaluate at any query point from its own
//!   commitments (a STARK's DEEP combination, computed from opened trace
//!   rows) -- so the caller supplies those two values per query, and FRI
//!   folds them with the first challenge. Committing and opening that layer
//!   again would only repeat what the caller already proved.
//! - **Every later round folds by 8** (fewer at the very end, if the bits
//!   don't divide evenly). A round commits leaves that each hold a whole
//!   coset of 8 values, and folds them with one challenge `beta` -- as three
//!   binary folds with `beta`, `beta^2`, `beta^4`, which is exactly
//!   `sum_j beta^j f_j` for `f(x) = sum_j x^j f_j(x^8)`. One opening per
//!   round per query, a third as many rounds as binary folding.
//!
//! # Fields and domains
//!
//! Evaluations and fold challenges live in the extension field (`ext`) --
//! a challenge drawn from BabyBear itself, at ~2^31 possibilities, would
//! let a cheating prover get lucky far too often. The domain points stay
//! in BabyBear, and may be a *coset* `shift · <g>`: a STARK evaluates over
//! a coset disjoint from its trace domain.
//!
//! # Fiat-Shamir and grinding
//!
//! Every challenge, and every query index, is derived from a
//! `transcript::Transcript` the caller passes in -- after the round's
//! commitment has been absorbed, so a prover can't choose round `i`'s
//! values knowing round `i`'s challenge. Before the query indices are
//! drawn, the prover must find a nonce whose hash with the transcript has
//! `grinding_bits` leading zeros: re-rolling the queries now costs
//! `2^grinding_bits` work per attempt, which buys that many bits of
//! security for far less than the queries it replaces.

#![allow(dead_code)]

use crate::ext::Ext;
use crate::merkle::{Hash, MerkleTree, Opening};
use crate::poseidon2::BabyBear;
use crate::transcript::Transcript;

/// Domain-separation labels for the Fiat-Shamir transcript.
pub(crate) const ROUND_ROOT_LABEL: &[u8] = b"fri-round-root";
pub(crate) const FOLD_CHALLENGE_LABEL: &[u8] = b"fri-fold-challenge";
pub(crate) const FINAL_VALUE_LABEL: &[u8] = b"fri-final-value";
pub(crate) const GRIND_LABEL: &[u8] = b"fri-grind";
pub(crate) const QUERY_INDEX_LABEL: &[u8] = b"fri-query-index";

/// `log2` of the folding arity of every committed round (except possibly
/// the last).
pub const MAX_ARITY_BITS: usize = 3;

/// Every tree here (and in `stark`) commits to its top `2^CAP_HEIGHT`
/// nodes rather than its root (`MerkleTree::cap`), so each opening's path
/// is that many hashes shorter -- a net saving once a proof makes more
/// than a few dozen openings per tree, which it always does.
pub const CAP_HEIGHT: usize = 5;

/// The size a cap must have for a tree of `leaves` leaves.
pub fn cap_len(leaves: usize) -> usize {
    leaves.min(1 << CAP_HEIGHT)
}

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

/// A generator of BabyBear's order-`2^log_size` multiplicative subgroup.
pub fn domain_generator(log_size: usize) -> BabyBear {
    assert!(
        log_size <= MAX_TWO_ADICITY,
        "log_size {log_size} exceeds BabyBear's 2-adicity ({MAX_TWO_ADICITY})"
    );
    BabyBear::new(TWO_ADIC_GENERATORS[log_size])
}

/// The coset `[shift · g^0, shift · g^1, ..., shift · g^(n-1)]` for
/// `n = 2^log_size`, `g` the order-`n` generator. `shift = 1` gives the
/// subgroup itself. Point `i + n/2` is always `-`(point `i`), since
/// `g^(n/2)` has order 2 and is therefore `-1` -- the pairing `fold`
/// relies on.
pub fn coset_domain(shift: BabyBear, log_size: usize) -> Vec<BabyBear> {
    let g = domain_generator(log_size);
    let n = 1usize << log_size;
    let mut points = Vec::with_capacity(n);
    let mut cur = shift;
    for _ in 0..n {
        points.push(cur);
        cur = cur * g;
    }
    points
}

/// The subgroup of order `2^log_size` itself.
pub fn domain(log_size: usize) -> Vec<BabyBear> {
    coset_domain(BabyBear::ONE, log_size)
}

/// One binary FRI fold: given evaluations of a polynomial `f` over
/// `domain`, and a `challenge`, return evaluations of
/// `f'(y) = f_even(y) + challenge * f_odd(y)` over the squared
/// (half-size) domain, where `f(x) = f_even(x^2) + x * f_odd(x^2)`.
///
/// For each pair `{x, -x}` (`domain[i]` and `domain[i + n/2]`):
/// `f_even(x^2) = (f(x)+f(-x))/2` and `f_odd(x^2) = (f(x)-f(-x))/(2x)`.
pub fn fold(evals: &[Ext], domain: &[BabyBear], challenge: Ext) -> Vec<Ext> {
    assert_eq!(evals.len(), domain.len(), "evaluations and domain must have the same length");
    let n = evals.len();
    assert!(
        n.is_power_of_two() && n > 1,
        "domain size must be a power of two greater than 1, got {n}"
    );
    let half = n / 2;
    (0..half)
        .map(|i| fold_pair(evals[i], evals[i + half], domain[i], challenge))
        .collect()
}

/// `fold`'s arithmetic for one pair: `f(x)`, `f(-x)`, `x`.
pub fn fold_pair(f_x: Ext, f_neg_x: Ext, x: BabyBear, challenge: Ext) -> Ext {
    let inv2 = BabyBear::new(2).inverse();
    let even = (f_x + f_neg_x).mul_base(inv2);
    let odd = (f_x - f_neg_x).mul_base(inv2 * x.inverse());
    even + challenge * odd
}

/// The domain `fold`'s output lives over: a coset `shift · <g>` squares to
/// the coset `shift^2 · <g^2>`.
pub fn fold_domain(domain: &[BabyBear]) -> Vec<BabyBear> {
    let half = domain.len() / 2;
    domain[..half].iter().map(|&x| x * x).collect()
}

/// One committed round's whole fold, from a single leaf: `values[m]` is
/// `f` at position `j + m·(len/a)` of a layer of size `len = 2^log_len`
/// over `shift · <g>`; returns the folded function at position `j` of the
/// next layer. `a = values.len()` binary folds' worth, with challenges
/// `challenge`, `challenge^2`, ... -- exactly what `fold`ing the whole
/// layer that many times computes there.
fn fold_leaf(values: &[Ext], j: usize, shift: BabyBear, log_len: usize, challenge: Ext) -> Ext {
    let mut values = values.to_vec();
    let (mut shift, mut log_len, mut beta) = (shift, log_len, challenge);
    while values.len() > 1 {
        let half = values.len() / 2;
        let group = (1usize << log_len) / values.len();
        let g = domain_generator(log_len);
        for m in 0..half {
            let x = shift * g.pow((j + m * group) as u64);
            values[m] = fold_pair(values[m], values[m + half], x, beta);
        }
        values.truncate(half);
        shift = shift * shift;
        log_len -= 1;
        beta = beta * beta;
    }
    values[0]
}

/// The arity (`log2`) of each committed round, for a first layer of size
/// `2^log_size`: the implicit first fold takes it to `log_size - 1`, then
/// rounds of up to `MAX_ARITY_BITS` down to `log_blowup`.
pub(crate) fn round_arities(log_size: usize, log_blowup: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut log = log_size - 1;
    while log > log_blowup {
        let bits = (log - log_blowup).min(MAX_ARITY_BITS);
        out.push(bits);
        log -= bits;
    }
    out
}

/// How many values of the folded functions one query reveals: the first
/// layer's pair, then one whole coset per committed round.
pub fn revealed_per_query(log_size: usize, log_blowup: usize) -> usize {
    2 + round_arities(log_size, log_blowup).iter().map(|&bits| 1usize << bits).sum::<usize>()
}

/// One committed round's leaf `j`: the coset of `2^bits` values it folds.
fn leaf(layer: &[Ext], j: usize, bits: usize) -> Vec<u8> {
    let group = layer.len() >> bits;
    (0..1usize << bits).flat_map(|m| layer[j + m * group].to_bytes()).collect()
}

fn decode_leaf(opening: &Opening, bits: usize) -> Option<Vec<Ext>> {
    if opening.leaf.len() != 16 << bits {
        return None;
    }
    Some(
        opening
            .leaf
            .chunks_exact(16)
            .map(|c| Ext::from_bytes(c.try_into().unwrap()))
            .collect(),
    )
}

/// One query's evidence: one opening per committed round.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FriQueryProof {
    pub openings: Vec<Opening>,
}

/// A complete, non-interactive FRI proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    /// Each committed round's tree, as its cap.
    pub caps: Vec<Vec<Hash>>,
    pub final_value: Ext,
    pub grinding_nonce: u64,
    pub query_proofs: Vec<FriQueryProof>,
}

/// The settings both sides must agree on.
#[derive(Clone, Copy, Debug)]
pub struct Settings {
    pub log_blowup: usize,
    pub num_queries: usize,
    pub grinding_bits: u32,
}

impl Proof {
    /// Prove that `first_layer`, over `coset_domain(shift,
    /// log2(first_layer.len()))`, is a polynomial of degree `<
    /// first_layer.len() / 2^log_blowup`. The first layer itself isn't
    /// committed (see the module docs): the caller must be able to vouch
    /// for its values at each query on its own. Returns the proof and
    /// each query's pair index -- query `q` needs the first layer at
    /// `indices[q]` and `indices[q] + n/2`.
    pub fn prove(first_layer: Vec<Ext>, shift: BabyBear, settings: Settings, transcript: &mut Transcript) -> (Self, Vec<usize>) {
        let n = first_layer.len();
        assert!(n.is_power_of_two(), "length must be a power of two, got {n}");
        let log_size = n.trailing_zeros() as usize;
        assert!(
            log_size > settings.log_blowup,
            "domain (2^{log_size}) must be larger than the blowup (2^{})",
            settings.log_blowup
        );

        let beta0 = transcript.challenge_ext(FOLD_CHALLENGE_LABEL);
        let mut layer = fold(&first_layer, &coset_domain(shift, log_size), beta0);
        let mut shift = shift * shift;
        let mut log = log_size - 1;
        let mut trees = Vec::new();
        for bits in round_arities(log_size, settings.log_blowup) {
            let group = layer.len() >> bits;
            let tree = MerkleTree::commit((0..group).map(|j| leaf(&layer, j, bits)).collect());
            transcript.absorb_digests(ROUND_ROOT_LABEL, &tree.cap(CAP_HEIGHT));
            let mut beta = transcript.challenge_ext(FOLD_CHALLENGE_LABEL);
            for _ in 0..bits {
                layer = fold(&layer, &coset_domain(shift, log), beta);
                beta = beta * beta;
                shift = shift * shift;
                log -= 1;
            }
            trees.push((tree, bits));
        }
        // An honest, low-degree input has folded down to a constant.
        let final_value = layer[0];
        transcript.absorb_ext(FINAL_VALUE_LABEL, &[final_value]);

        let grinding_nonce = transcript.grind(GRIND_LABEL, settings.grinding_bits);
        transcript.absorb(GRIND_LABEL, &[BabyBear::new(grinding_nonce as u32)]);

        let indices: Vec<usize> = (0..settings.num_queries)
            .map(|_| transcript.challenge_index(QUERY_INDEX_LABEL, n / 2))
            .collect();
        let query_proofs = indices
            .iter()
            .map(|&low| {
                let mut p = low;
                let openings = trees
                    .iter()
                    .map(|(tree, bits)| {
                        let j = p % (tree.len());
                        let _ = bits;
                        p = j;
                        tree.open_to_cap(j, CAP_HEIGHT)
                    })
                    .collect();
                FriQueryProof { openings }
            })
            .collect();
        let proof = Proof {
            caps: trees.iter().map(|(t, _)| t.cap(CAP_HEIGHT)).collect(),
            final_value,
            grinding_nonce,
            query_proofs,
        };
        (proof, indices)
    }

    /// Verify against the same parameters, replaying the transcript the
    /// prover must have used. `first_layer(q, i)` must return the first
    /// layer's values at positions `i` and `i + n/2` for query `q` --
    /// vouched for by the caller's own commitments -- or `None` to reject.
    pub fn verify(
        &self,
        log_size: usize,
        shift: BabyBear,
        settings: Settings,
        transcript: &mut Transcript,
        mut first_layer: impl FnMut(usize, usize) -> Option<(Ext, Ext)>,
    ) -> bool {
        if log_size <= settings.log_blowup || log_size > MAX_TWO_ADICITY {
            return false;
        }
        let arities = round_arities(log_size, settings.log_blowup);
        if self.caps.len() != arities.len()
            || self.query_proofs.len() != settings.num_queries
            || self.query_proofs.iter().any(|q| q.openings.len() != arities.len())
        {
            return false;
        }

        let beta0 = transcript.challenge_ext(FOLD_CHALLENGE_LABEL);
        // Each round's tree has as many leaves as its layer has cosets.
        let mut leaves = Vec::with_capacity(arities.len());
        let mut log = log_size - 1;
        for &bits in &arities {
            leaves.push((1usize << log) >> bits);
            log -= bits;
        }
        if self.caps.iter().zip(&leaves).any(|(cap, &l)| cap.len() != cap_len(l)) {
            return false;
        }
        let challenges: Vec<Ext> = self
            .caps
            .iter()
            .map(|cap| {
                transcript.absorb_digests(ROUND_ROOT_LABEL, cap);
                transcript.challenge_ext(FOLD_CHALLENGE_LABEL)
            })
            .collect();
        transcript.absorb_ext(FINAL_VALUE_LABEL, &[self.final_value]);
        if !transcript.check_grind(GRIND_LABEL, self.grinding_nonce, settings.grinding_bits) {
            return false;
        }
        transcript.absorb(GRIND_LABEL, &[BabyBear::new(self.grinding_nonce as u32)]);

        let n = 1usize << log_size;
        for (q, query) in self.query_proofs.iter().enumerate() {
            let low = transcript.challenge_index(QUERY_INDEX_LABEL, n / 2);
            let Some((f_x, f_neg_x)) = first_layer(q, low) else {
                return false;
            };
            let x = shift * domain_generator(log_size).pow(low as u64);
            let mut value = fold_pair(f_x, f_neg_x, x, beta0);
            let mut p = low;
            let mut layer_shift = shift * shift;
            let mut log = log_size - 1;
            for (r, &bits) in arities.iter().enumerate() {
                let group = (1usize << log) >> bits;
                let (j, slot) = (p % group, p / group);
                let opening = &query.openings[r];
                if opening.index != j || !opening.verify_cap(&self.caps[r], leaves[r]) {
                    return false;
                }
                let Some(values) = decode_leaf(opening, bits) else {
                    return false;
                };
                if values[slot] != value {
                    return false;
                }
                value = fold_leaf(&values, j, layer_shift, log, challenges[r]);
                for _ in 0..bits {
                    layer_shift = layer_shift * layer_shift;
                }
                log -= bits;
                p = j;
            }
            if value != self.final_value {
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

    /// Horner's method over the extension, from base-field coefficients --
    /// an independent reference, never used by `fold` itself.
    fn eval_poly(coeffs: &[BabyBear], x: BabyBear) -> Ext {
        let mut acc = BabyBear::ZERO;
        for &c in coeffs.iter().rev() {
            acc = acc * x + c;
        }
        Ext::from_base(acc)
    }

    fn sample_coeffs(n: usize, seed: u32) -> Vec<BabyBear> {
        (0..n as u32).map(|i| v(seed.wrapping_mul(7919) + i * 31 + 1)).collect()
    }

    fn evaluations(coeffs: &[BabyBear], shift: BabyBear, log_size: usize) -> Vec<Ext> {
        coset_domain(shift, log_size).iter().map(|&x| eval_poly(coeffs, x)).collect()
    }

    const SHIFT: BabyBear = BabyBear::new_const(31);

    const SETTINGS: Settings = Settings {
        log_blowup: 3,
        num_queries: 10,
        grinding_bits: 4,
    };

    #[test]
    fn domain_has_the_right_size_and_order() {
        let d = domain(4);
        assert_eq!(d.len(), 16);
        assert_eq!(d[0], BabyBear::ONE);
        assert_eq!(domain_generator(4).pow(16), BabyBear::ONE);
        assert_ne!(domain_generator(4).pow(8), BabyBear::ONE);
    }

    #[test]
    fn coset_points_pair_up_as_x_and_negative_x() {
        let d = coset_domain(SHIFT, 4);
        for i in 0..8 {
            assert_eq!(d[i + 8], d[i].neg());
        }
    }

    /// The test that actually matters for the math: folding evaluations
    /// must equal folding the underlying polynomial's even/odd coefficient
    /// split, checked directly -- over a coset, with an extension challenge.
    #[test]
    fn fold_matches_direct_polynomial_evaluation() {
        let log_size = 4;
        let coeffs = sample_coeffs(16, 3);
        let evals = evaluations(&coeffs, SHIFT, log_size);
        let challenge = Ext([v(5), v(6), v(7), v(8)]);

        let folded = fold(&evals, &coset_domain(SHIFT, log_size), challenge);
        let folded_domain = fold_domain(&coset_domain(SHIFT, log_size));

        let even: Vec<BabyBear> = coeffs.iter().step_by(2).copied().collect();
        let odd: Vec<BabyBear> = coeffs.iter().skip(1).step_by(2).copied().collect();
        for (i, &y) in folded_domain.iter().enumerate() {
            let expected = eval_poly(&even, y) + challenge * eval_poly(&odd, y);
            assert_eq!(folded[i], expected, "at {i}");
        }
    }

    /// Folding one leaf's coset (what the verifier does) gives exactly what
    /// folding the whole layer three times (what the prover does) gives.
    #[test]
    fn folding_a_leaf_matches_folding_the_whole_layer() {
        let log_len = 6;
        let layer = evaluations(&sample_coeffs(40, 2), SHIFT, log_len);
        let beta = Ext([v(9), v(1), v(4), v(7)]);
        let mut whole = layer.clone();
        let (mut shift, mut log, mut b) = (SHIFT, log_len, beta);
        for _ in 0..3 {
            whole = fold(&whole, &coset_domain(shift, log), b);
            shift = shift * shift;
            log -= 1;
            b = b * b;
        }
        let group = layer.len() / 8;
        for j in 0..group {
            let values: Vec<Ext> = (0..8).map(|m| layer[j + m * group]).collect();
            assert_eq!(fold_leaf(&values, j, SHIFT, log_len, beta), whole[j], "leaf {j}");
        }
    }

    #[test]
    fn rounds_fold_by_eight_except_possibly_the_last() {
        assert_eq!(round_arities(12, 2), vec![3, 3, 3]);
        assert_eq!(round_arities(13, 2), vec![3, 3, 3, 1]);
        assert_eq!(round_arities(4, 3), Vec::<usize>::new());
    }

    /// Run a whole proof over `evals`, answering the first-layer callback
    /// from `evals` itself -- standing in for a STARK's own openings.
    fn prove_and_verify(evals: Vec<Ext>, log_size: usize, settings: Settings) -> bool {
        let (proof, indices) = Proof::prove(evals.clone(), SHIFT, settings, &mut Transcript::new(b"test"));
        let half = evals.len() / 2;
        proof.verify(log_size, SHIFT, settings, &mut Transcript::new(b"test"), |q, i| {
            (indices[q] == i).then(|| (evals[i], evals[i + half]))
        })
    }

    /// A polynomial of degree `< n / blowup` verifies, for round shapes
    /// with and without a short last round, and with no rounds at all.
    #[test]
    fn a_low_degree_polynomial_verifies() {
        for (log_size, log_blowup) in [(10, 2), (11, 3), (8, 2), (4, 3)] {
            let settings = Settings { log_blowup, ..SETTINGS };
            let degree_bound = 1 << (log_size - log_blowup);
            let evals = evaluations(&sample_coeffs(degree_bound, 9), SHIFT, log_size);
            assert!(prove_and_verify(evals, log_size, settings), "2^{log_size}, blowup 2^{log_blowup}");
        }
    }

    /// Arbitrary data -- not low-degree at all -- must be rejected.
    #[test]
    fn random_high_degree_evaluations_are_rejected() {
        let evals: Vec<Ext> = (0..1024u32)
            .map(|i| Ext([v(i.wrapping_mul(i).wrapping_mul(7919) + 13), v(i + 1), v(3 * i), v(i ^ 5)]))
            .collect();
        assert!(!prove_and_verify(evals, 10, SETTINGS));
    }

    /// Exactly one degree too many is still caught.
    #[test]
    fn a_polynomial_just_over_the_degree_bound_is_rejected() {
        let degree_bound = 1 << (10 - SETTINGS.log_blowup);
        let evals = evaluations(&sample_coeffs(degree_bound + 1, 4), SHIFT, 10);
        assert!(!prove_and_verify(evals, 10, SETTINGS));
    }

    fn honest() -> (Proof, Vec<usize>, Vec<Ext>) {
        let evals = evaluations(&sample_coeffs(128, 1), SHIFT, 10);
        let (proof, indices) = Proof::prove(evals.clone(), SHIFT, SETTINGS, &mut Transcript::new(b"test"));
        (proof, indices, evals)
    }

    fn verifies(proof: &Proof, evals: &[Ext]) -> bool {
        let half = evals.len() / 2;
        proof.verify(10, SHIFT, SETTINGS, &mut Transcript::new(b"test"), |_, i| Some((evals[i], evals[i + half])))
    }

    #[test]
    fn proving_is_deterministic() {
        assert_eq!(honest().0, honest().0);
    }

    #[test]
    fn tampering_with_any_part_of_the_proof_is_rejected() {
        let (proof, _, evals) = honest();
        assert!(verifies(&proof, &evals));

        let mut p = proof.clone();
        p.caps[1][0][0] ^= 1;
        assert!(!verifies(&p, &evals));

        let mut p = proof.clone();
        p.final_value = p.final_value + Ext::ONE;
        assert!(!verifies(&p, &evals));

        let mut p = proof.clone();
        p.query_proofs[0].openings[1].leaf[0] ^= 1;
        assert!(!verifies(&p, &evals));

        let mut p = proof;
        p.grinding_nonce += 1;
        // A different nonce almost always misses the grinding target (and
        // changes every query index even when it doesn't).
        assert!(!verifies(&p, &evals));
    }

    /// The first layer's values the caller vouches for are part of the
    /// check: different ones break the folding path.
    #[test]
    fn wrong_first_layer_values_are_rejected() {
        let (proof, _, evals) = honest();
        let half = evals.len() / 2;
        assert!(!proof.verify(10, SHIFT, SETTINGS, &mut Transcript::new(b"test"), |_, i| {
            Some((evals[i] + Ext::ONE, evals[i + half]))
        }));
    }

    #[test]
    fn verify_rejects_wrong_parameters() {
        let (proof, _, evals) = honest();
        let half = evals.len() / 2;
        let answer = |_: usize, i: usize| Some((evals[i % half], evals[i % half + half]));
        assert!(!proof.verify(11, SHIFT, SETTINGS, &mut Transcript::new(b"test"), answer));
        let fewer = Settings { num_queries: 9, ..SETTINGS };
        assert!(!proof.verify(10, SHIFT, fewer, &mut Transcript::new(b"test"), answer));
        let other_blowup = Settings { log_blowup: 2, ..SETTINGS };
        assert!(!proof.verify(10, SHIFT, other_blowup, &mut Transcript::new(b"test"), answer));
        assert!(!proof.verify(10, BabyBear::ONE, SETTINGS, &mut Transcript::new(b"test"), answer));
        assert!(!proof.verify(10, SHIFT, SETTINGS, &mut Transcript::new(b"other"), answer));
    }
}
