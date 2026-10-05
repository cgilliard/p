//! The number-theoretic transform: the finite-field FFT. Converts between
//! a polynomial's coefficients and its evaluations over a power-of-two
//! subgroup (or a coset of one) in `O(n log n)` -- what a STARK uses to
//! interpolate each trace column and re-evaluate it over a larger domain
//! (its "low-degree extension").
//!
//! Plain iterative radix-2 Cooley-Tukey with a bit-reversal permutation.
//! Values may be any `Field` (BabyBear or its extension); twiddles are
//! always BabyBear, since the domains are.

#![allow(dead_code)]

use crate::field::Field;
use crate::fri::domain_generator;
use crate::poseidon2::BabyBear;

fn bit_reverse_permute<F>(values: &mut [F]) {
    let n = values.len();
    let bits = n.trailing_zeros();
    if bits == 0 {
        return;
    }
    for i in 0..n {
        let j = i.reverse_bits() >> (usize::BITS - bits);
        if i < j {
            values.swap(i, j);
        }
    }
}

/// In place: coefficients -> evaluations over the order-`n` subgroup,
/// `values[i]` becoming `f(g^i)`.
pub fn ntt<F: Field>(values: &mut [F]) {
    transform(values, false);
}

/// In place: evaluations over the order-`n` subgroup -> coefficients.
pub fn intt<F: Field>(values: &mut [F]) {
    transform(values, true);
    let n_inv = BabyBear::new(values.len() as u32).inverse();
    for v in values.iter_mut() {
        *v = v.mul_base(n_inv);
    }
}

fn transform<F: Field>(values: &mut [F], inverse: bool) {
    let n = values.len();
    assert!(n.is_power_of_two(), "length must be a power of two, got {n}");
    bit_reverse_permute(values);
    let mut len = 2;
    while len <= n {
        let log_len = len.trailing_zeros() as usize;
        let mut w_len = domain_generator(log_len);
        if inverse {
            w_len = w_len.inverse();
        }
        let half = len / 2;
        // Twiddles for this stage, computed once and reused per block.
        let mut twiddles = Vec::with_capacity(half);
        let mut w = BabyBear::ONE;
        for _ in 0..half {
            twiddles.push(w);
            w = w * w_len;
        }
        for start in (0..n).step_by(len) {
            for (k, &w) in twiddles.iter().enumerate() {
                let a = values[start + k];
                let b = values[start + k + half].mul_base(w);
                values[start + k] = a + b;
                values[start + k + half] = a - b;
            }
        }
        len *= 2;
    }
}

/// Coefficients -> evaluations over the coset `shift · <g>` of size
/// `2^log_size` (zero-padding `coeffs` up to that size).
pub fn coset_evaluate<F: Field>(coeffs: &[F], shift: BabyBear, log_size: usize) -> Vec<F> {
    let n = 1usize << log_size;
    assert!(coeffs.len() <= n, "more coefficients than evaluation points");
    // f(shift · x) has coefficients c_i · shift^i.
    let mut values = vec![F::ZERO; n];
    let mut s = BabyBear::ONE;
    for (i, &c) in coeffs.iter().enumerate() {
        values[i] = c.mul_base(s);
        s = s * shift;
    }
    ntt(&mut values);
    values
}

/// Evaluations over the coset `shift · <g>` -> coefficients.
pub fn coset_interpolate<F: Field>(evals: &[F], shift: BabyBear) -> Vec<F> {
    let mut coeffs = evals.to_vec();
    intt(&mut coeffs);
    let shift_inv = shift.inverse();
    let mut s = BabyBear::ONE;
    for c in coeffs.iter_mut() {
        *c = c.mul_base(s);
        s = s * shift_inv;
    }
    coeffs
}

/// Evaluate base-or-extension coefficients at a point of the same field
/// type (Horner's method).
pub fn evaluate_at<F: Field>(coeffs: &[F], x: F) -> F {
    coeffs.iter().rev().fold(F::ZERO, |acc, &c| acc * x + c)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ext::Ext;
    use crate::fri::coset_domain;

    fn sample(n: usize) -> Vec<BabyBear> {
        (0..n as u32).map(|i| BabyBear::new(i * i * 31 + 7 * i + 3)).collect()
    }

    #[test]
    fn ntt_matches_direct_evaluation() {
        for log_n in [0, 1, 3, 6] {
            let coeffs = sample(1 << log_n);
            let mut evals = coeffs.clone();
            ntt(&mut evals);
            for (i, &x) in coset_domain(BabyBear::ONE, log_n).iter().enumerate() {
                assert_eq!(evals[i], evaluate_at(&coeffs, x), "n = 2^{log_n}, i = {i}");
            }
        }
    }

    #[test]
    fn intt_inverts_ntt() {
        let coeffs = sample(64);
        let mut values = coeffs.clone();
        ntt(&mut values);
        intt(&mut values);
        assert_eq!(values, coeffs);
    }

    #[test]
    fn coset_evaluation_matches_direct_evaluation_and_inverts() {
        let shift = BabyBear::new(31);
        let coeffs = sample(8);
        let evals = coset_evaluate(&coeffs, shift, 5); // 8 coeffs over 32 points
        for (i, &x) in coset_domain(shift, 5).iter().enumerate() {
            assert_eq!(evals[i], evaluate_at(&coeffs, x));
        }
        let back = coset_interpolate(&evals, shift);
        assert_eq!(&back[..8], &coeffs[..]);
        assert!(back[8..].iter().all(|&c| c == BabyBear::ZERO));
    }

    #[test]
    fn extension_values_transform_too() {
        let coeffs: Vec<Ext> = (0..16u32)
            .map(|i| Ext([BabyBear::new(i), BabyBear::new(i + 1), BabyBear::new(2 * i), BabyBear::new(9)]))
            .collect();
        let shift = BabyBear::new(31);
        let evals = coset_evaluate(&coeffs, shift, 4);
        for (i, &x) in coset_domain(shift, 4).iter().enumerate() {
            assert_eq!(evals[i], evaluate_at(&coeffs, Ext::from_base(x)));
        }
        assert_eq!(coset_interpolate(&evals, shift), coeffs);
    }
}
