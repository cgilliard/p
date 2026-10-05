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

use crate::ext::Ext;
use crate::field::Field;
use crate::fri::domain_generator;
use crate::poseidon2::{BabyBear, add_mod, from_monty, monty_mul, sub_mod, to_monty};

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
mod batch_tests {
    use super::*;

    /// The portable path agrees with whatever `evaluate_batch` picked.
    #[test]
    fn portable_batches_match_the_dispatched_ones() {
        let log_size = 7;
        let polys: Vec<Vec<BabyBear>> = (0..BATCH).map(|c| (0..100).map(|i| BabyBear::new((c * 977 + i * 31) as u32)).collect()).collect();
        let members: Vec<&[BabyBear]> = polys.iter().map(|p| &p[..]).collect();
        let shift = BabyBear::new(31);
        let mut s = BabyBear::ONE;
        let shift_powers: Vec<u32> = (0..100)
            .map(|_| {
                let v = to_monty(s);
                s = s * shift;
                v
            })
            .collect();
        let twiddles = stage_twiddles(log_size);
        assert_eq!(
            evaluate_batch_generic(&members, &shift_powers, &twiddles, log_size),
            evaluate_batch(&members, &shift_powers, &twiddles, log_size)
        );
    }

    /// Not a correctness test. Run with
    /// `cargo test --release -- --ignored --nocapture ntt_speed`.
    #[test]
    #[ignore]
    fn ntt_speed() {
        let log_size = 17;
        let polys: Vec<Vec<BabyBear>> = (0..16).map(|c| (0..1usize << 15).map(|i| BabyBear::new((c * 7 + i * 13) as u32)).collect()).collect();
        let shift = BabyBear::new(31);
        let start = std::time::Instant::now();
        for p in &polys {
            std::hint::black_box(coset_evaluate(p, shift, log_size));
        }
        println!("one at a time: {:.2?} for 16 columns", start.elapsed());
        let start = std::time::Instant::now();
        std::hint::black_box(coset_evaluate_many_serial(&polys, shift, log_size));
        println!("batched, one thread: {:.2?} for 16 columns", start.elapsed());
    }

    #[test]
    fn batched_evaluation_matches_one_at_a_time() {
        let shift = BabyBear::new(31);
        for log_size in [0, 1, 3, 6] {
            let n = 1usize << log_size;
            let polys: Vec<Vec<BabyBear>> = (0..11)
                .map(|c| (0..n.saturating_sub(c % 3).max(1)).map(|i| BabyBear::new((c * 977 + i * 31337 + 5) as u32)).collect())
                .collect();
            let many = coset_evaluate_many(&polys, shift, log_size);
            for (p, evals) in polys.iter().zip(&many) {
                assert_eq!(evals, &coset_evaluate(p, shift, log_size));
            }
            let ext: Vec<Vec<Ext>> = polys.chunks(4).map(|c| (0..c[0].len()).map(|i| Ext([c[0][i], c[0][i] + BabyBear::ONE, c[0][i] * c[0][i], BabyBear::new(i as u32)])).collect()).collect();
            let many = coset_evaluate_many_ext(&ext, shift, log_size);
            for (p, evals) in ext.iter().zip(&many) {
                assert_eq!(evals, &coset_evaluate(p, shift, log_size));
            }
        }
    }
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

// ---- Many columns at once ---------------------------------------------------

/// Columns transformed together: one twiddle serves them all, so the
/// butterflies run across the batch as plain loops (vectorized with AVX2
/// where the CPU has it), in Montgomery form.
const BATCH: usize = 8;

/// `coset_evaluate` of many base-field polynomials (each at most
/// `2^log_size` coefficients) over one coset, batched and in parallel.
pub fn coset_evaluate_many<C: AsRef<[BabyBear]> + Sync>(polys: &[C], shift: BabyBear, log_size: usize) -> Vec<Vec<BabyBear>> {
    evaluate_many(polys, shift, log_size, true).columns()
}

/// Evaluations of many polynomials over one domain, kept as the batched
/// transform leaves them -- `groups[g][k]` holds columns `BATCH·g ..` at
/// point `k` -- so a row reads a few contiguous chunks rather than one
/// value from every column.
pub struct Evaluations {
    groups: Vec<Vec<[BabyBear; BATCH]>>,
    pub width: usize,
    pub len: usize,
}

impl Evaluations {
    /// Append row `k` (every column's value at point `k`) to `out`.
    #[inline]
    pub fn row_into(&self, k: usize, out: &mut Vec<BabyBear>) {
        for (g, rows) in self.groups.iter().enumerate() {
            let take = BATCH.min(self.width - g * BATCH);
            out.extend_from_slice(&rows[k][..take]);
        }
    }

    pub fn get(&self, column: usize, k: usize) -> BabyBear {
        self.groups[column / BATCH][k][column % BATCH]
    }

    pub fn columns(&self) -> Vec<Vec<BabyBear>> {
        (0..self.width).map(|c| (0..self.len).map(|k| self.get(c, k)).collect()).collect()
    }
}

/// `coset_evaluate` of many base-field polynomials, as `Evaluations`.
pub fn coset_evaluate_rows<C: AsRef<[BabyBear]> + Sync>(polys: &[C], shift: BabyBear, log_size: usize, parallel: bool) -> Evaluations {
    evaluate_many(polys, shift, log_size, parallel)
}

/// How many batches `count` columns make: the parallelism one
/// evaluation has.
pub fn batches(count: usize) -> usize {
    count.div_ceil(BATCH)
}

/// `coset_evaluate` of many extension-field polynomials, as
/// `Evaluations` of their components: extension column `j` is base
/// columns `4j .. 4j + 4`.
pub fn coset_evaluate_rows_ext<C: AsRef<[Ext]> + Sync>(polys: &[C], shift: BabyBear, log_size: usize, parallel: bool) -> Evaluations {
    let parts: Vec<Vec<BabyBear>> = polys
        .iter()
        .flat_map(|p| (0..4).map(move |k| p.as_ref().iter().map(|e| e.0[k]).collect()))
        .collect();
    evaluate_many(&parts, shift, log_size, parallel)
}

fn evaluate_many<C: AsRef<[BabyBear]> + Sync>(polys: &[C], shift: BabyBear, log_size: usize, parallel: bool) -> Evaluations {
    let n = 1usize << log_size;
    let longest = polys.iter().map(|p| p.as_ref().len()).max().unwrap_or(0);
    assert!(longest <= n, "more coefficients than evaluation points");
    // Shift powers and per-stage twiddles, in Montgomery form, shared by
    // every batch.
    let mut shift_powers = Vec::with_capacity(longest);
    let mut s = BabyBear::ONE;
    for _ in 0..longest {
        shift_powers.push(to_monty(s));
        s = s * shift;
    }
    let twiddles = stage_twiddles(log_size);
    let group = |g: usize| {
        let members: Vec<&[BabyBear]> = polys[g * BATCH..((g + 1) * BATCH).min(polys.len())].iter().map(|p| p.as_ref()).collect();
        evaluate_batch(&members, &shift_powers, &twiddles, log_size)
    };
    let groups = polys.len().div_ceil(BATCH);
    let groups = if parallel {
        crate::parallel::map_each(groups, group)
    } else {
        (0..groups).map(group).collect()
    };
    Evaluations {
        groups,
        width: polys.len(),
        len: n,
    }
}

/// `coset_evaluate_many` on the calling thread only -- for callers that
/// are already parallel.
pub fn coset_evaluate_many_serial<C: AsRef<[BabyBear]> + Sync>(polys: &[C], shift: BabyBear, log_size: usize) -> Vec<Vec<BabyBear>> {
    evaluate_many(polys, shift, log_size, false).columns()
}

/// `coset_evaluate` of many extension-field polynomials: each is four
/// base-field ones (its coefficients' components), since the transform is
/// linear over the base field.
pub fn coset_evaluate_many_ext<C: AsRef<[Ext]> + Sync>(polys: &[C], shift: BabyBear, log_size: usize) -> Vec<Vec<Ext>> {
    let evals = coset_evaluate_rows_ext(polys, shift, log_size, true).columns();
    evals
        .chunks(4)
        .map(|c| (0..c[0].len()).map(|i| Ext([c[0][i], c[1][i], c[2][i], c[3][i]])).collect())
        .collect()
}

/// Twiddles for every stage of a size-`2^log_size` transform, in
/// Montgomery form: stage `s` (block length `2^s`) uses
/// `table[2^(s-1) - 1 ..][..2^(s-1)]`.
fn stage_twiddles(log_size: usize) -> Vec<u32> {
    let mut table = Vec::with_capacity(1 << log_size);
    for s in 1..=log_size {
        let w_len = domain_generator(s);
        let mut w = BabyBear::ONE;
        for _ in 0..1usize << (s - 1) {
            table.push(to_monty(w));
            w = w * w_len;
        }
    }
    table
}

fn evaluate_batch(members: &[&[BabyBear]], shift_powers: &[u32], twiddles: &[u32], log_size: usize) -> Vec<[BabyBear; BATCH]> {
    #[cfg(target_arch = "x86_64")]
    if std::arch::is_x86_feature_detected!("avx2") {
        // SAFETY: the CPU supports AVX2, checked just above.
        return unsafe { evaluate_batch_avx2(members, shift_powers, twiddles, log_size) };
    }
    evaluate_batch_generic(members, shift_powers, twiddles, log_size)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn evaluate_batch_avx2(members: &[&[BabyBear]], shift_powers: &[u32], twiddles: &[u32], log_size: usize) -> Vec<[BabyBear; BATCH]> {
    evaluate_batch_generic(members, shift_powers, twiddles, log_size)
}

/// Rows per cache block: 2^12 rows of `BATCH` values is 128 KB.
const CACHE_ROWS: usize = 1 << 12;

/// One radix-2 stage (block length `len`) over `rows`.
#[inline(always)]
fn butterflies(rows: &mut [[u32; BATCH]], len: usize, tw: &[u32]) {
    let half = len / 2;
    for block in rows.chunks_mut(len) {
        let (lo, hi) = block.split_at_mut(half);
        for ((a, b), &w) in lo.iter_mut().zip(hi.iter_mut()).zip(tw) {
            for c in 0..BATCH {
                let t = monty_mul(b[c], w);
                let x = a[c];
                a[c] = add_mod(x, t);
                b[c] = sub_mod(x, t);
            }
        }
    }
}

#[inline(always)]
fn evaluate_batch_generic(members: &[&[BabyBear]], shift_powers: &[u32], twiddles: &[u32], log_size: usize) -> Vec<[BabyBear; BATCH]> {
    let n = 1usize << log_size;
    let bits = log_size as u32;
    // rows[i][c]: member c's value i, written straight into bit-reversed
    // position (only the nonzero coefficients need placing).
    let mut rows = vec![[0u32; BATCH]; n];
    for (c, poly) in members.iter().enumerate() {
        for (i, (&v, &sp)) in poly.iter().zip(shift_powers).enumerate() {
            let j = if bits == 0 { 0 } else { i.reverse_bits() >> (usize::BITS - bits) };
            rows[j][c] = monty_mul(to_monty(v), sp);
        }
    }
    // Stages up to `CACHE_ROWS` touch only blocks of that size: run all of
    // them one block at a time, while it's in cache; only the larger
    // stages stream the whole buffer.
    let local = n.min(CACHE_ROWS);
    for block in rows.chunks_mut(local) {
        let (mut len, mut offset) = (2, 0);
        while len <= local {
            butterflies(block, len, &twiddles[offset..offset + len / 2]);
            offset += len / 2;
            len *= 2;
        }
    }
    let (mut len, mut offset) = (2 * local, local - 1);
    while len <= n {
        butterflies(&mut rows, len, &twiddles[offset..offset + len / 2]);
        offset += len / 2;
        len *= 2;
    }
    rows.into_iter().map(|r| r.map(from_monty)).collect()

}
