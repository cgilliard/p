//! The chain's numeric consensus rules as circuit gadgets, for chain
//! proofs (`chain_step`): **retargeting** (`retarget`, ASERT, the same
//! rule as `chain::next_retarget`) and **cumulative work** (`add_work`, as
//! `pow::work_for_target`, summed).
//!
//! Both are 256-bit arithmetic. Numbers are little-endian **bytes**, each
//! a cell below 256 (range-checked where they enter), so limb products
//! (`assert_product`) stay far below the field's 31 bits: a column of up
//! to 35 byte products plus carries is under 2^22. Division is checked,
//! not computed: the quotient and remainder are witnesses satisfying
//! `q·d + r = n` with `r < d`.

#![allow(dead_code)]

use crate::chain::DifficultyConfig;
use crate::circuit::{Builder, EVar};
use crate::ext::Ext;
use crate::poseidon2::BabyBear;
use crate::state_circuit::bits_of;

fn value(b: &Builder, v: EVar) -> u64 {
    b.ext_value(v).0[0].value() as u64
}

fn witness(b: &mut Builder, v: u64) -> EVar {
    b.witness_ext(Ext::from_base(BabyBear::new(v as u32)))
}

/// A witness byte, range-checked.
pub fn witness_byte(b: &mut Builder, v: u64) -> EVar {
    let cell = witness(b, v);
    bits_of(b, cell, 8);
    cell
}

pub fn witness_bytes(b: &mut Builder, bytes: &[u8]) -> Vec<EVar> {
    bytes.iter().map(|&v| witness_byte(b, v as u64)).collect()
}

pub fn const_bytes(b: &mut Builder, bytes: &[u8]) -> Vec<EVar> {
    bytes.iter().map(|&v| b.const_base(BabyBear::new(v as u32))).collect()
}

/// Cells' values as little-endian bytes.
pub fn bytes_of(b: &Builder, cells: &[EVar]) -> Vec<u8> {
    cells.iter().map(|&c| value(b, c) as u8).collect()
}

/// `a` where `s` is 0, `x` where `s` is 1.
pub fn select(b: &mut Builder, s: EVar, a: EVar, x: EVar) -> EVar {
    let d = b.sub(x, a);
    b.mul_add(s, d, a)
}

/// 1 if `x` is zero, else 0.
pub fn is_zero(b: &mut Builder, x: EVar) -> EVar {
    let v = b.ext_value(x);
    let inv = if v.is_zero() { Ext::ZERO } else { v.inverse() };
    let inv = b.witness_ext(inv);
    let product = b.mul(x, inv);
    let one = b.one();
    let e = b.sub(one, product);
    let zero_check = b.mul(x, e);
    b.assert_zero(zero_check);
    e
}

/// Assert `a·m + Σ addends + k == out` exactly, all little-endian byte
/// limbs (`out` at least as long as the product). Column by column, with
/// range-checked carries.
pub fn assert_product(b: &mut Builder, a: &[EVar], m: &[EVar], addends: &[&[EVar]], k: u32, out: &[EVar]) {
    assert!(out.len() + 1 >= a.len() + m.len(), "the product doesn't fit");
    let (z, o) = (BabyBear::ZERO, BabyBear::ONE);
    let mut carry: Option<EVar> = None;
    // The largest a column can be (every limb 255), so each carry's range
    // check is only as wide as it has to be.
    let mut carry_max: u64 = 0;
    for (col, &out_col) in out.iter().enumerate() {
        let mut acc = if col == 0 && k > 0 { b.const_base(BabyBear::new(k)) } else { b.zero() };
        let mut column_max = if col == 0 { k as u64 } else { 0 } + carry_max;
        for (i, &ai) in a.iter().enumerate() {
            if let Some(j) = col.checked_sub(i)
                && let Some(&mj) = m.get(j)
            {
                acc = b.mul_add(ai, mj, acc);
                column_max += 255 * 255;
            }
        }
        column_max += 255 * addends.iter().filter(|add| col < add.len()).count() as u64;
        carry_max = column_max / 256;
        let carry_bits = (64 - carry_max.leading_zeros() as usize).max(1);
        for add in addends {
            if let Some(&x) = add.get(col) {
                acc = b.add(acc, x);
            }
        }
        if let Some(c) = carry {
            acc = b.add(acc, c);
        }
        let carry_value = value(b, acc).saturating_sub(value(b, out_col)) / 256;
        let c = witness(b, carry_value);
        bits_of(b, c, carry_bits);
        let rhs = b.arith(z, Some(c), None, BabyBear::new(256), z, Some(out_col), o, [z; 4]);
        b.assert_eq(acc, rhs);
        carry = Some(c);
    }
    if let Some(c) = carry {
        b.assert_zero(c);
    }
}

/// `x - y` for little-endian limbs of `bits` bits each (the same count):
/// the difference's limbs (range-checked) and the final borrow -- 1 if
/// and only if `x < y`.
pub fn subtract(b: &mut Builder, x: &[EVar], y: &[EVar], bits: usize) -> (Vec<EVar>, EVar) {
    let (z, o) = (BabyBear::ZERO, BabyBear::ONE);
    let base = 1i64 << bits;
    let mut borrow = b.zero();
    let mut diff = Vec::with_capacity(x.len());
    for (&xi, &yi) in x.iter().zip(y) {
        let raw = value(b, xi) as i64 - value(b, yi) as i64 - value(b, borrow) as i64;
        let (d, out) = if raw < 0 { (raw + base, 1) } else { (raw, 0) };
        let d = witness(b, d as u64);
        bits_of(b, d, bits);
        let out = witness(b, out);
        bits_of(b, out, 1);
        // x - y - borrow + base·out == d
        let t = b.sub(xi, yi);
        let t = b.sub(t, borrow);
        let t = b.arith(z, Some(out), None, BabyBear::new(base as u32), z, Some(t), o, [z; 4]);
        b.assert_eq(t, d);
        diff.push(d);
        borrow = out;
    }
    (diff, borrow)
}

/// `x < y`, bytes.
pub fn less_than(b: &mut Builder, x: &[EVar], y: &[EVar]) -> EVar {
    subtract(b, x, y, 8).1
}

/// `v`'s low `n` little-endian bytes.
fn le_bytes128(v: u128, n: usize) -> Vec<u8> {
    v.to_le_bytes()[..n].to_vec()
}

/// Four 16-bit limbs (range-checked) as eight bytes: witnesses, composing
/// to the limbs.
fn limb_bytes(b: &mut Builder, limbs: &[EVar; 4]) -> Vec<EVar> {
    let z = BabyBear::ZERO;
    let mut bytes = Vec::with_capacity(8);
    for &limb in limbs {
        let v = value(b, limb);
        let (lo, hi) = (witness_byte(b, v & 0xff), witness_byte(b, v >> 8));
        let composed = b.arith(z, Some(hi), None, BabyBear::new(256), z, Some(lo), BabyBear::ONE, [z; 4]);
        b.assert_eq(composed, limb);
        bytes.extend([lo, hi]);
    }
    bytes
}

/// The retarget rule (`chain::next_retarget`: ASERT, `chain::asert`) for
/// a block after the first, at the height whose bits are `height_bits`
/// (31, lowest first, canonical) with timestamp `ts` (four 16-bit limbs,
/// range-checked), the first block's timestamp being `anchor` (four
/// 16-bit limbs): the target in effect after it, 32 little-endian bytes.
///
/// `behind` (`asert`'s) is made non-negative by adding `C = half_life ·
/// 2^k`, at least any `height · target_block_time` (the timestamp is past
/// the anchor's): that adds exactly `2^(k+16)` to `e`, so `2^k` to the
/// whole halvings and nothing to the fraction. Then the fraction's
/// factor (the cubic, in bytes), `initial_target · factor`, and the
/// shift by `halvings - 16` bits: a shift by up to 7 bits (a small
/// multiplier) and then a barrel shift by whole bytes, with everything
/// below the result's bytes dropped (rounding down) and anything above
/// them overflow. Shifts out of the barrel's range are the clamps.
pub fn retarget(b: &mut Builder, config: &DifficultyConfig, height_bits: &[EVar], ts: &[EVar; 4], anchor: &[EVar; 4]) -> Vec<EVar> {
    use crate::state_circuit::from_bits;
    let (z, o) = (BabyBear::ZERO, BabyBear::ONE);
    let (block_time, half_life) = (config.target_block_time_ms, config.half_life_ms);
    assert!(height_bits.len() == 31 && block_time < 1 << 32 && (1..1 << 32).contains(&half_life), "the retarget parameters must fit the gadget");
    let mut k = 9;
    while (half_life as u128) << k < (block_time as u128) << 31 {
        k += 1;
    }
    let offset = (half_life as u128) << k;
    let one = b.one();
    let zero = b.zero();
    let limbs_value = |b: &Builder, l: &[EVar; 4]| (0..4).map(|j| value(b, l[j]) << (16 * j)).sum::<u64>();
    let (t, a) = (limbs_value(b, ts), limbs_value(b, anchor));
    let h = (0..31).map(|i| value(b, height_bits[i]) << i).sum::<u64>();

    // n = t + C - anchor - height · block_time, in 10 bytes.
    let ts_bytes = limb_bytes(b, ts);
    let anchor_bytes = limb_bytes(b, anchor);
    let h_bytes: Vec<EVar> = height_bits.chunks(8).map(|c| from_bits(b, c)).collect();
    let sum = t as u128 + offset;
    let sum_cells = witness_bytes(b, &le_bytes128(sum, 10));
    let offset_cells = const_bytes(b, &le_bytes128(offset, 10));
    assert_product(b, &ts_bytes, &[one], &[&offset_cells], 0, &sum_cells);
    let n = sum.checked_sub(a as u128 + block_time as u128 * h as u128).expect("a timestamp before the schedule's start");
    let n_cells = witness_bytes(b, &le_bytes128(n, 10));
    let block_time_cells = const_bytes(b, &le_bytes128(block_time as u128, 4));
    assert_product(b, &h_bytes, &block_time_cells, &[&n_cells, &anchor_bytes], 0, &sum_cells);

    // n · 2^16 = e · half_life + r, r < half_life.
    let (e, r) = ((n << 16) / half_life as u128, (n << 16) % half_life as u128);
    let e_cells = witness_bytes(b, &le_bytes128(e, 12));
    let r_cells = witness_bytes(b, &le_bytes128(r, 4));
    let half_life_cells = const_bytes(b, &le_bytes128(half_life as u128, 4));
    let mut shifted = vec![zero, zero];
    shifted.extend(&n_cells);
    shifted.resize(15, zero);
    assert_product(b, &e_cells, &half_life_cells, &[&r_cells], 0, &shifted);
    let smaller = less_than(b, &r_cells, &half_life_cells);
    b.assert_eq(smaller, one);

    // factor = 2^16 + (c1·f + c2·f² + c3·f³ + 2^47) >> 48.
    let f = (e & 0xffff) as u128;
    let f_cells = &e_cells[..2];
    let f2 = witness_bytes(b, &le_bytes128(f * f, 4));
    assert_product(b, f_cells, f_cells, &[], 0, &f2);
    let f3 = witness_bytes(b, &le_bytes128(f * f * f, 6));
    assert_product(b, &f2, f_cells, &[], 0, &f3);
    let [c1, c2, c3] = crate::chain::ASERT_POLY.map(|c| c as u128);
    let mut terms = Vec::new();
    for (c, c_len, (power, value)) in [(c1, 6, (f_cells, f)), (c2, 4, (&f2[..], f * f)), (c3, 2, (&f3[..], f * f * f))] {
        assert!(c < 1 << (8 * c_len));
        let c_cells = const_bytes(b, &le_bytes128(c, c_len));
        let term = witness_bytes(b, &le_bytes128(c * value, 9));
        assert_product(b, power, &c_cells, &[], 0, &term);
        terms.push(term);
    }
    let poly = c1 * f + c2 * f * f + c3 * f * f * f + (1 << 47);
    let poly_cells = witness_bytes(b, &le_bytes128(poly, 9));
    let half = const_bytes(b, &le_bytes128(1 << 47, 6));
    assert_product(b, &terms[0], &[one], &[&terms[1], &terms[2], &half], 0, &poly_cells);
    let factor = (1 << 16) + (poly >> 48);
    let factor_cells = witness_bytes(b, &le_bytes128(factor, 3));
    let base_factor = const_bytes(b, &le_bytes128(1 << 16, 3));
    assert_product(b, &poly_cells[6..], &[one], &[&base_factor], 0, &factor_cells);

    // x = initial_target · factor, 35 bytes.
    let target_le: Vec<u8> = config.initial_target.iter().rev().copied().collect();
    let target_cells = const_bytes(b, &target_le);
    let x = mul_small(&target_le, factor as u64);
    let x_cells = witness_bytes(b, &x[..35]);
    assert_product(b, &target_cells, &factor_cells, &[], 0, &x_cells);

    // The shift: u = halvings - 16 + 296 = (e >> 16) - (2^k - 280), from
    // 0 to 1023 within range; below, the result rounds to 0 (so 1), and
    // above, it overflows.
    let base = (1u128 << k) - 280;
    let halvings = &e_cells[2..];
    let (base_cells, top_cells) = (const_bytes(b, &le_bytes128(base, 10)), const_bytes(b, &le_bytes128(base + 1024, 10)));
    let (u_cells, under) = subtract(b, halvings, &base_cells, 8);
    let below_top = less_than(b, halvings, &top_cells);
    let mut u_bits = bits_of(b, u_cells[0], 8);
    u_bits.extend(bits_of(b, u_cells[1], 8));
    // Up to 7 bits: x · 2^(u mod 8), 36 bytes.
    let mut m = one;
    for (i, &bit) in u_bits[..3].iter().enumerate() {
        let factor = b.arith(z, Some(bit), None, BabyBear::new((1 << (1 << i)) - 1), z, Some(one), o, [z; 4]);
        m = b.mul(m, factor);
    }
    let y_bytes = mul_small(&x[..35], 1 << (value(b, u_bits[0]) + 2 * value(b, u_bits[1]) + 4 * value(b, u_bits[2])));
    let y_cells = witness_bytes(b, &y_bytes[..36]);
    assert_product(b, &x_cells, &[m], &[], 0, &y_cells);
    // Then by u >> 3 whole bytes: 7 stages of 1, 2, ... 64 bytes (`None`
    // is a known zero).
    const LEN: usize = 36 + 127;
    let mut cells: Vec<Option<EVar>> = y_cells.iter().map(|&c| Some(c)).chain(std::iter::repeat(None)).take(LEN).collect();
    for (i, &bit) in u_bits[3..10].iter().enumerate() {
        let by = 1 << i;
        cells = (0..LEN)
            .map(|j| {
                let from = if j >= by { cells[j - by] } else { None };
                match (cells[j], from) {
                    (None, None) => None,
                    (Some(stay), None) => {
                        let moved = b.mul(bit, stay);
                        Some(b.sub(stay, moved))
                    }
                    (None, Some(from)) => Some(b.mul(bit, from)),
                    (Some(stay), Some(from)) => Some(select(b, bit, stay, from)),
                }
            })
            .collect();
    }
    // Bytes 37.. 69 are the result; any above, overflow.
    let mut high = zero;
    for &cell in cells[69..].iter().flatten() {
        high = b.add(high, cell);
    }
    let fits = is_zero(b, high);
    let result: Vec<EVar> = cells[37..69].iter().map(|c| c.unwrap_or(zero)).collect();
    let mut low = zero;
    for &cell in &result {
        low = b.add(low, cell);
    }
    let vanished = is_zero(b, low);
    let not_under = b.sub(one, under);
    let ok = b.mul(not_under, below_top);
    let ok = b.mul(ok, fits);
    let all_ones = b.const_base(BabyBear::new(255));
    (0..32)
        .map(|k| {
            let least = if k == 0 { one } else { zero };
            let r = select(b, vanished, result[k], least);
            let r = select(b, ok, all_ones, r);
            select(b, under, r, least)
        })
        .collect()
}

/// `work + work_for_target(target)`, all 32 little-endian bytes: the
/// cumulative work after a block mined at `target`. (The work of a target
/// is `⌊(2^256 - 1 - t) / (t + 1)⌋ + 1`; `t = 0` can't be mined, and isn't
/// handled.)
pub fn add_work(b: &mut Builder, target: &[EVar], work: &[EVar]) -> Vec<EVar> {
    let t = bytes_of(b, target);
    let mut t1 = t.clone();
    t1.push(0);
    for byte in t1.iter_mut() {
        let (v, carry) = byte.overflowing_add(1);
        *byte = v;
        if !carry {
            break;
        }
    }
    let t1_cells = witness_bytes(b, &t1);
    let one = b.one();
    assert_product(b, target, &[one], &[], 1, &t1_cells);
    let not_t: Vec<EVar> = target
        .iter()
        .map(|&x| {
            let negated = b.scale(x, -BabyBear::ONE);
            b.add_base(negated, BabyBear::new(255))
        })
        .collect();
    // q = ⌊not(t) / (t + 1)⌋, r the rest.
    let (q, r) = if t1[32] == 1 {
        (vec![0u8; 32], vec![0u8; 33]) // t is all ones: not(t) = 0
    } else {
        let to_be = |le: &[u8]| -> [u8; 32] { std::array::from_fn(|i| le[31 - i]) };
        let not_be: [u8; 32] = to_be(&t.iter().map(|x| 255 - x).collect::<Vec<_>>());
        let (q_be, r_be) = crate::pow::divmod256(not_be, to_be(&t1[..32]));
        let q: Vec<u8> = q_be.iter().rev().copied().collect();
        let mut r: Vec<u8> = r_be.iter().rev().copied().collect();
        r.push(0);
        (q, r)
    };
    let q_cells = witness_bytes(b, &q);
    let r_cells = witness_bytes(b, &r);
    let mut out = not_t.clone();
    while out.len() < q_cells.len() + t1_cells.len() - 1 {
        out.push(b.zero());
    }
    assert_product(b, &q_cells, &t1_cells, &[&r_cells], 0, &out);
    let smaller = less_than(b, &r_cells, &t1_cells);
    b.assert_eq(smaller, one);
    // work + q + 1.
    let w = bytes_of(b, work);
    let mut sum = vec![0u8; 32];
    let mut carry = 1u32;
    for k in 0..32 {
        let v = w[k] as u32 + q[k] as u32 + carry;
        sum[k] = v as u8;
        carry = v >> 8;
    }
    let sum_cells = witness_bytes(b, &sum);
    assert_product(b, &q_cells, &[one], &[work], 1, &sum_cells);
    sum_cells
}

/// `value · m` for little-endian bytes, 8 bytes longer.
fn mul_small(value: &[u8], m: u64) -> Vec<u8> {
    let mut out = vec![0u8; value.len() + 8];
    let mut carry: u128 = 0;
    for (k, slot) in out.iter_mut().enumerate() {
        let v = value.get(k).copied().unwrap_or(0) as u128 * m as u128 + carry;
        *slot = v as u8;
        carry = v >> 8;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark;
    use crate::transcript::Transcript;

    const PARAMS: stark::Params = stark::Params {
        log_blowup: 1,
        num_queries: 4,
        grinding_bits: 0,
        hiding: false,
    };

    fn check(b: Builder) {
        let circuit = b.finish();
        let air = circuit.air(&PARAMS);
        let mut t = Transcript::new(b"chain rules test");
        let challenges: Vec<Ext> = (0..2).map(|_| t.challenge_ext(b"c")).collect();
        stark::check(&air, &circuit.witness, &challenges).unwrap();
    }

    fn le(be: [u8; 32]) -> Vec<u8> {
        be.iter().rev().copied().collect()
    }

    fn limbs(b: &mut Builder, v: u64) -> [EVar; 4] {
        std::array::from_fn(|j| {
            let cell = witness(b, (v >> (16 * j)) & 0xffff);
            bits_of(b, cell, 16);
            cell
        })
    }

    fn limbs_value(b: &Builder, l: &[EVar; 4]) -> u64 {
        (0..4).map(|j| value(b, l[j]) << (16 * j)).sum()
    }

    /// The circuit's retarget agrees with the node's (`chain::asert`):
    /// on schedule, behind and ahead by whole and fractional half-lives,
    /// at the edges of the shifts it computes and past them (clamped to
    /// all ones, or to 1).
    fn retargeting_matches(target_block_time_ms: u64, half_life_ms: u64, initial_target: [u8; 32]) {
        let config = DifficultyConfig {
            pow: crate::pow::Params::TEST,
            initial_target,
            target_block_time_ms,
            half_life_ms,
            schedule: crate::prover::DEV_SCHEDULE,
        };
        let anchor = 1_791_000_000_000u64;
        let (t, hl) = (target_block_time_ms as i128, half_life_ms as i128);
        // (height, how far behind schedule) -- in half-lives, scaled by
        // 1/12.
        let mut cases: Vec<(u64, i128)> = vec![(1, 0), (5, 12), (5, -12), (100, 4), (100, -7), (100, 17), (1 << 20, 30), (crate::poseidon2::P as u64 - 1, 0)];
        for halvings in [-298, -296, -290, -281, -280, -3, -1, 1, 3, 8, 16, 19, 20, 21, 22, 23, 24, 200, 233, 254, 256, 727, 728] {
            cases.push((1 << 25, 12 * halvings));
        }
        for (height, twelfths) in cases {
            let behind = twelfths * hl / 12;
            let Ok(ts) = u64::try_from(anchor as i128 + t * height as i128 + behind) else { continue };
            if ts <= anchor {
                continue;
            }
            let expected = crate::chain::asert(&config, anchor, height, ts);
            let mut b = Builder::new();
            let h = witness(&mut b, height);
            let height_bits = crate::state_circuit::canonical_bits(&mut b, h);
            let ts_cells = limbs(&mut b, ts);
            let anchor_cells = limbs(&mut b, anchor);
            let next = retarget(&mut b, &config, &height_bits, &ts_cells, &anchor_cells);
            assert_eq!(bytes_of(&b, &next), le(expected), "height {height}, {twelfths}/12 half-lives behind");
            check(b);
        }
    }

    #[test]
    fn retargeting_in_the_circuit_matches_the_chain_on_main() {
        retargeting_matches(600_000, 2 * 24 * 3_600_000, crate::pow::max_hash_with_leading_zero_bits(23));
    }

    #[test]
    fn retargeting_in_the_circuit_matches_the_chain_on_dev() {
        retargeting_matches(10_000, 600_000, crate::pow::max_hash_with_leading_zero_bits(20));
    }

    #[test]
    fn retargeting_in_the_circuit_matches_the_chain_in_tests() {
        retargeting_matches(10, 100, crate::block::INITIAL_MAX_HASH);
    }

    /// Anchor targets that overflow at once, and that round to nothing.
    #[test]
    fn retargeting_in_the_circuit_matches_the_chain_at_extreme_targets() {
        let mut tiny = [0u8; 32];
        tiny[31] = 3;
        retargeting_matches(600_000, 2 * 24 * 3_600_000, tiny);
        retargeting_matches(600_000, 2 * 24 * 3_600_000, [0xff; 32]);
    }

    /// A far future timestamp: the most behind schedule a chain can be.
    #[test]
    fn retargeting_in_the_circuit_takes_any_timestamp() {
        let config = DifficultyConfig::for_tests();
        for ts in [u64::MAX, u64::MAX / 3] {
            let mut b = Builder::new();
            let h = witness(&mut b, 7);
            let height_bits = crate::state_circuit::canonical_bits(&mut b, h);
            let ts_cells = limbs(&mut b, ts);
            let anchor_cells = limbs(&mut b, 1);
            let next = retarget(&mut b, &config, &height_bits, &ts_cells, &anchor_cells);
            assert_eq!(bytes_of(&b, &next), le(crate::chain::asert(&config, 1, 7, ts)));
            check(b);
        }
    }

    /// The circuit's cumulative work agrees with `pow::work_for_target`.
    #[test]
    fn work_in_the_circuit_matches_the_chain() {
        let start = crate::pow::work_for_target(crate::pow::max_hash_with_leading_zero_bits(30));
        for target in [crate::block::INITIAL_MAX_HASH, crate::pow::max_hash_with_leading_zero_bits(37), [0xff; 32], {
            let mut t = [0u8; 32];
            t[31] = 1;
            t
        }] {
            let expected = crate::pow::add256(start, crate::pow::work_for_target(target));
            let mut b = Builder::new();
            let t = witness_bytes(&mut b, &le(target));
            let w = witness_bytes(&mut b, &le(start));
            let sum = add_work(&mut b, &t, &w);
            assert_eq!(bytes_of(&b, &sum), le(expected));
            check(b);
        }
    }

    #[test]
    #[should_panic(expected = "assertion fails")]
    fn a_wrong_quotient_is_refused() {
        // 1000 / 7: claim 141 r 13 (13 isn't below 7).
        let mut b = Builder::new();
        let n = witness_bytes(&mut b, &[0xe8, 0x03]);
        let q = witness_bytes(&mut b, &[141, 0]);
        let r = witness_bytes(&mut b, &[13, 0]);
        let d = const_bytes(&mut b, &[7, 0]);
        let mut out = n.clone();
        out.push(b.zero());
        assert_product(&mut b, &q, &d, &[&r], 0, &out);
        let smaller = less_than(&mut b, &r, &d);
        let one = b.one();
        b.assert_eq(smaller, one);
    }
}
