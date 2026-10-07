//! The chain's numeric consensus rules as circuit gadgets, for chain
//! proofs (`chain_step`): **retargeting** (`retarget`, the same rule as
//! `chain::next_retarget`) and **cumulative work** (`add_work`, as
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

/// A number's 16-bit limbs (little-endian), as constants.
fn const_limbs16(b: &mut Builder, v: u64) -> Vec<EVar> {
    (0..4).map(|j| b.const_base(BabyBear::new(((v >> (16 * j)) & 0xffff) as u32))).collect()
}

fn le_bytes(v: u64, n: usize) -> Vec<u8> {
    v.to_le_bytes()[..n].to_vec()
}

/// Bytes of a time span (milliseconds) in the retarget gadget: three
/// 16-bit limbs, room for main's clamp (`600 s × 2015 × 4` ≈ 2^32.2).
const TIME_BYTES: usize = 6;

/// The retarget rule (`chain::next_retarget`) for a block at `height`
/// with timestamp `ts` (four 16-bit limbs, range-checked), given the
/// `target` (32 little-endian bytes) and window start `window_start`
/// (four 16-bit limbs) in effect before it: the target and window start
/// in effect after it.
pub fn retarget(
    b: &mut Builder,
    config: &DifficultyConfig,
    height: EVar,
    ts: &[EVar; 4],
    target: &[EVar],
    window_start: &[EVar; 4],
) -> (Vec<EVar>, [EVar; 4]) {
    let interval = config.interval;
    let expected = config.target_block_time_ms * (interval - 1);
    let (lo, hi) = (expected / config.max_adjustment_factor, expected * config.max_adjustment_factor);
    // Clamped times are `TIME_BYTES` bytes in the gadget.
    assert!(hi < 1 << (8 * TIME_BYTES) && interval >= 2 && interval < 1 << 30, "the retarget parameters must fit the gadget");

    // height = q·interval + r, 0 <= r < interval.
    let h = value(b, height);
    let (q, r) = (witness(b, h / interval), witness(b, h % interval));
    let r_bits = 64 - (interval - 1).leading_zeros() as usize;
    bits_of(b, q, 31);
    bits_of(b, r, r_bits);
    let last = b.const_base(BabyBear::new((interval - 1) as u32));
    let room = b.sub(last, r);
    bits_of(b, room, r_bits);
    let z = BabyBear::ZERO;
    let composed = b.arith(z, Some(q), None, BabyBear::new(interval as u32), z, Some(r), BabyBear::ONE, [z; 4]);
    b.assert_eq(composed, height);
    let starts = is_zero(b, r);
    let at_last = b.sub(r, last);
    let ends = is_zero(b, at_last);

    // The window start: this block's timestamp at a window's first block.
    let window: [EVar; 4] = std::array::from_fn(|j| select(b, starts, window_start[j], ts[j]));

    // Elapsed, saturating at zero, clamped to [lo, hi].
    let (elapsed, backwards) = subtract(b, ts, &window, 16);
    let hi_limbs = const_limbs16(b, hi);
    let lo_limbs = const_limbs16(b, lo);
    let (_, below_hi) = subtract(b, &elapsed, &hi_limbs, 16);
    let (_, below_lo) = subtract(b, &elapsed, &lo_limbs, 16);
    // Limb by limb (the clamp may not fit one element).
    let clamped: Vec<EVar> = (0..4)
        .map(|j| {
            let inner = select(b, below_lo, elapsed[j], lo_limbs[j]);
            let mid = select(b, below_hi, hi_limbs[j], inner);
            select(b, backwards, mid, lo_limbs[j])
        })
        .collect();

    // target · clamped / expected, or all ones if the product overflows.
    let c = (0..4).map(|j| value(b, clamped[j]) << (16 * j)).sum::<u64>();
    let c_bytes = witness_bytes(b, &le_bytes(c, TIME_BYTES));
    for (j, &limb) in clamped.iter().enumerate() {
        if 2 * j < TIME_BYTES {
            let composed = b.arith(z, Some(c_bytes[2 * j + 1]), None, BabyBear::new(256), z, Some(c_bytes[2 * j]), BabyBear::ONE, [z; 4]);
            b.assert_eq(composed, limb);
        } else {
            b.assert_zero(limb);
        }
    }
    let t_bytes = bytes_of(b, target);
    let product = mul_small(&t_bytes, c);
    let p = witness_bytes(b, &product);
    assert_product(b, target, &c_bytes, &[], 0, &p);
    let (quotient, remainder) = div_small(&product, expected);
    let q_bytes = witness_bytes(b, &quotient);
    let r_bytes = witness_bytes(b, &le_bytes(remainder, TIME_BYTES));
    let d_bytes = const_bytes(b, &le_bytes(expected, TIME_BYTES));
    let mut p_out = p.clone();
    while p_out.len() < q_bytes.len() + d_bytes.len() - 1 {
        p_out.push(b.zero());
    }
    assert_product(b, &q_bytes, &d_bytes, &[&r_bytes], 0, &p_out);
    let smaller = less_than(b, &r_bytes, &d_bytes);
    let one = b.one();
    b.assert_eq(smaller, one);
    let high = p[33..].iter().fold(p[32], |acc, &x| b.add(acc, x));
    let fits = is_zero(b, high);
    let all_ones = b.const_base(BabyBear::new(255));
    let next: Vec<EVar> = (0..32)
        .map(|k| {
            let scaled = select(b, fits, all_ones, q_bytes[k]);
            select(b, ends, target[k], scaled)
        })
        .collect();
    (next, window)
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

/// `value · m` for little-endian bytes: 35 bytes.
fn mul_small(value: &[u8], m: u64) -> Vec<u8> {
    let mut out = vec![0u8; value.len() + TIME_BYTES];
    let mut carry: u128 = 0;
    for (k, slot) in out.iter_mut().enumerate() {
        let v = value.get(k).copied().unwrap_or(0) as u128 * m as u128 + carry;
        *slot = v as u8;
        carry = v >> 8;
    }
    out
}

/// `value / d` and `value % d` for little-endian bytes.
fn div_small(value: &[u8], d: u64) -> (Vec<u8>, u64) {
    let mut q = vec![0u8; value.len()];
    let mut rem: u128 = 0;
    for k in (0..value.len()).rev() {
        let cur = (rem << 8) | value[k] as u128;
        q[k] = (cur / d as u128) as u8;
        rem = cur % d as u128;
    }
    (q, rem as u64)
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

    /// The circuit's retarget agrees with the node's, across window
    /// positions and fast, slow, clamped, backwards and overflowing
    /// windows.
    #[test]
    fn retargeting_in_the_circuit_matches_the_chain() {
        // Dev's ten-block windows, and main's 2016 ten-minute blocks (whose
        // clamp needs more than 32 bits); the cases' heights are in units
        // of ten-block windows, scaled to the interval.
        for (interval, target_block_time_ms) in [(10, 60_000), (10, 600_000), (2016, 600_000)] {
        let config = DifficultyConfig {
            pow: crate::pow::Params::TEST,
            initial_target: [0; 32],
            interval,
            target_block_time_ms,
            max_adjustment_factor: 4,
            schedule: crate::prover::DEV_SCHEDULE,
        };
        let easy = crate::block::INITIAL_MAX_HASH;
        let hard = crate::pow::max_hash_with_leading_zero_bits(40);
        let cases: [([u8; 32], u64, u64, u64); 9] = [
            (easy, 5, 1_000_000, 900_000),           // mid-window: nothing changes
            (easy, 10, 2_000_000, 900_000),          // a window starts
            (hard, 19, 1_100_000, 1_000_000),        // fast window: clamped harder
            (hard, 19, 3_000_000, 1_000_000),        // slow: easier, within the clamp
            (hard, 19, 900_000_000, 1_000_000),      // very slow: clamped easier
            (hard, 19, 500_000, 1_000_000),          // timestamps went backwards
            ([0xff; 32], 9, 900_000_000, 0),         // overflow: all ones
            (easy, 9, 1_000_000_000_000, 999_999_999_000), // big timestamps
            (hard, 0, 7, 0),                          // the first block
        ];
        let scale_time = target_block_time_ms * (interval - 1) / (60_000 * 9);
        for (target, height, ts, ws) in cases {
            // The same position in the window, and the same pace.
            let height = height / 10 * interval + if height % 10 == 9 { interval - 1 } else { height % 10 };
            let (ts, ws) = (ts * scale_time, ws * scale_time);
            let (expected_target, expected_ws) = crate::chain::next_retarget(&config, (target, ws), height, ts);
            let mut b = Builder::new();
            let h = witness(&mut b, height);
            let ts_cells = limbs(&mut b, ts);
            let ws_cells = limbs(&mut b, ws);
            let t = witness_bytes(&mut b, &le(target));
            let (next, window) = retarget(&mut b, &config, h, &ts_cells, &t, &ws_cells);
            assert_eq!(bytes_of(&b, &next), le(expected_target), "height {height}, ts {ts}, ws {ws}");
            assert_eq!(limbs_value(&b, &window), expected_ws);
            check(b);
        }
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
