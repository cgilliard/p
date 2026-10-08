//! What code generic over "a field element" needs -- implemented by both
//! `BabyBear` and its extension `Ext`. A STARK evaluates the same
//! constraints twice: over BabyBear, row by row, when proving, and over
//! the extension, at one random point, when verifying. Writing them once,
//! against this trait, is what keeps those two from ever disagreeing.

#![allow(dead_code)]

use crate::ext::Ext;
use crate::poseidon2::BabyBear;

pub trait Field:
    Copy
    + PartialEq
    + std::fmt::Debug
    + std::ops::Add<Output = Self>
    + std::ops::Sub<Output = Self>
    + std::ops::Mul<Output = Self>
    + std::ops::Neg<Output = Self>
{
    const ZERO: Self;
    const ONE: Self;

    fn from_base(value: BabyBear) -> Self;

    fn mul_base(self, rhs: BabyBear) -> Self;

    /// Multiplicative inverse; zero maps to zero.
    fn inverse(self) -> Self;

    fn square(self) -> Self {
        self * self
    }
}

impl Field for BabyBear {
    const ZERO: Self = BabyBear::ZERO;
    const ONE: Self = BabyBear::ONE;

    fn from_base(value: BabyBear) -> Self {
        value
    }

    fn mul_base(self, rhs: BabyBear) -> Self {
        self * rhs
    }

    fn inverse(self) -> Self {
        BabyBear::inverse(self)
    }
}

impl Field for Ext {
    const ZERO: Self = Ext::ZERO;
    const ONE: Self = Ext::ONE;

    fn from_base(value: BabyBear) -> Self {
        Ext::from_base(value)
    }

    fn mul_base(self, rhs: BabyBear) -> Self {
        Ext::mul_base(self, rhs)
    }

    fn inverse(self) -> Self {
        Ext::inverse(self)
    }
}

/// Invert every element of `values` with one real inversion
/// (Montgomery's trick): running prefix products, invert the last, then
/// unwind. Zeros stay zero and don't disturb the rest.
pub fn batch_inverse<F: Field>(values: &[F]) -> Vec<F> {
    let mut prefix = Vec::with_capacity(values.len());
    let mut acc = F::ONE;
    for &v in values {
        prefix.push(acc);
        if v != F::ZERO {
            acc = acc * v;
        }
    }
    let mut inv = acc.inverse();
    let mut out = vec![F::ZERO; values.len()];
    for i in (0..values.len()).rev() {
        if values[i] == F::ZERO {
            continue;
        }
        out[i] = inv * prefix[i];
        inv = inv * values[i];
    }
    out
}
