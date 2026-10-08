//! The degree-4 extension of BabyBear: `BabyBear[x] / (x^4 - 11)`, the
//! same quartic extension Plonky3 uses for this field.
//!
//! BabyBear alone has only ~2^31 elements, which is far too few for the
//! *random challenges* a STARK draws: a cheating prover gets every
//! challenge-dependent check past with probability roughly (degree /
//! field size), and at 2^31 that's nowhere near negligible. Drawing
//! challenges -- FRI folding factors, constraint-combination weights,
//! the out-of-domain point -- from this ~2^124-element extension instead
//! is the standard fix. Trace values themselves stay in BabyBear; only
//! what depends on a challenge lives up here.
//!
//! `x^4 - 11` is irreducible over BabyBear: for a binomial `x^4 - w` over
//! a prime field with `p ≡ 1 (mod 4)` (true here: `p - 1 = 15 · 2^27`),
//! that holds exactly when `w` is not a square, and 11 isn't -- see
//! `eleven_is_not_a_square`.

#![allow(dead_code)]

use crate::poseidon2::{BabyBear, P};

/// The `w` in `x^4 = w`.
const W: BabyBear = BabyBear::new_const(11);

/// An element `c0 + c1·x + c2·x^2 + c3·x^3`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Ext(pub [BabyBear; 4]);

impl Ext {
    pub const ZERO: Ext = Ext([BabyBear::ZERO; 4]);
    pub const ONE: Ext = Ext([BabyBear::ONE, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO]);

    pub fn from_base(value: BabyBear) -> Self {
        Ext([value, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO])
    }

    pub fn add(self, rhs: Self) -> Self {
        let mut out = [BabyBear::ZERO; 4];
        for (i, slot) in out.iter_mut().enumerate() {
            *slot = self.0[i].add(rhs.0[i]);
        }
        Ext(out)
    }

    pub fn sub(self, rhs: Self) -> Self {
        let mut out = [BabyBear::ZERO; 4];
        for (i, slot) in out.iter_mut().enumerate() {
            *slot = self.0[i].sub(rhs.0[i]);
        }
        Ext(out)
    }

    pub fn neg(self) -> Self {
        Ext(self.0.map(BabyBear::neg))
    }

    /// Multiply by a base-field element -- coefficient-wise, much cheaper
    /// than a full extension multiplication.
    pub fn mul_base(self, rhs: BabyBear) -> Self {
        Ext(self.0.map(|c| c.mul(rhs)))
    }

    pub fn mul(self, rhs: Self) -> Self {
        // Schoolbook product into degree <= 6, then fold x^4 = W back down.
        let (a, b) = (self.0, rhs.0);
        let mut wide = [BabyBear::ZERO; 7];
        for i in 0..4 {
            for j in 0..4 {
                wide[i + j] = wide[i + j].add(a[i].mul(b[j]));
            }
        }
        Ext([
            wide[0].add(W.mul(wide[4])),
            wide[1].add(W.mul(wide[5])),
            wide[2].add(W.mul(wide[6])),
            wide[3],
        ])
    }

    pub fn square(self) -> Self {
        self.mul(self)
    }

    pub fn pow(self, mut exp: u128) -> Self {
        let mut base = self;
        let mut acc = Ext::ONE;
        while exp > 0 {
            if exp & 1 == 1 {
                acc = acc.mul(base);
            }
            base = base.square();
            exp >>= 1;
        }
        acc
    }

    /// Multiplicative inverse, via `a^(p^4 - 2)` (the extension's
    /// multiplicative group has order `p^4 - 1`). Slow-ish; anything
    /// inverting many elements at once should use `batch_inverse`.
    /// Zero maps to zero.
    pub fn inverse(self) -> Self {
        let p = P as u128;
        self.pow(p * p * p * p - 2)
    }

    pub fn is_zero(self) -> bool {
        self == Ext::ZERO
    }

    /// Little-endian, coefficient by coefficient: 16 bytes.
    pub fn to_bytes(self) -> [u8; 16] {
        let mut out = [0u8; 16];
        for (i, c) in self.0.iter().enumerate() {
            out[4 * i..4 * i + 4].copy_from_slice(&c.to_bytes());
        }
        out
    }

    pub fn from_bytes(bytes: [u8; 16]) -> Self {
        let mut out = [BabyBear::ZERO; 4];
        for (i, slot) in out.iter_mut().enumerate() {
            *slot = BabyBear::from_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap());
        }
        Ext(out)
    }
}

impl std::ops::Add for Ext {
    type Output = Ext;
    fn add(self, rhs: Self) -> Self {
        Ext::add(self, rhs)
    }
}

impl std::ops::Sub for Ext {
    type Output = Ext;
    fn sub(self, rhs: Self) -> Self {
        Ext::sub(self, rhs)
    }
}

impl std::ops::Mul for Ext {
    type Output = Ext;
    fn mul(self, rhs: Self) -> Self {
        Ext::mul(self, rhs)
    }
}

impl std::ops::Neg for Ext {
    type Output = Ext;
    fn neg(self) -> Self {
        Ext::neg(self)
    }
}

/// Batch inversion over the extension -- see `field::batch_inverse`.
pub fn batch_inverse(values: &[Ext]) -> Vec<Ext> {
    crate::field::batch_inverse(values)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A deterministic spread of extension elements to test identities on.
    fn samples() -> Vec<Ext> {
        let mut out = vec![Ext::ZERO, Ext::ONE, Ext::from_base(BabyBear::new(P - 1))];
        let mut seed = 0x1234_5678u64;
        for _ in 0..20 {
            let mut coeffs = [BabyBear::ZERO; 4];
            for c in coeffs.iter_mut() {
                seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                *c = BabyBear::new((seed >> 33) as u32);
            }
            out.push(Ext(coeffs));
        }
        out
    }

    #[test]
    fn eleven_is_not_a_square() {
        // Euler's criterion: w is a square iff w^((p-1)/2) == 1.
        assert_eq!(W.pow(((P - 1) / 2) as u64), BabyBear::ONE.neg());
        assert_eq!(P % 4, 1);
    }

    #[test]
    fn x_to_the_fourth_is_eleven() {
        let x = Ext([BabyBear::ZERO, BabyBear::ONE, BabyBear::ZERO, BabyBear::ZERO]);
        assert_eq!(x.pow(4), Ext::from_base(W));
    }

    #[test]
    fn multiplication_is_commutative_associative_and_distributive() {
        let s = samples();
        for &a in &s {
            for &b in &s[..6] {
                assert_eq!(a * b, b * a);
                for &c in &s[..4] {
                    assert_eq!((a * b) * c, a * (b * c));
                    assert_eq!(a * (b + c), a * b + a * c);
                }
            }
        }
    }

    #[test]
    fn every_nonzero_element_has_an_inverse() {
        for a in samples().into_iter().filter(|a| !a.is_zero()) {
            assert_eq!(a * a.inverse(), Ext::ONE, "{a:?}");
        }
        assert_eq!(Ext::ZERO.inverse(), Ext::ZERO);
    }

    #[test]
    fn batch_inverse_matches_one_at_a_time() {
        let s = samples();
        let batch = batch_inverse(&s);
        for (a, inv) in s.iter().zip(batch) {
            assert_eq!(inv, a.inverse());
        }
    }

    #[test]
    fn base_field_embeds_faithfully() {
        let a = BabyBear::new(123_456);
        let b = BabyBear::new(987_654_321);
        assert_eq!(Ext::from_base(a) * Ext::from_base(b), Ext::from_base(a * b));
        assert_eq!(Ext(samples()[5].0).mul_base(b), samples()[5] * Ext::from_base(b));
    }

    #[test]
    fn bytes_roundtrip() {
        for a in samples() {
            assert_eq!(Ext::from_bytes(a.to_bytes()), a);
        }
    }
}
