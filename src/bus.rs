//! A LogUp "bus": wires values between arbitrary, distant rows of a
//! STARK trace -- or between the trace and public data -- with one
//! running sum, using the two-phase STARK's auxiliary columns.
//!
//! Each row may *send* or *receive* tuples of field values. With
//! challenges `gamma` and `beta` (drawn after the main trace is
//! committed), a tuple `v` gets the fingerprint `gamma - sum_j beta^j·v_j`,
//! and an interaction of multiplicity `m` (positive to send, negative to
//! receive, zero for "not this row") contributes `m / fingerprint`. The
//! bus balances -- every sent tuple was received exactly as often -- only
//! if the contributions sum to what the public side expects (zero for a
//! closed bus); with `gamma`, `beta` random, an unbalanced bus hits that
//! sum only with negligible probability (the LogUp argument).
//!
//! # Columns and constraints
//!
//! One auxiliary helper column per interaction slot, `h_k = m_k /
//! fingerprint_k`, enforced as `h_k · fingerprint_k = m_k`; and one
//! running-sum column, `acc' = acc + sum_k h_k`, starting at zero. Both
//! constraints are degree `max(2, degree of m_k)`. The running sum's final
//! value must equal `public_sum` of whatever the verifier contributes.
//!
//! Transition constraints don't cover the last row, so an AIR using a
//! bus must not place interactions there (its multiplicities must be zero
//! on the last row) -- they would simply be ignored.

#![allow(dead_code)]

use crate::ext::Ext;
use crate::field::{Field, batch_inverse};
use crate::poseidon2::BabyBear;
use crate::stark::{AuxBoundary, AuxFrame};

/// The challenges a bus uses: `gamma`, then `beta`.
pub const NUM_CHALLENGES: usize = 2;

/// One send or receive at a row.
#[derive(Clone, Debug)]
pub struct Interaction<F> {
    /// Positive to send, negative to receive, zero for none.
    pub multiplicity: F,
    pub values: Vec<F>,
}

/// A bus with a fixed number of interaction slots per row, whose
/// auxiliary columns start at `aux_offset` among the AIR's auxiliary
/// columns, and whose challenges start at `challenge_offset`.
#[derive(Clone, Copy, Debug)]
pub struct Bus {
    pub slots: usize,
    pub aux_offset: usize,
    pub challenge_offset: usize,
}

/// `gamma - sum_j beta^j · values_j`.
pub fn fingerprint<F: Field>(values: &[F], gamma: F, beta: F) -> F {
    let mut acc = F::ZERO;
    let mut power = F::ONE;
    for &v in values {
        acc = acc + power * v;
        power = power * beta;
    }
    gamma - acc
}

impl Bus {
    pub fn num_aux_columns(&self) -> usize {
        self.slots + 1
    }

    pub fn num_constraints(&self) -> usize {
        self.slots + 1
    }

    fn running_sum_column(&self) -> usize {
        self.aux_offset + self.slots
    }

    fn challenges<F: Field>(&self, challenges: &[F]) -> (F, F) {
        (challenges[self.challenge_offset], challenges[self.challenge_offset + 1])
    }

    /// The auxiliary columns for a trace of `n` rows, where `rows(i)`
    /// gives row `i`'s interactions (exactly `slots` of them).
    pub fn aux_trace(
        &self,
        n: usize,
        rows: impl Fn(usize) -> Vec<Interaction<BabyBear>>,
        challenges: &[Ext],
    ) -> Vec<Vec<Ext>> {
        let (gamma, beta) = self.challenges(challenges);
        let mut multiplicities = vec![Vec::with_capacity(n); self.slots];
        let mut fingerprints = vec![Vec::with_capacity(n); self.slots];
        for i in 0..n {
            let interactions = rows(i);
            assert_eq!(interactions.len(), self.slots, "row {i} must have exactly {} interactions", self.slots);
            for (k, interaction) in interactions.into_iter().enumerate() {
                let values: Vec<Ext> = interaction.values.iter().map(|&v| Ext::from_base(v)).collect();
                multiplicities[k].push(Ext::from_base(interaction.multiplicity));
                fingerprints[k].push(fingerprint(&values, gamma, beta));
            }
        }
        let mut columns: Vec<Vec<Ext>> = (0..self.slots)
            .map(|k| {
                batch_inverse(&fingerprints[k])
                    .into_iter()
                    .zip(&multiplicities[k])
                    .map(|(inv, &m)| inv * m)
                    .collect()
            })
            .collect();
        let mut sum = vec![Ext::ZERO; n];
        for i in 1..n {
            sum[i] = sum[i - 1] + (0..self.slots).map(|k| columns[k][i - 1]).fold(Ext::ZERO, |a, b| a + b);
        }
        columns.push(sum);
        columns
    }

    /// The bus's constraints at one row, written to `out`
    /// (`num_constraints` of them); `interactions` are this row's, in
    /// slot order.
    pub fn eval<F: Field>(&self, interactions: &[Interaction<F>], frame: &AuxFrame<F>, out: &mut [F]) {
        let (gamma, beta) = self.challenges(frame.challenges);
        let mut total = F::ZERO;
        for (k, interaction) in interactions.iter().enumerate() {
            let h = frame.aux_current[self.aux_offset + k];
            out[k] = h * fingerprint(&interaction.values, gamma, beta) - interaction.multiplicity;
            total = total + h;
        }
        let acc = self.running_sum_column();
        out[self.slots] = frame.aux_next[acc] - frame.aux_current[acc] - total;
    }

    /// The running sum's two boundaries: zero on the first row, and
    /// `expected` -- `public_sum` of the verifier's own contributions -- on
    /// the last.
    pub fn boundaries(&self, n: usize, expected: Ext) -> Vec<AuxBoundary> {
        let column = self.running_sum_column();
        vec![
            AuxBoundary { row: 0, column, value: Ext::ZERO },
            AuxBoundary { row: n - 1, column, value: expected },
        ]
    }

    /// What the trace's interactions must sum to for the bus to balance
    /// against `public` -- tuples the verifier itself contributes, each
    /// with a multiplicity from the *trace's* point of view (a tuple the
    /// trace must send exactly once is `(+1, tuple)`, since the public side
    /// receives it).
    pub fn public_sum(&self, public: &[(BabyBear, Vec<BabyBear>)], challenges: &[Ext]) -> Ext {
        let (gamma, beta) = self.challenges(challenges);
        public.iter().fold(Ext::ZERO, |acc, (m, values)| {
            let values: Vec<Ext> = values.iter().map(|&v| Ext::from_base(v)).collect();
            acc + Ext::from_base(*m) * fingerprint(&values, gamma, beta).inverse()
        })
    }
}

/// Lift a row's interactions (as an AIR computes them, over any `Field`)
/// to the extension -- what `Bus::eval` takes.
pub fn lift<F: Field>(interactions: Vec<Interaction<F>>, to_ext: impl Fn(F) -> Ext) -> Vec<Interaction<Ext>> {
    interactions
        .into_iter()
        .map(|i| Interaction {
            multiplicity: to_ext(i.multiplicity),
            values: i.values.into_iter().map(&to_ext).collect(),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::{self, Air, Boundary, Params};

    /// Proves every value in column 0 (on rows where column 1 is 1)
    /// belongs to a public list, each list entry used exactly once --
    /// "these private values are exactly that public set". Column 1 is a
    /// boolean selector, and the last row is padding (selector 0).
    struct Membership {
        log_n: usize,
        public: Vec<BabyBear>,
    }

    const BUS: Bus = Bus {
        slots: 1,
        aux_offset: 0,
        challenge_offset: 0,
    };
    const TAG: u32 = 7;

    impl Membership {
        fn interactions<F: Field>(&self, row: &[F]) -> Vec<Interaction<F>> {
            vec![Interaction {
                multiplicity: row[1],
                values: vec![F::from_base(BabyBear::new(TAG)), row[0]],
            }]
        }
    }

    impl Air for Membership {
        fn width(&self) -> usize {
            2
        }
        fn trace_len(&self) -> usize {
            1 << self.log_n
        }
        fn constraint_degree(&self) -> usize {
            2
        }
        fn num_transition_constraints(&self) -> usize {
            1
        }
        fn eval_transition<F: Field>(&self, current: &[F], _next: &[F], _periodic: &[F], out: &mut [F]) {
            out[0] = current[1] * (current[1] - F::ONE); // boolean selector
        }
        fn boundaries(&self) -> Vec<Boundary> {
            vec![Boundary { row: self.trace_len() - 1, column: 1, value: BabyBear::ZERO }]
        }
        fn num_aux_columns(&self) -> usize {
            BUS.num_aux_columns()
        }
        fn num_challenges(&self) -> usize {
            NUM_CHALLENGES
        }
        fn aux_trace(&self, main: &[Vec<BabyBear>], challenges: &[Ext]) -> Vec<Vec<Ext>> {
            BUS.aux_trace(
                self.trace_len(),
                |i| self.interactions(&[main[0][i], main[1][i]]),
                challenges,
            )
        }
        fn num_aux_constraints(&self) -> usize {
            BUS.num_constraints()
        }
        fn eval_aux_transition<F: Field>(&self, frame: &AuxFrame<F>, out: &mut [F]) {
            let interactions = self.interactions(frame.main_current);
            BUS.eval(&interactions, frame, out);
        }
        fn aux_boundaries(&self, challenges: &[Ext]) -> Vec<AuxBoundary> {
            let public: Vec<(BabyBear, Vec<BabyBear>)> = self
                .public
                .iter()
                .map(|&v| (BabyBear::ONE, vec![BabyBear::new(TAG), v]))
                .collect();
            BUS.boundaries(self.trace_len(), BUS.public_sum(&public, challenges))
        }
        fn statement(&self) -> Vec<BabyBear> {
            self.public.clone()
        }
    }

    const PARAMS: Params = Params {
        log_blowup: 2,
        num_queries: 20,
        grinding_bits: 4,
    };

    /// Private values `values` scattered among unselected filler rows.
    fn trace(log_n: usize, values: &[u32]) -> Vec<Vec<BabyBear>> {
        let n = 1 << log_n;
        let mut column = vec![BabyBear::new(999); n];
        let mut selector = vec![BabyBear::ZERO; n];
        for (k, &v) in values.iter().enumerate() {
            column[3 * k] = BabyBear::new(v);
            selector[3 * k] = BabyBear::ONE;
        }
        vec![column, selector]
    }

    fn public(values: &[u32]) -> Vec<BabyBear> {
        values.iter().map(|&v| BabyBear::new(v)).collect()
    }

    #[test]
    fn the_same_set_in_a_different_order_verifies() {
        let air = Membership {
            log_n: 5,
            public: public(&[10, 20, 30, 40]),
        };
        let proof = stark::prove(&air, &trace(5, &[30, 10, 40, 20]), &PARAMS, [1; 32]).unwrap();
        assert!(stark::verify(&air, &proof, &PARAMS));
    }

    #[test]
    fn a_missing_extra_or_altered_value_is_refused() {
        let air = Membership {
            log_n: 5,
            public: public(&[10, 20, 30, 40]),
        };
        for values in [&[10, 20, 30][..], &[10, 20, 30, 40, 50], &[10, 20, 30, 41], &[10, 10, 30, 40]] {
            assert!(
                matches!(
                    stark::prove(&air, &trace(5, values), &PARAMS, [1; 32]),
                    Err(stark::Error::AuxBoundaryViolated(_))
                ),
                "{values:?}"
            );
        }
    }

    /// A proof for one public set doesn't verify against another.
    #[test]
    fn a_proof_does_not_carry_over_to_a_different_public_set() {
        let air = Membership {
            log_n: 5,
            public: public(&[10, 20, 30, 40]),
        };
        let proof = stark::prove(&air, &trace(5, &[10, 20, 30, 40]), &PARAMS, [1; 32]).unwrap();
        let other = Membership {
            log_n: 5,
            public: public(&[10, 20, 30, 41]),
        };
        assert!(!stark::verify(&other, &proof, &PARAMS));
    }
}
