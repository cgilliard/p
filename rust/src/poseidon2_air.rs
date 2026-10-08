//! Poseidon2 as a STARK circuit: a "chip" -- trace generation plus
//! constraints over a slice of columns -- that proves a block of rows
//! computes one Poseidon2 permutation, exactly as `poseidon2`'s native
//! `permute` does (same constants, same layers; tested against it).
//!
//! Hashing is nearly all a block's proof does (commitments, public-key
//! hashes, WOTS chains), so this is the workhorse every later circuit
//! embeds. Generic over the state width: 24 for `hash_bytes` (the
//! commitments), 16 for WOTS's `compress`.
//!
//! # Layout
//!
//! One permutation occupies `ROWS` (32) consecutive rows, one row per
//! round. Row 0 holds the input; each transition `r -> r + 1` applies
//! round `r`; the row after the last round holds the output, and any rows
//! left over in the block are unconstrained padding. Rounds, in order:
//! the initial external linear layer (a "linear" round, no S-box), the
//! first `R_F / 2` full rounds, the `R_P` partial rounds, then the last
//! `R_F / 2` full rounds -- 22 for width 16, 30 for width 24.
//!
//! Columns: the state (`WIDTH`) and an auxiliary "cube" column per state
//! element (`WIDTH`). The S-box is `x^7`, degree 7 -- far too high to
//! write as one constraint cheaply -- so it's split through the cube
//! column: `c = t^3` and `t^7 = c^2 · t`, each degree 3. Partial rounds
//! only use the first cube column; the rest are left free there.
//!
//! What changes row by row -- which kind of round it is, and that round's
//! constants -- comes from periodic columns (`periodic_columns`), period
//! `ROWS`, so the same constraints repeat for every permutation in a
//! trace. Each constraint is gated by its round-type selector, which
//! makes the overall degree 4.

#![allow(dead_code)]

use crate::field::Field;
use crate::poseidon2::{BabyBear, Poseidon2BabyBear};

/// Rows per permutation: enough for the most rounds any supported width
/// needs (30, for width 24) plus the output row, rounded up to a power of
/// two so it can be a periodic column's period.
pub const ROWS: usize = 32;

/// Constraint degree: a selector times a degree-3 expression.
pub const CONSTRAINT_DEGREE: usize = 4;

/// Periodic column indices.
const LINEAR: usize = 0;
const FULL: usize = 1;
const PARTIAL: usize = 2;
const CONSTANTS: usize = 3;

pub struct Poseidon2Chip<const WIDTH: usize> {
    perm: Poseidon2BabyBear<WIDTH>,
}

/// What kind of round row `r` of a block begins.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Round {
    Linear,
    Full,
    Partial,
    /// After the last round: the output row, then padding.
    None,
}

impl<const WIDTH: usize> Poseidon2Chip<WIDTH>
where
    Poseidon2BabyBear<WIDTH>: Default,
{
    pub fn new() -> Self {
        Poseidon2Chip {
            perm: Poseidon2BabyBear::<WIDTH>::default(),
        }
    }
}

impl<const WIDTH: usize> Poseidon2Chip<WIDTH> {
    pub fn from_permutation(perm: Poseidon2BabyBear<WIDTH>) -> Self {
        Poseidon2Chip { perm }
    }

    pub fn num_columns(&self) -> usize {
        2 * WIDTH
    }

    pub fn num_constraints(&self) -> usize {
        2 * WIDTH
    }

    fn half_full(&self) -> usize {
        self.perm.ext_initial.len()
    }

    fn partial(&self) -> usize {
        self.perm.internal_rc.len()
    }

    /// Rounds in one permutation, the initial linear layer included.
    pub fn num_rounds(&self) -> usize {
        1 + 2 * self.half_full() + self.partial()
    }

    /// The row within a block holding the permutation's output.
    pub fn output_row(&self) -> usize {
        self.num_rounds()
    }

    fn round(&self, r: usize) -> Round {
        let hf = self.half_full();
        let p = self.partial();
        match r {
            0 => Round::Linear,
            r if r <= hf => Round::Full,
            r if r <= hf + p => Round::Partial,
            r if r <= 2 * hf + p => Round::Full,
            _ => Round::None,
        }
    }

    /// Round `r`'s constants (zero where it has none).
    fn constants(&self, r: usize) -> [BabyBear; WIDTH] {
        let hf = self.half_full();
        let p = self.partial();
        let mut out = [BabyBear::ZERO; WIDTH];
        match self.round(r) {
            Round::Full if r <= hf => out = self.perm.ext_initial[r - 1],
            Round::Full => out = self.perm.ext_final[r - 1 - hf - p],
            Round::Partial => out[0] = self.perm.internal_rc[r - 1 - hf],
            _ => {}
        }
        out
    }

    /// The periodic columns the constraints read: three round-type
    /// selectors, then `WIDTH` round-constant columns. Period `ROWS`.
    // Filling column-major tables row by row reads clearest indexed.
    #[allow(clippy::needless_range_loop)]
    pub fn periodic_columns(&self) -> Vec<Vec<BabyBear>> {
        let mut columns = vec![vec![BabyBear::ZERO; ROWS]; CONSTANTS + WIDTH];
        for r in 0..ROWS {
            let selector = match self.round(r) {
                Round::Linear => Some(LINEAR),
                Round::Full => Some(FULL),
                Round::Partial => Some(PARTIAL),
                Round::None => None,
            };
            if let Some(s) = selector {
                columns[s][r] = BabyBear::ONE;
            }
            for (i, c) in self.constants(r).into_iter().enumerate() {
                columns[CONSTANTS + i][r] = c;
            }
        }
        columns
    }

    /// The `ROWS` rows (each `num_columns` wide) proving
    /// `permute(input)`, and that output.
    pub fn generate(&self, input: [BabyBear; WIDTH]) -> (Vec<Vec<BabyBear>>, [BabyBear; WIDTH]) {
        let mut rows = Vec::with_capacity(ROWS);
        let mut state = input;
        for r in 0..ROWS {
            let mut row = vec![BabyBear::ZERO; 2 * WIDTH];
            row[..WIDTH].copy_from_slice(&state);
            let rc = self.constants(r);
            let round = self.round(r);
            let sboxed = match round {
                Round::Full => WIDTH,
                Round::Partial => 1,
                _ => 0,
            };
            let mut t = state;
            for i in 0..sboxed {
                t[i] = state[i] + rc[i];
                let cube = t[i] * t[i] * t[i];
                row[WIDTH + i] = cube;
                t[i] = cube * cube * t[i];
            }
            rows.push(row);
            state = match round {
                Round::Linear => external_layer(state),
                Round::Full => external_layer(t),
                Round::Partial => internal_layer(t, &self.perm.internal_diag),
                Round::None => state,
            };
        }
        let output: [BabyBear; WIDTH] = rows[self.output_row()][..WIDTH].try_into().unwrap();
        (rows, output)
    }

    /// The constraints for one transition, written to `out`
    /// (`num_constraints` of them). `current`/`next` are this chip's
    /// columns of two consecutive rows; `periodic` is this chip's
    /// periodic values at the current row.
    pub fn eval<F: Field>(&self, current: &[F], next: &[F], periodic: &[F], out: &mut [F]) {
        let (state, cube) = current.split_at(WIDTH);
        let linear = periodic[LINEAR];
        let full = periodic[FULL];
        let partial = periodic[PARTIAL];
        let rc = &periodic[CONSTANTS..CONSTANTS + WIDTH];

        // S-box inputs and outputs, through the cube columns.
        let mut t = [F::ZERO; WIDTH];
        let mut u = [F::ZERO; WIDTH];
        for i in 0..WIDTH {
            t[i] = state[i] + rc[i];
            u[i] = cube[i] * cube[i] * t[i];
            // Cube constraint: every element in a full round, only the
            // first in a partial one.
            let gate = if i == 0 { full + partial } else { full };
            out[i] = gate * (cube[i] - t[i] * t[i] * t[i]);
        }

        let state_array: [F; WIDTH] = state.try_into().unwrap();
        let after_linear = external_layer(state_array);
        let after_full = external_layer(u);
        let mut partial_in: [F; WIDTH] = state.try_into().unwrap();
        partial_in[0] = u[0];
        let after_partial = internal_layer(partial_in, &self.perm.internal_diag);
        for i in 0..WIDTH {
            out[WIDTH + i] = linear * (next[i] - after_linear[i])
                + full * (next[i] - after_full[i])
                + partial * (next[i] - after_partial[i]);
        }
    }
}

/// `poseidon2`'s 4x4 MDS block, over any `Field`.
fn mat4<F: Field>(x: &mut [F]) {
    let t01 = x[0] + x[1];
    let t23 = x[2] + x[3];
    let t0123 = t01 + t23;
    let t01123 = t0123 + x[1];
    let t01233 = t0123 + x[3];
    x[3] = t01233 + x[0] + x[0];
    x[1] = t01123 + x[2] + x[2];
    x[0] = t01123 + t01;
    x[2] = t01233 + t23;
}

/// `poseidon2`'s external linear layer, over any `Field`.
fn external_layer<F: Field, const WIDTH: usize>(mut state: [F; WIDTH]) -> [F; WIDTH] {
    for chunk in state.chunks_mut(4) {
        mat4(chunk);
    }
    let mut sums = [F::ZERO; 4];
    for (k, sum) in sums.iter_mut().enumerate() {
        for j in (0..WIDTH).step_by(4) {
            *sum = *sum + state[j + k];
        }
    }
    for (i, elem) in state.iter_mut().enumerate() {
        *elem = *elem + sums[i % 4];
    }
    state
}

/// `poseidon2`'s internal linear layer, over any `Field`.
fn internal_layer<F: Field, const WIDTH: usize>(mut state: [F; WIDTH], diag: &[BabyBear; WIDTH]) -> [F; WIDTH] {
    let sum = state.iter().fold(F::ZERO, |a, &b| a + b);
    for i in 0..WIDTH {
        state[i] = state[i].mul_base(diag[i]) + sum;
    }
    state
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::{self, Air, Boundary, Params};

    /// Proves `permute(inputs[k]) == outputs[k]` for every `k`, one block
    /// of `ROWS` rows each.
    struct Permutations<const WIDTH: usize> {
        chip: Poseidon2Chip<WIDTH>,
        inputs: Vec<[BabyBear; WIDTH]>,
        outputs: Vec<[BabyBear; WIDTH]>,
    }

    impl<const WIDTH: usize> Air for Permutations<WIDTH> {
        fn width(&self) -> usize {
            self.chip.num_columns()
        }
        fn trace_len(&self) -> usize {
            ROWS * self.inputs.len()
        }
        fn constraint_degree(&self) -> usize {
            CONSTRAINT_DEGREE
        }
        fn periodic_columns(&self) -> Vec<Vec<BabyBear>> {
            self.chip.periodic_columns()
        }
        fn num_transition_constraints(&self) -> usize {
            self.chip.num_constraints()
        }
        fn eval_transition<F: Field>(&self, current: &[F], next: &[F], periodic: &[F], out: &mut [F]) {
            self.chip.eval(current, next, periodic, out);
        }
        fn boundaries(&self) -> Vec<Boundary> {
            let mut out = Vec::new();
            for (k, (input, output)) in self.inputs.iter().zip(&self.outputs).enumerate() {
                for i in 0..WIDTH {
                    out.push(Boundary { row: k * ROWS, column: i, value: input[i] });
                    out.push(Boundary {
                        row: k * ROWS + self.chip.output_row(),
                        column: i,
                        value: output[i],
                    });
                }
            }
            out
        }
    }

    const PARAMS: Params = Params {
        log_blowup: 1,
        num_queries: 16,
        grinding_bits: 4,
        hiding: true,
    };

    fn input<const WIDTH: usize>(seed: u32) -> [BabyBear; WIDTH] {
        std::array::from_fn(|i| BabyBear::new(seed.wrapping_mul(1_000_003) + i as u32 * 7919))
    }

    /// Column-major trace for `inputs`, and the outputs it computes.
    fn trace<const WIDTH: usize>(
        chip: &Poseidon2Chip<WIDTH>,
        inputs: &[[BabyBear; WIDTH]],
    ) -> (Vec<Vec<BabyBear>>, Vec<[BabyBear; WIDTH]>) {
        let mut columns = vec![Vec::new(); chip.num_columns()];
        let mut outputs = Vec::new();
        for &input in inputs {
            let (rows, output) = chip.generate(input);
            for row in rows {
                for (c, v) in row.into_iter().enumerate() {
                    columns[c].push(v);
                }
            }
            outputs.push(output);
        }
        (columns, outputs)
    }

    #[test]
    fn round_counts_fit_a_block() {
        assert_eq!(Poseidon2Chip::<16>::new().num_rounds(), 22);
        assert_eq!(Poseidon2Chip::<24>::new().num_rounds(), 30);
        assert!(Poseidon2Chip::<24>::new().output_row() < ROWS);
    }

    /// The generated trace's output is exactly the native permutation's.
    #[test]
    fn generated_output_matches_the_native_permutation() {
        let chip16 = Poseidon2Chip::<16>::new();
        let chip24 = Poseidon2Chip::<24>::new();
        for seed in 0..5 {
            assert_eq!(chip16.generate(input(seed)).1, Poseidon2BabyBear::<16>::new().permute(input(seed)));
            assert_eq!(chip24.generate(input(seed)).1, Poseidon2BabyBear::<24>::new().permute(input(seed)));
        }
    }

    /// The constraints hold on every transition of a generated trace --
    /// checked directly, row by row, before any proving is involved.
    #[test]
    fn constraints_hold_on_a_generated_trace() {
        let chip = Poseidon2Chip::<24>::new();
        let periodic = chip.periodic_columns();
        let (rows, _) = chip.generate(input(3));
        let mut out = vec![BabyBear::ZERO; chip.num_constraints()];
        for r in 0..ROWS - 1 {
            let p: Vec<BabyBear> = periodic.iter().map(|c| c[r]).collect();
            chip.eval(&rows[r], &rows[r + 1], &p, &mut out);
            assert!(out.iter().all(|&v| v == BabyBear::ZERO), "row {r}");
        }
    }

    #[test]
    fn a_proof_of_several_permutations_verifies_at_both_widths() {
        let chip = Poseidon2Chip::<16>::new();
        let inputs: Vec<[BabyBear; 16]> = (0..4).map(input).collect();
        let (columns, outputs) = trace(&chip, &inputs);
        let air = Permutations { chip, inputs, outputs };
        let proof = stark::prove(&air, &columns, &PARAMS, [1; 32]).unwrap();
        assert!(stark::verify(&air, &proof, &PARAMS));

        let chip = Poseidon2Chip::<24>::new();
        let inputs: Vec<[BabyBear; 24]> = (0..2).map(input).collect();
        let (columns, outputs) = trace(&chip, &inputs);
        let air = Permutations { chip, inputs, outputs };
        let proof = stark::prove(&air, &columns, &PARAMS, [2; 32]).unwrap();
        assert!(stark::verify(&air, &proof, &PARAMS));
    }

    /// Claiming a wrong output is refused by the prover, and a proof of
    /// the right one doesn't pass for the wrong one.
    #[test]
    fn a_wrong_output_is_rejected() {
        let chip = Poseidon2Chip::<16>::new();
        let inputs: Vec<[BabyBear; 16]> = (0..2).map(input).collect();
        let (columns, outputs) = trace(&chip, &inputs);
        let air = Permutations {
            chip,
            inputs: inputs.clone(),
            outputs: outputs.clone(),
        };
        let proof = stark::prove(&air, &columns, &PARAMS, [1; 32]).unwrap();

        let mut wrong = outputs;
        wrong[1][5] = wrong[1][5] + BabyBear::ONE;
        let lie = Permutations {
            chip: Poseidon2Chip::<16>::new(),
            inputs,
            outputs: wrong,
        };
        assert!(!stark::verify(&lie, &proof, &PARAMS));
        assert!(stark::prove(&lie, &columns, &PARAMS, [1; 32]).is_err());
    }

    /// Every way to fudge a round -- a wrong cube, or a state that doesn't
    /// follow from the round -- breaks a constraint.
    #[test]
    fn fudging_any_round_breaks_a_constraint() {
        let chip = Poseidon2Chip::<16>::new();
        let periodic = chip.periodic_columns();
        let (rows, _) = chip.generate(input(1));
        let check = |rows: &[Vec<BabyBear>]| -> bool {
            let mut out = vec![BabyBear::ZERO; chip.num_constraints()];
            (0..ROWS - 1).all(|r| {
                let p: Vec<BabyBear> = periodic.iter().map(|c| c[r]).collect();
                chip.eval(&rows[r], &rows[r + 1], &p, &mut out);
                out.iter().all(|&v| v == BabyBear::ZERO)
            })
        };
        assert!(check(&rows));
        // The linear round, a full round, a partial round, the last round.
        for r in [1, 3, 10, chip.output_row()] {
            let mut bad = rows.clone();
            bad[r][2] = bad[r][2] + BabyBear::ONE;
            assert!(!check(&bad), "state at row {r}");
        }
        // A cube in a full round, and the one cube a partial round uses.
        for (r, i) in [(2, 7), (8, 0)] {
            let mut bad = rows.clone();
            bad[r][16 + i] = bad[r][16 + i] + BabyBear::ONE;
            assert!(!check(&bad), "cube {i} at row {r}");
        }
    }

    /// Not a correctness test: proving time and proof size for a
    /// realistic batch, to plan against the 2 MB block limit. Run with
    /// `cargo test --release -- --ignored --nocapture poseidon2_cost`.
    #[test]
    #[ignore]
    fn poseidon2_cost() {
        let chip = Poseidon2Chip::<24>::new();
        let inputs: Vec<[BabyBear; 24]> = (0..64).map(input).collect();
        let (columns, outputs) = trace(&chip, &inputs);
        let air = Permutations { chip, inputs, outputs };
        for params in [
            Params { log_blowup: 1, num_queries: 100, grinding_bits: 4, hiding: true },
            Params { log_blowup: 2, num_queries: 50, grinding_bits: 4, hiding: true },
            Params { log_blowup: 3, num_queries: 34, grinding_bits: 4, hiding: true },
        ] {
            let start = std::time::Instant::now();
            let proof = stark::prove(&air, &columns, &params, [1; 32]).unwrap();
            let proving = start.elapsed();
            let start = std::time::Instant::now();
            assert!(stark::verify(&air, &proof, &params));
            println!(
                "64 width-24 permutations ({} rows), blowup 2^{}, {} queries: prove {:.2?}, verify {:.2?}, ~{} KB",
                air.trace_len(),
                params.log_blowup,
                params.num_queries,
                proving,
                start.elapsed(),
                proof.approximate_size() / 1024
            );
        }
    }
}
