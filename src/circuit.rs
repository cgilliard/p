//! A small circuit VM: write a computation as ordinary Rust against a
//! `Builder` -- Poseidon2 permutations, extension-field arithmetic, bit
//! decomposition, table lookups -- and get back one STARK trace that
//! proves it. Its first job is verifying STARK proofs inside a STARK
//! (`docs/RECURSION.md`), but nothing here is specific to that.
//!
//! # Memory
//!
//! Every value lives in a memory *cell*: an address and eight base-field
//! lanes. A cell holds either an **octet** (8 elements: a digest, half a
//! Poseidon2 rate) or an **extension element** (4 coefficients, lanes 4-7
//! zero; a base value is an extension element with coefficients 1-3 zero).
//! Each cell is *written* exactly once -- by the operation computing it, or
//! by the verifier for constants and public inputs -- and *read* any number
//! of times. Reads and writes are matched by one LogUp bus (`bus`) over
//! tuples `(address, lane 0..8)`: each write sends its tuple with a
//! multiplicity equal to how often it's read, each read receives one copy.
//! Since a cell's address is written once (write addresses are fixed
//! columns, distinct by construction), every read sees exactly the value
//! its writer produced. Reading an extension cell with zeros in lanes 4-7
//! (as arithmetic does) also *proves* those lanes are zero.
//!
//! # Rows
//!
//! What each row does -- its kind, the addresses it reads and writes, its
//! arithmetic coefficients -- is fixed, in preprocessed columns
//! (`stark::Preprocessed`): that's the circuit, and its commitment is the
//! circuit's identity. The witness columns hold values: 48 *value*
//! columns `V`, plus one write multiplicity per bus slot (4 slots). Kinds:
//!
//! - **Poseidon2** (32 rows, `poseidon2_air`'s chip over `V`): row 0 reads
//!   the input state as three octets (rate low, rate high, capacity) --
//!   optionally *swapping* the two rate octets by a bit read from memory,
//!   which is how a Merkle path picks left/right -- and row 30 writes the
//!   output as three octets. Permutation blocks come first, 32-row aligned.
//! - **Arithmetic** (1 row): `c = α·a·b + β·a + γ·b + δ·d + Σ_l λ_l·d[l]`
//!   over the extension, with base-field coefficients; `d[l]` is lane `l`
//!   of `d` taken as a base value. `c` is either written, or read -- which
//!   *asserts* the result equals an existing cell.
//! - **Repack** (1 row): one octet and its two halves as extension cells;
//!   any of the three may be read or written. Writing all three is how
//!   free witness values enter.
//! - **Bit step** (1 row): reads `x` (lane 0 of a cell), writes `x'` and
//!   the bit `b` with `x = 2x' + b`, `b ∈ {0, 1}`.
//! - **Lookup** (1 row): asserts `value == table[i]`, reading the table
//!   entry at a *computed* address `base + i`, `i` read from memory.
//!
//! The last row is always idle: transition constraints (and so bus
//! interactions) don't reach it.
//!
//! # Soundness notes
//!
//! A circuit is only as good as what its author asserts: values written by
//! repack rows are free, so whatever a computation relies on must be
//! derived from public cells and assertions. Tables read by lookups must
//! be written in the trace (not public), since how often each entry is
//! read depends on the witness.

#![allow(dead_code)]

use std::collections::HashMap;
use std::sync::Arc;

use crate::bus::{Bus, Interaction};
use crate::ext::Ext;
use crate::field::Field;
use crate::poseidon2::BabyBear;
use crate::poseidon2_air::{self, Poseidon2Chip};
use crate::stark::{Air, AuxBoundary, AuxFrame, Boundary, Params, Preprocessed};

pub type Octet = [BabyBear; 8];

/// Value columns (the Poseidon2 chip's 48 on its rows).
const V: usize = 0;
const VALUES: usize = 48;
/// Write multiplicities, one per slot.
const M: usize = 48;
pub const WITNESS_WIDTH: usize = 52;
/// A permutation's swap bit, on its input row: the first cube column,
/// which the chip leaves free on that (linear) round.
const SWAP_BIT: usize = 24;

// Preprocessed columns, indexed from the first one.
const SEL: usize = 0; // the chip's three round-type selectors
const P_IN: usize = 3;
const P_OUT: usize = 4;
const ARITH: usize = 5;
const REPACK: usize = 6;
const BITS: usize = 7;
const LOOKUP: usize = 8;
const SW: usize = 9;
const ADDR: usize = 10; // 4: each slot's address
const RD: usize = 14; // 4: slot reads (multiplicity -1)
const WR: usize = 18; // 4: slot writes (multiplicity from M)
const ALPHA: usize = 22;
const BETA: usize = 23;
const GAMMA: usize = 24;
const DELTA: usize = 25;
const LAMBDA: usize = 26; // 4
/// Constant rows write the 8 lanes held in `ALPHA..LAMBDA + 4`.
const CONST: usize = 30;
pub const NUM_PREPROCESSED: usize = 31;

const SLOTS: usize = 4;
const BUS: Bus = Bus {
    slots: SLOTS,
    aux_offset: 0,
    challenge_offset: 0,
};

const NUM_CONSTRAINTS: usize = 48 + 2 + 4 + 1 + SLOTS;

/// An extension-element cell.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct EVar(u32);

/// An octet cell.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct OVar(u32);

/// A run of consecutive cells, for lookups.
#[derive(Clone, Copy, Debug)]
pub struct Table {
    base: u32,
    len: u32,
}

impl Table {
    pub fn ext(&self, k: usize) -> EVar {
        assert!(k < self.len as usize);
        EVar(self.base + k as u32)
    }
    pub fn octet(&self, k: usize) -> OVar {
        assert!(k < self.len as usize);
        OVar(self.base + k as u32)
    }
    pub fn len(&self) -> usize {
        self.len as usize
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Dir {
    None,
    Read,
    Write,
}

#[derive(Clone, Copy, Debug)]
struct Coefficients {
    alpha: BabyBear,
    beta: BabyBear,
    gamma: BabyBear,
    delta: BabyBear,
    lambda: [BabyBear; 4],
}

#[derive(Clone, Debug)]
enum RowOp {
    Arith {
        a: Option<u32>,
        b: Option<u32>,
        d: Option<u32>,
        c: u32,
        c_dir: Dir,
        k: Coefficients,
    },
    /// Octet, low half, high half.
    Repack { cells: [Option<(u32, Dir)>; 3] },
    Bits { x: u32, half: u32, bit: u32 },
    Lookup { value: u32, table: u32, index: u32 },
    /// Writes a constant held in the fixed columns.
    Const { cell: u32 },
}

#[derive(Clone, Debug)]
struct PermOp {
    inputs: [u32; 3],
    swap: Option<u32>,
    outputs: [u32; 3],
    state: [BabyBear; 24],
}

/// Records a computation and its values as it runs.
pub struct Builder {
    values: Vec<Octet>,
    reads: Vec<u32>,
    /// Cells whose value the verifier supplies (constants, public inputs).
    public: Vec<u32>,
    constants: HashMap<Octet, u32>,
    halves: HashMap<u32, (EVar, EVar)>,
    perms: Vec<PermOp>,
    rows: Vec<RowOp>,
}

fn ext_octet(e: Ext) -> Octet {
    let mut o = [BabyBear::ZERO; 8];
    o[..4].copy_from_slice(&e.0);
    o
}

impl Default for Builder {
    fn default() -> Self {
        Self::new()
    }
}

impl Builder {
    pub fn new() -> Self {
        Builder {
            values: Vec::new(),
            reads: Vec::new(),
            public: Vec::new(),
            constants: HashMap::new(),
            halves: HashMap::new(),
            perms: Vec::new(),
            rows: Vec::new(),
        }
    }

    fn alloc(&mut self, value: Octet) -> u32 {
        self.values.push(value);
        self.reads.push(0);
        (self.values.len() - 1) as u32
    }

    fn read(&mut self, addr: u32) -> Octet {
        self.reads[addr as usize] += 1;
        self.values[addr as usize]
    }

    pub fn ext_value(&self, v: EVar) -> Ext {
        Ext(self.values[v.0 as usize][..4].try_into().unwrap())
    }

    pub fn octet_value(&self, v: OVar) -> Octet {
        self.values[v.0 as usize]
    }

    /// Number of permutations and one-row operations so far.
    pub fn size(&self) -> (usize, usize) {
        (self.perms.len(), self.rows.len())
    }

    // ---- values from outside ------------------------------------------

    fn constant(&mut self, value: Octet) -> u32 {
        if let Some(&a) = self.constants.get(&value) {
            return a;
        }
        let a = self.alloc(value);
        self.rows.push(RowOp::Const { cell: a });
        self.constants.insert(value, a);
        a
    }

    pub fn const_ext(&mut self, e: Ext) -> EVar {
        EVar(self.constant(ext_octet(e)))
    }

    pub fn const_base(&mut self, x: BabyBear) -> EVar {
        self.const_ext(Ext::from_base(x))
    }

    pub fn const_octet(&mut self, o: Octet) -> OVar {
        OVar(self.constant(o))
    }

    pub fn zero(&mut self) -> EVar {
        self.const_ext(Ext::ZERO)
    }

    pub fn one(&mut self) -> EVar {
        self.const_ext(Ext::ONE)
    }

    /// A builder whose circuit takes `values` as public inputs (supplied
    /// by the verifier, part of the statement), returned as octet cells.
    /// They occupy addresses `0..values.len()` and each is read exactly
    /// once (copied into a working cell), so circuits with the same number
    /// of public inputs present them identically -- a verifier circuit
    /// can then check any of them without knowing which it is.
    pub fn with_public(values: &[Octet]) -> (Self, Vec<OVar>) {
        let mut b = Builder::new();
        let cells: Vec<u32> = values.iter().map(|&v| b.alloc(v)).collect();
        b.public = cells.clone();
        let copies = cells
            .into_iter()
            .map(|a| {
                let (lo, hi) = b.halves(OVar(a));
                b.pack(lo, hi)
            })
            .collect();
        (b, copies)
    }

    /// A free witness octet (and its two halves).
    pub fn witness_octet(&mut self, o: Octet) -> OVar {
        let oct = self.alloc(o);
        let lo = self.alloc(ext_octet(Ext(o[..4].try_into().unwrap())));
        let hi = self.alloc(ext_octet(Ext(o[4..].try_into().unwrap())));
        self.rows.push(RowOp::Repack {
            cells: [Some((oct, Dir::Write)), Some((lo, Dir::Write)), Some((hi, Dir::Write))],
        });
        self.halves.insert(oct, (EVar(lo), EVar(hi)));
        OVar(oct)
    }

    /// A free witness extension element.
    pub fn witness_ext(&mut self, e: Ext) -> EVar {
        let a = self.alloc(ext_octet(e));
        self.rows.push(RowOp::Repack {
            cells: [None, Some((a, Dir::Write)), None],
        });
        EVar(a)
    }

    /// Free witness octets at consecutive addresses, for lookups.
    pub fn witness_octet_table(&mut self, values: &[Octet]) -> Table {
        let base = self.values.len() as u32;
        for &o in values {
            let a = self.alloc(o);
            self.rows.push(RowOp::Repack {
                cells: [Some((a, Dir::Write)), None, None],
            });
        }
        Table {
            base,
            len: values.len() as u32,
        }
    }

    /// Free witness extension elements at consecutive addresses.
    pub fn witness_ext_table(&mut self, values: &[Ext]) -> Table {
        let base = self.values.len() as u32;
        for &e in values {
            let a = self.alloc(ext_octet(e));
            self.rows.push(RowOp::Repack {
                cells: [None, Some((a, Dir::Write)), None],
            });
        }
        Table {
            base,
            len: values.len() as u32,
        }
    }

    // ---- octets ---------------------------------------------------------

    /// An octet's two halves as extension cells.
    pub fn halves(&mut self, o: OVar) -> (EVar, EVar) {
        if let Some(&h) = self.halves.get(&o.0) {
            return h;
        }
        let v = self.read(o.0);
        let lo = self.alloc(ext_octet(Ext(v[..4].try_into().unwrap())));
        let hi = self.alloc(ext_octet(Ext(v[4..].try_into().unwrap())));
        self.rows.push(RowOp::Repack {
            cells: [Some((o.0, Dir::Read)), Some((lo, Dir::Write)), Some((hi, Dir::Write))],
        });
        self.halves.insert(o.0, (EVar(lo), EVar(hi)));
        (EVar(lo), EVar(hi))
    }

    /// The octet `[lo coefficients, hi coefficients]`.
    pub fn pack(&mut self, lo: EVar, hi: EVar) -> OVar {
        let (l, h) = (self.read(lo.0), self.read(hi.0));
        let mut v = [BabyBear::ZERO; 8];
        v[..4].copy_from_slice(&l[..4]);
        v[4..].copy_from_slice(&h[..4]);
        let o = self.alloc(v);
        self.rows.push(RowOp::Repack {
            cells: [Some((o, Dir::Write)), Some((lo.0, Dir::Read)), Some((hi.0, Dir::Read))],
        });
        self.halves.insert(o, (lo, hi));
        OVar(o)
    }

    /// Assert two octets are equal.
    pub fn assert_eq_octet(&mut self, x: OVar, y: OVar) {
        let (xl, xh) = self.halves(x);
        let (yl, yh) = self.halves(y);
        self.assert_eq(xl, yl);
        self.assert_eq(xh, yh);
    }

    // ---- Poseidon2 ------------------------------------------------------

    /// Permute the state `[rate_lo, rate_hi, capacity]` -- or, if `swap`
    /// (a bit cell) is 1, `[rate_hi, rate_lo, capacity]` -- returning the
    /// output's three octets.
    pub fn permute(&mut self, rate_lo: OVar, rate_hi: OVar, capacity: OVar, swap: Option<EVar>) -> [OVar; 3] {
        let (lo, hi, cap) = (self.read(rate_lo.0), self.read(rate_hi.0), self.read(capacity.0));
        let swapped = match swap {
            Some(b) => {
                let bit = self.read(b.0)[0];
                assert!(bit == BabyBear::ZERO || bit == BabyBear::ONE, "swap must be a bit");
                bit == BabyBear::ONE
            }
            None => false,
        };
        let mut state = [BabyBear::ZERO; 24];
        let (first, second) = if swapped { (hi, lo) } else { (lo, hi) };
        state[..8].copy_from_slice(&first);
        state[8..16].copy_from_slice(&second);
        state[16..].copy_from_slice(&cap);
        let out = crate::poseidon2::perm24().permute(state);
        let outputs = [0, 1, 2].map(|k| self.alloc(out[8 * k..8 * k + 8].try_into().unwrap()));
        self.perms.push(PermOp {
            inputs: [rate_lo.0, rate_hi.0, capacity.0],
            swap: swap.map(|b| b.0),
            outputs,
            state,
        });
        outputs.map(OVar)
    }

    // ---- arithmetic -----------------------------------------------------

    fn arith_row(&mut self, a: Option<EVar>, b: Option<EVar>, d: Option<EVar>, k: Coefficients) -> Ext {
        let val = |s: &mut Self, v: Option<EVar>| v.map(|v| Ext(s.read(v.0)[..4].try_into().unwrap())).unwrap_or(Ext::ZERO);
        let (av, bv, dv) = (val(self, a), val(self, b), val(self, d));
        let lanes = dv.0.iter().zip(&k.lambda).fold(BabyBear::ZERO, |acc, (&x, &l)| acc + x * l);
        (av * bv).mul_base(k.alpha) + av.mul_base(k.beta) + bv.mul_base(k.gamma) + dv.mul_base(k.delta) + Ext::from_base(lanes)
    }

    /// The general operation: `α·a·b + β·a + γ·b + δ·d + Σ λ_l·d[l]`.
    #[allow(clippy::too_many_arguments)]
    pub fn arith(
        &mut self,
        alpha: BabyBear,
        a: Option<EVar>,
        b: Option<EVar>,
        beta: BabyBear,
        gamma: BabyBear,
        d: Option<EVar>,
        delta: BabyBear,
        lambda: [BabyBear; 4],
    ) -> EVar {
        let k = Coefficients {
            alpha,
            beta,
            gamma,
            delta,
            lambda,
        };
        let value = self.arith_row(a, b, d, k);
        let c = self.alloc(ext_octet(value));
        self.rows.push(RowOp::Arith {
            a: a.map(|v| v.0),
            b: b.map(|v| v.0),
            d: d.map(|v| v.0),
            c,
            c_dir: Dir::Write,
            k,
        });
        EVar(c)
    }

    pub fn add(&mut self, a: EVar, b: EVar) -> EVar {
        let (o, z) = (BabyBear::ONE, BabyBear::ZERO);
        self.arith(z, Some(a), Some(b), o, o, None, z, [z; 4])
    }

    pub fn sub(&mut self, a: EVar, b: EVar) -> EVar {
        let (o, z) = (BabyBear::ONE, BabyBear::ZERO);
        self.arith(z, Some(a), Some(b), o, -o, None, z, [z; 4])
    }

    pub fn mul(&mut self, a: EVar, b: EVar) -> EVar {
        let (o, z) = (BabyBear::ONE, BabyBear::ZERO);
        self.arith(o, Some(a), Some(b), z, z, None, z, [z; 4])
    }

    /// `a·b + d`.
    pub fn mul_add(&mut self, a: EVar, b: EVar, d: EVar) -> EVar {
        let (o, z) = (BabyBear::ONE, BabyBear::ZERO);
        self.arith(o, Some(a), Some(b), z, z, Some(d), o, [z; 4])
    }

    /// `a·b - d`.
    pub fn mul_sub(&mut self, a: EVar, b: EVar, d: EVar) -> EVar {
        let (o, z) = (BabyBear::ONE, BabyBear::ZERO);
        self.arith(o, Some(a), Some(b), z, z, Some(d), -o, [z; 4])
    }

    /// `k·a`, `k` a base constant.
    pub fn scale(&mut self, a: EVar, k: BabyBear) -> EVar {
        let z = BabyBear::ZERO;
        self.arith(z, Some(a), None, k, z, None, z, [z; 4])
    }

    /// `a + k`, `k` a base constant.
    pub fn add_base(&mut self, a: EVar, k: BabyBear) -> EVar {
        let one = self.one();
        let z = BabyBear::ZERO;
        self.arith(z, Some(a), None, BabyBear::ONE, z, Some(one), k, [z; 4])
    }

    /// `acc·w + d[lane]`: one step of a Horner sum over base values packed
    /// four to a cell.
    pub fn horner_lane(&mut self, acc: EVar, w: EVar, d: EVar, lane: usize) -> EVar {
        let (o, z) = (BabyBear::ONE, BabyBear::ZERO);
        let mut lambda = [z; 4];
        lambda[lane] = o;
        self.arith(o, Some(acc), Some(w), z, z, Some(d), z, lambda)
    }

    /// Lane `l` of `d` as a base value.
    pub fn lane(&mut self, d: EVar, lane: usize) -> EVar {
        let (o, z) = (BabyBear::ONE, BabyBear::ZERO);
        let mut lambda = [z; 4];
        lambda[lane] = o;
        self.arith(z, None, None, z, z, Some(d), z, lambda)
    }

    /// Assert `x == y`.
    pub fn assert_eq(&mut self, x: EVar, y: EVar) {
        let (o, z) = (BabyBear::ONE, BabyBear::ZERO);
        let k = Coefficients {
            alpha: z,
            beta: o,
            gamma: z,
            delta: z,
            lambda: [z; 4],
        };
        let value = self.arith_row(Some(x), None, None, k);
        assert_eq!(value, self.ext_value(y), "assertion fails");
        self.read(y.0);
        self.rows.push(RowOp::Arith {
            a: Some(x.0),
            b: None,
            d: None,
            c: y.0,
            c_dir: Dir::Read,
            k,
        });
    }

    pub fn assert_zero(&mut self, x: EVar) {
        let zero = self.zero();
        self.assert_eq(x, zero);
    }

    /// `1 / x` (asserting `x ≠ 0`).
    pub fn inverse(&mut self, x: EVar) -> EVar {
        let inv = self.witness_ext(self.ext_value(x).inverse());
        let product = self.mul(x, inv);
        let one = self.one();
        self.assert_eq(product, one);
        inv
    }

    // ---- bits and lookups -----------------------------------------------

    /// One step of bit decomposition: `x = 2·x' + b` (`x` lane 0 of a
    /// cell, as an integer below 2^31), returning `(x', b)`.
    pub fn bit_step(&mut self, x: EVar) -> (EVar, EVar) {
        let v = self.read(x.0)[0].value();
        let half = self.alloc(ext_octet(Ext::from_base(BabyBear::new(v >> 1))));
        let bit = self.alloc(ext_octet(Ext::from_base(BabyBear::new(v & 1))));
        self.rows.push(RowOp::Bits { x: x.0, half, bit });
        (EVar(half), EVar(bit))
    }

    /// Assert `value == table[index]` (`index` a cell holding a small
    /// integer below the table's length).
    pub fn lookup(&mut self, value: u32, table: Table, index: EVar) {
        let i = self.read(index.0)[0].value();
        assert!(i < table.len, "lookup index out of range");
        let entry = self.read(table.base + i);
        assert_eq!(self.read(value), entry, "lookup fails");
        self.rows.push(RowOp::Lookup {
            value,
            table: table.base,
            index: index.0,
        });
    }

    pub fn lookup_ext(&mut self, value: EVar, table: Table, index: EVar) {
        self.lookup(value.0, table, index)
    }

    pub fn lookup_octet(&mut self, value: OVar, table: Table, index: EVar) {
        self.lookup(value.0, table, index)
    }

    // ---- the trace ------------------------------------------------------

    /// Lay the computation out as a circuit (fixed columns and public
    /// cells) and its witness.
    pub fn finish(self) -> Circuit {
        self.finish_padded(0)
    }

    /// Rows the laid-out circuit needs (before padding to a power of two).
    pub fn rows_used(&self) -> usize {
        poseidon2_air::ROWS * self.perms.len() + self.rows.len() + 1 // + an idle last row
    }

    /// `finish`, with at least `min_len` rows (so circuits meant to be
    /// verified by one verifier circuit can share a trace length).
    pub fn finish_padded(self, min_len: usize) -> Circuit {
        let chip = Poseidon2Chip::<24>::new();
        let perm_rows = poseidon2_air::ROWS * self.perms.len();
        let n = self.rows_used().max(min_len).next_power_of_two().max(poseidon2_air::ROWS);
        let mut w = vec![vec![BabyBear::ZERO; n]; WITNESS_WIDTH];
        let mut p = vec![vec![BabyBear::ZERO; n]; NUM_PREPROCESSED];
        let selectors = chip.periodic_columns();
        let bb = |a: u32| BabyBear::new(a);
        let reads = &self.reads;
        let mult = |a: u32| BabyBear::new(reads[a as usize]);

        for (k, op) in self.perms.iter().enumerate() {
            let base = poseidon2_air::ROWS * k;
            let (rows, _) = chip.generate(op.state);
            for (r, row) in rows.iter().enumerate() {
                for (c, &v) in row.iter().enumerate() {
                    w[V + c][base + r] = v;
                }
                for s in 0..3 {
                    p[SEL + s][base + r] = selectors[s][r];
                }
            }
            p[P_IN][base] = BabyBear::ONE;
            for s in 0..3 {
                p[ADDR + s][base] = bb(op.inputs[s]);
                p[RD + s][base] = BabyBear::ONE;
            }
            if let Some(bit) = op.swap {
                p[SW][base] = BabyBear::ONE;
                p[ADDR + 3][base] = bb(bit);
                p[RD + 3][base] = BabyBear::ONE;
                w[V + SWAP_BIT][base] = self.values[bit as usize][0];
            }
            let out = base + chip.output_row();
            p[P_OUT][out] = BabyBear::ONE;
            for s in 0..3 {
                p[ADDR + s][out] = bb(op.outputs[s]);
                p[WR + s][out] = BabyBear::ONE;
                w[M + s][out] = mult(op.outputs[s]);
            }
        }

        let set_slot = |w: &mut Vec<Vec<BabyBear>>, p: &mut Vec<Vec<BabyBear>>, row: usize, s: usize, addr: u32, dir: Dir| {
            p[ADDR + s][row] = bb(addr);
            match dir {
                Dir::Read => p[RD + s][row] = BabyBear::ONE,
                Dir::Write => {
                    p[WR + s][row] = BabyBear::ONE;
                    w[M + s][row] = mult(addr);
                }
                Dir::None => {}
            }
        };
        for (k, op) in self.rows.iter().enumerate() {
            let row = perm_rows + k;
            let value = |a: u32| self.values[a as usize];
            match op {
                RowOp::Arith { a, b, d, c, c_dir, k } => {
                    p[ARITH][row] = BabyBear::ONE;
                    for (slot, operand) in [*a, *b, *d].into_iter().enumerate() {
                        if let Some(addr) = operand {
                            set_slot(&mut w, &mut p, row, slot, addr, Dir::Read);
                            for l in 0..4 {
                                w[V + 4 * slot + l][row] = value(addr)[l];
                            }
                        }
                    }
                    set_slot(&mut w, &mut p, row, 3, *c, *c_dir);
                    for l in 0..4 {
                        w[V + 12 + l][row] = value(*c)[l];
                    }
                    p[ALPHA][row] = k.alpha;
                    p[BETA][row] = k.beta;
                    p[GAMMA][row] = k.gamma;
                    p[DELTA][row] = k.delta;
                    for l in 0..4 {
                        p[LAMBDA + l][row] = k.lambda[l];
                    }
                }
                RowOp::Repack { cells } => {
                    p[REPACK][row] = BabyBear::ONE;
                    let mut lanes = [BabyBear::ZERO; 8];
                    for (slot, cell) in cells.iter().enumerate() {
                        if let Some((addr, dir)) = *cell {
                            set_slot(&mut w, &mut p, row, slot, addr, dir);
                            let v = value(addr);
                            match slot {
                                0 => lanes = v,
                                1 => lanes[..4].copy_from_slice(&v[..4]),
                                _ => lanes[4..].copy_from_slice(&v[..4]),
                            }
                        }
                    }
                    for (l, &v) in lanes.iter().enumerate() {
                        w[V + l][row] = v;
                    }
                }
                RowOp::Bits { x, half, bit } => {
                    p[BITS][row] = BabyBear::ONE;
                    set_slot(&mut w, &mut p, row, 0, *x, Dir::Read);
                    set_slot(&mut w, &mut p, row, 1, *half, Dir::Write);
                    set_slot(&mut w, &mut p, row, 2, *bit, Dir::Write);
                    let xv = value(*x);
                    w[V][row] = xv[0];
                    w[V + 1][row] = value(*half)[0];
                    for l in 1..4 {
                        w[V + 1 + l][row] = xv[l];
                    }
                }
                RowOp::Lookup { value: v, table, index } => {
                    p[LOOKUP][row] = BabyBear::ONE;
                    set_slot(&mut w, &mut p, row, 0, *v, Dir::Read);
                    set_slot(&mut w, &mut p, row, 1, *table, Dir::Read);
                    set_slot(&mut w, &mut p, row, 2, *index, Dir::Read);
                    let vv = value(*v);
                    for l in 0..8 {
                        w[V + l][row] = vv[l];
                    }
                    w[V + 8][row] = value(*index)[0];
                }
                RowOp::Const { cell } => {
                    p[CONST][row] = BabyBear::ONE;
                    set_slot(&mut w, &mut p, row, 0, *cell, Dir::Write);
                    for (l, &v) in value(*cell).iter().enumerate() {
                        p[ALPHA + l][row] = v;
                    }
                }
            }
        }

        let public = self
            .public
            .iter()
            .map(|&a| {
                let mut tuple = self.values[a as usize].to_vec();
                tuple.push(bb(a));
                (-BabyBear::new(self.reads[a as usize]), tuple)
            })
            .collect();
        Circuit {
            trace_len: n,
            preprocessed: p,
            public,
            witness: w,
        }
    }
}

/// A laid-out computation.
pub struct Circuit {
    pub trace_len: usize,
    /// The fixed columns: what the circuit is.
    pub preprocessed: Vec<Vec<BabyBear>>,
    /// Values the verifier contributes to the bus: each public cell's
    /// tuple, with minus how often the trace reads it.
    pub public: Vec<(BabyBear, Vec<BabyBear>)>,
    pub witness: Vec<Vec<BabyBear>>,
}

impl Circuit {
    /// Commit this circuit's fixed columns under `params` -- its
    /// verifying key; the expensive, once-per-circuit step.
    pub fn commit(&self, params: &Params) -> Arc<Preprocessed> {
        Arc::new(Preprocessed::commit(
            self.preprocessed.clone(),
            self.trace_len,
            poseidon2_air::CONSTRAINT_DEGREE,
            params,
        ))
    }

    /// The AIR proving this circuit under `params` (commits the fixed
    /// columns).
    pub fn air(&self, params: &Params) -> CircuitAir {
        self.air_with(self.commit(params))
    }

    /// The AIR proving this circuit, with its fixed columns already
    /// committed (by `commit`, for this very circuit).
    pub fn air_with(&self, preprocessed: Arc<Preprocessed>) -> CircuitAir {
        assert_eq!(preprocessed.columns(), Some(&self.preprocessed[..]), "a different circuit's commitment");
        CircuitAir::new(self.trace_len, preprocessed, self.public.clone())
    }
}

pub struct CircuitAir {
    trace_len: usize,
    preprocessed: Arc<Preprocessed>,
    public: Vec<(BabyBear, Vec<BabyBear>)>,
    chip: Poseidon2Chip<24>,
}

/// Extension multiplication on coefficient arrays, over any field.
fn ext_mul<F: Field>(a: &[F], b: &[F]) -> [F; 4] {
    let w = F::from_base(BabyBear::new(11));
    let mut wide = [F::ZERO; 7];
    for i in 0..4 {
        for j in 0..4 {
            wide[i + j] = wide[i + j] + a[i] * b[j];
        }
    }
    [wide[0] + w * wide[4], wide[1] + w * wide[5], wide[2] + w * wide[6], wide[3]]
}

impl CircuitAir {
    /// A circuit's AIR from its parts: a verifier needs only the fixed
    /// columns' cap (`Preprocessed::from_cap`) and the public tuples.
    pub fn new(trace_len: usize, preprocessed: Arc<Preprocessed>, public: Vec<(BabyBear, Vec<BabyBear>)>) -> Self {
        CircuitAir {
            trace_len,
            preprocessed,
            public,
            chip: Poseidon2Chip::new(),
        }
    }

    pub fn preprocessed_commitment(&self) -> &Arc<Preprocessed> {
        &self.preprocessed
    }

    // Lane-by-lane formulas read clearest indexed.
    #[allow(clippy::needless_range_loop)]
    fn interactions<F: Field>(&self, cur: &[F]) -> Vec<Interaction<F>> {
        let pre = &cur[WITNESS_WIDTH..];
        let v = |i: usize| cur[V + i];
        let two = F::from_base(BabyBear::new(2));
        let b = v(SWAP_BIT);
        let (pin, pout, ar, rp, bt, lk) = (pre[P_IN], pre[P_OUT], pre[ARITH], pre[REPACK], pre[BITS], pre[LOOKUP]);
        let mut slots = [[F::ZERO; 8]; SLOTS];
        for l in 0..8 {
            let (lo, hi) = (v(l), v(8 + l));
            slots[0][l] = pin * (lo + b * (hi - lo)) + (pout + rp + lk) * lo;
            slots[1][l] = pin * (hi - b * (hi - lo)) + pout * hi + lk * lo;
            slots[2][l] = (pin + pout) * v(16 + l);
        }
        for l in 0..4 {
            slots[0][l] = slots[0][l] + ar * v(l);
            slots[1][l] = slots[1][l] + ar * v(4 + l) + rp * v(l);
            slots[2][l] = slots[2][l] + ar * v(8 + l) + rp * v(4 + l);
            slots[3][l] = ar * v(12 + l);
        }
        // Bit step: x (lane 0, other coefficients free), x', b.
        slots[0][0] = slots[0][0] + bt * v(0);
        for l in 1..4 {
            slots[0][l] = slots[0][l] + bt * v(1 + l);
        }
        slots[1][0] = slots[1][0] + bt * v(1);
        slots[2][0] = slots[2][0] + bt * (v(0) - two * v(1)) + lk * v(8);
        slots[3][0] = slots[3][0] + pin * b;
        // Constants: lanes from the fixed columns.
        for l in 0..8 {
            slots[0][l] = slots[0][l] + pre[CONST] * pre[ALPHA + l];
        }
        (0..SLOTS)
            .map(|s| {
                let mut address = pre[ADDR + s];
                if s == 1 {
                    address = address + lk * v(8);
                }
                // Lanes first, address last: a cell's value then lines up
                // with octets when a tuple is laid out in a statement.
                let mut values = slots[s].to_vec();
                values.push(address);
                Interaction {
                    multiplicity: cur[M + s] - pre[RD + s],
                    values,
                }
            })
            .collect()
    }
}

impl Air for CircuitAir {
    fn width(&self) -> usize {
        WITNESS_WIDTH
    }

    fn preprocessed(&self) -> Option<&Preprocessed> {
        Some(&self.preprocessed)
    }

    fn trace_len(&self) -> usize {
        self.trace_len
    }

    fn constraint_degree(&self) -> usize {
        poseidon2_air::CONSTRAINT_DEGREE
    }

    /// The chip's round constants (its round-type selectors are
    /// preprocessed instead, so they're zero off permutation rows).
    fn periodic_columns(&self) -> Vec<Vec<BabyBear>> {
        self.chip.periodic_columns().split_off(3)
    }

    fn num_transition_constraints(&self) -> usize {
        NUM_CONSTRAINTS
    }

    fn eval_transition<F: Field>(&self, cur: &[F], next: &[F], periodic: &[F], out: &mut [F]) {
        let pre = &cur[WITNESS_WIDTH..];
        let mut chip_periodic = vec![pre[SEL], pre[SEL + 1], pre[SEL + 2]];
        chip_periodic.extend_from_slice(periodic);
        self.chip.eval(&cur[V..V + VALUES], &next[V..V + VALUES], &chip_periodic, &mut out[..48]);
        let one = F::ONE;
        let b = cur[V + SWAP_BIT];
        out[48] = pre[P_IN] * b * (b - one);
        out[49] = pre[P_IN] * (one - pre[SW]) * b;

        let (a, bb, d, c) = (&cur[V..V + 4], &cur[V + 4..V + 8], &cur[V + 8..V + 12], &cur[V + 12..V + 16]);
        let ab = ext_mul(a, bb);
        let lanes = (0..4).fold(F::ZERO, |acc, l| acc + pre[LAMBDA + l] * d[l]);
        for j in 0..4 {
            let mut rhs = pre[ALPHA] * ab[j] + pre[BETA] * a[j] + pre[GAMMA] * bb[j] + pre[DELTA] * d[j];
            if j == 0 {
                rhs = rhs + lanes;
            }
            out[50 + j] = pre[ARITH] * (c[j] - rhs);
        }

        let bit = cur[V] - cur[V + 1] - cur[V + 1];
        out[54] = pre[BITS] * bit * (bit - one);
        for s in 0..SLOTS {
            out[55 + s] = (one - pre[WR + s]) * cur[M + s];
        }
    }

    fn boundaries(&self) -> Vec<Boundary> {
        Vec::new()
    }

    fn num_aux_columns(&self) -> usize {
        BUS.num_aux_columns()
    }

    fn num_challenges(&self) -> usize {
        crate::bus::NUM_CHALLENGES
    }

    fn aux_trace(&self, main: &[Vec<BabyBear>], challenges: &[Ext]) -> Vec<Vec<Ext>> {
        BUS.aux_trace(
            self.trace_len,
            |i| {
                let row: Vec<BabyBear> = main.iter().map(|c| c[i]).collect();
                self.interactions(&row)
            },
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
        BUS.boundaries(self.trace_len, BUS.public_sum(&self.public, challenges))
    }

    fn statement(&self) -> Vec<BabyBear> {
        crate::recursion::bus_statement(&self.public)
    }
}

impl crate::recursion::RecursiveAir for CircuitAir {
    fn bus(&self) -> Option<(Bus, crate::recursion::PublicTuples)> {
        Some((BUS, self.public.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark;
    use crate::transcript::Transcript;

    const PARAMS: Params = Params {
        log_blowup: 1,
        num_queries: 20,
        grinding_bits: 0,
        hiding: true,
    };

    fn e(v: u32) -> Ext {
        Ext::from_base(BabyBear::new(v))
    }

    fn octet(start: u32) -> Octet {
        std::array::from_fn(|i| BabyBear::new(start + i as u32))
    }

    fn challenges() -> Vec<Ext> {
        let mut t = Transcript::new(b"circuit test");
        (0..2).map(|_| t.challenge_ext(b"c")).collect()
    }

    /// Exercises every row kind; returns the builder for further tweaks.
    fn sample() -> Builder {
        let mut b = Builder::new();
        // A Merkle-style hash with a swap, checked against the native one.
        let (x, y) = (b.witness_octet(octet(1)), b.witness_octet(octet(100)));
        let cap = b.const_octet(octet(1000));
        let bit = b.witness_ext(e(1));
        let out = b.permute(x, y, cap, Some(bit));
        let mut state = [BabyBear::ZERO; 24];
        state[..8].copy_from_slice(&octet(100));
        state[8..16].copy_from_slice(&octet(1));
        state[16..].copy_from_slice(&octet(1000));
        let expected: Octet = crate::poseidon2::perm24().permute(state)[..8].try_into().unwrap();
        let expected = b.const_octet(expected);
        b.assert_eq_octet(out[0], expected);
        // Arithmetic, checked against native arithmetic.
        let (p, q) = (Ext([1, 2, 3, 4].map(BabyBear::new)), Ext([5, 6, 7, 8].map(BabyBear::new)));
        let (pv, qv) = (b.witness_ext(p), b.witness_ext(q));
        let r = b.mul_add(pv, qv, pv);
        let want = b.const_ext(p * q + p);
        b.assert_eq(r, want);
        let inv = b.inverse(qv);
        assert_eq!(b.ext_value(inv), q.inverse());
        let l = b.lane(qv, 2);
        let seven = b.const_base(BabyBear::new(7));
        b.assert_eq(l, seven);
        // Bits of 6 = 0b110, and a lookup by the result.
        let six = b.witness_ext(e(6));
        let (three, low) = b.bit_step(six);
        b.assert_zero(low);
        let table = b.witness_ext_table(&[e(10), e(20), e(30), e(40)]);
        let thirty = b.const_ext(e(30));
        let (one, _) = b.bit_step(three);
        let two = b.add(one, one);
        b.lookup_ext(thirty, table, two);
        b
    }

    #[test]
    fn a_circuit_using_every_row_kind_satisfies_its_constraints_and_proves() {
        let circuit = sample().finish();
        let air = circuit.air(&PARAMS);
        stark::check(&air, &circuit.witness, &challenges()).unwrap();
        let proof = stark::prove(&air, &circuit.witness, &PARAMS, [3; 32]).unwrap();
        assert!(stark::verify(&air, &proof, &PARAMS));
    }

    #[test]
    fn tampered_values_break_the_bus() {
        let circuit = sample().finish();
        let air = circuit.air(&PARAMS);
        // Change a value each row kind relies on, at the first row of
        // that kind, and confirm the check fails for each.
        let first = |kind: usize| (0..circuit.trace_len).find(|&r| circuit.preprocessed[kind][r] == BabyBear::ONE).unwrap();
        let cases = [
            (V, first(P_IN)),           // permutation input
            (V + 3, first(P_OUT)),      // permutation output
            (V + 12, first(ARITH)),     // arithmetic result
            (V + 5, first(REPACK)),     // a repacked lane
            (V + 1, first(BITS)),       // a bit step's half
            (V + 8, first(LOOKUP)),     // a lookup index
            (M, first(CONST)),          // a constant's multiplicity
        ];
        for (column, row) in cases {
            let mut witness = circuit.witness.clone();
            witness[column][row] = witness[column][row] + BabyBear::ONE;
            assert!(stark::check(&air, &witness, &challenges()).is_err(), "column {column} row {row}");
        }
    }

    #[test]
    fn a_wrong_public_value_is_refused() {
        let ten = ext_octet(e(10));
        let (mut b, public) = Builder::with_public(&[ten]);
        let x = b.witness_ext(e(5));
        let y = b.add(x, x);
        let (claimed, _) = b.halves(public[0]);
        b.assert_eq(y, claimed);
        let mut circuit = b.finish();
        let air = circuit.air(&PARAMS);
        stark::check(&air, &circuit.witness, &challenges()).unwrap();
        // Public cells sit at the first addresses, read exactly once,
        // address last in the tuple.
        assert_eq!(circuit.public, vec![(-BabyBear::ONE, [&ten[..], &[BabyBear::ZERO]].concat())]);
        // The same trace against a statement saying the input is 11.
        circuit.public[0].1[0] = BabyBear::new(11);
        let air = circuit.air(&PARAMS);
        assert!(matches!(
            stark::check(&air, &circuit.witness, &challenges()),
            Err(stark::Error::AuxBoundaryViolated(_))
        ));
    }

    /// Constants are part of the circuit (fixed columns), not the
    /// statement: a circuit with a different constant is a different
    /// circuit, and a trace can't claim another value for one.
    #[test]
    fn constants_live_in_the_fixed_columns() {
        let build = |k: u32| {
            let mut b = Builder::new();
            let x = b.witness_ext(e(5));
            let y = b.add(x, x);
            let c = b.const_ext(e(k));
            b.assert_eq(y, c);
            b
        };
        let circuit = build(10).finish();
        assert!(circuit.public.is_empty());
        let air = circuit.air(&PARAMS);
        stark::check(&air, &circuit.witness, &challenges()).unwrap();
        let mut b = Builder::new();
        let x = b.witness_ext(e(5));
        let y = b.add(x, x);
        let c = b.const_ext(e(10));
        b.assert_eq(y, c);
        assert_eq!(b.finish().preprocessed, circuit.preprocessed);
        // Rows: witness, add, constant, assert. Changing how often the
        // constant's write claims to be read breaks the bus.
        let mut witness = circuit.witness.clone();
        witness[M][2] = witness[M][2] + BabyBear::ONE;
        assert!(stark::check(&air, &witness, &challenges()).is_err());
        assert!(std::panic::catch_unwind(|| build(11)).is_err(), "a false assertion can't be built");
    }

    #[test]
    fn the_fixed_columns_do_not_depend_on_witness_values() {
        let build = |seed: u32| {
            let mut b = Builder::new();
            let x = b.witness_octet(octet(seed));
            let z = b.const_octet(octet(0));
            let out = b.permute(x, x, z, None);
            let (lo, _) = b.halves(out[0]);
            let sq = b.mul(lo, lo);
            b.add(sq, lo);
            b.finish()
        };
        assert_eq!(build(1).preprocessed, build(77).preprocessed);
        assert_ne!(build(1).witness, build(77).witness);
    }
}
