//! A STARK: proof that an execution trace -- a table of BabyBear values,
//! `width` columns by `trace_len` rows -- satisfies an `Air`'s rules
//! (transition constraints between consecutive rows, plus fixed values
//! at given cells), revealing only a small number of random openings.
//!
//! # Protocol (DEEP-ALI with FRI)
//!
//! 0. (Optionally, see "Two phases" below.)
//! 1. Each trace column is interpolated (`ntt`) and re-evaluated over a
//!    larger coset -- the *low-degree extension*, `2^log_blowup` times
//!    bigger than the composition polynomial's degree bound. Rows of the
//!    extension are committed in one Merkle tree.
//! 2. With a challenge `alpha`, every constraint is divided by the
//!    polynomial vanishing where it must hold, and the quotients are
//!    summed with weights `alpha^k` into one *composition polynomial*
//!    `C`, also evaluated over the coset and committed. If (and, up to
//!    negligible luck, only if) every constraint holds, every quotient is
//!    a genuine polynomial, so `C` is low-degree.
//! 3. A random out-of-domain point `z` is drawn. The prover states each
//!    column's value at `z` and `z·g` (the "next row"), and `C(z)`; the
//!    verifier checks those are consistent: the constraints evaluated on
//!    the stated values reproduce `C(z)`.
//! 4. With a challenge `beta`, the DEEP quotients `(T(x) - T(z)) / (x - z)`
//!    (and likewise for `z·g`, and for `C`) are combined into one
//!    polynomial, which is low-degree only if every stated value is
//!    honest. FRI proves it is.
//! 5. At each FRI query point, the prover opens the trace and composition
//!    commitments; the verifier recomputes the DEEP combination there
//!    and checks FRI saw the same value.
//!
//! # Two phases
//!
//! Some statements need randomness *after* the trace is fixed -- most
//! importantly a multiset check ("these values are a rearrangement of
//! those"), done as a running product of `(gamma - value)` with `gamma`
//! drawn only once the values can no longer change. So an AIR may declare
//! *auxiliary* columns: once the main trace is committed, `num_challenges`
//! extension challenges are drawn, the AIR builds its auxiliary columns
//! from the main trace and those challenges (`Air::aux_trace`), and they
//! are committed in turn -- before `alpha`. They're extension-field
//! columns with their own transition constraints and boundaries (which may
//! depend on the challenges), and are otherwise treated exactly like the
//! main trace: blinded, extended, opened at `z`/`z·g`, folded into DEEP,
//! and opened at every query.
//!
//! # Preprocessed columns
//!
//! An AIR may also declare *preprocessed* columns (`Air::preprocessed`):
//! fixed, public columns -- a circuit's wiring, say -- committed once, for
//! given parameters, by whoever defines the AIR. Their cap is part of the
//! statement (a verifier needs only the cap, never the columns), and
//! constraints see them as extra main columns after the witness ones: every
//! "row" handed to `eval_transition`, `aux_trace` and the boundaries is
//! witness columns then preprocessed columns. They're opened at `z`, `z·g`
//! and every query like the trace (their values at `z`/`z·g` follow the
//! trace's in `trace_at_z`/`trace_at_zg`), but from their own tree, and not
//! blinded: they're public.
//!
//! All challenges come from a Fiat-Shamir `Transcript` that has first
//! absorbed the whole public statement (`Air::statement`), so a proof is
//! bound to the exact claim it was made for.
//!
//! Challenges live in the degree-4 extension (`ext`): see its docs on
//! why BabyBear alone is too small. Soundness is about
//! `log_blowup * num_queries` bits (FRI's conjectured bound).
//!
//! # Zero knowledge
//!
//! The witness is hidden by two layers of randomness, both from a seed
//! the prover supplies (`prove`'s `seed` -- fresh random bytes each time):
//!
//! - **Random rows.** Each column is interpolated over a domain *twice*
//!   the trace length, real rows on the even positions and fresh random
//!   values on the odd ones. The even positions are exactly the order-`n`
//!   subgroup the constraints are checked on, so the polynomial still
//!   equals the trace there and nothing about the constraints changes --
//!   but it now has `n` random degrees of freedom. Any `n` or fewer of
//!   its evaluations *off* the trace rows are then uniformly random,
//!   whatever the trace. Everything this proof reveals about the trace
//!   is a function of its values at a small set of such points: the
//!   opened rows at each query and their next-row neighbours (which the
//!   opened composition values depend on), and the values at `z` and
//!   `z·g` -- under `4 * num_queries + 2` points in all. So when
//!   `trace_len` exceeds that, those values are distributed identically
//!   for every valid witness.
//! - **A random mask in FRI.** FRI's deeper layers reveal combinations of
//!   the DEEP polynomial at many more points than the queries. A random
//!   polynomial below FRI's degree bound is committed and added into the
//!   DEEP combination as one more batched term, so every value FRI
//!   reveals is masked by it. Being one more term of the same random
//!   (`beta`-weighted) combination, it doesn't weaken soundness: the sum
//!   is low-degree only if every term is. FRI reveals two values per
//!   query per fold round; the mask hides them all while its degree bound
//!   exceeds that count.
//!
//! `hides` checks both conditions. Real block statements have traces
//! far larger than either threshold; small test traces may not.

#![allow(dead_code)]

use crate::ext::{Ext, batch_inverse};
use crate::field::Field;
use crate::fri::{self, coset_domain, domain_generator};
use crate::merkle::{Hash, MerkleTree, Opening};
use crate::ntt::{coset_evaluate, coset_interpolate, evaluate_at, intt};
use crate::poseidon2::BabyBear;
use crate::transcript::Transcript;

/// The coset shift for the low-degree extension: BabyBear's multiplicative
/// generator (Plonky3's choice too). Its order isn't a power of two, so
/// the coset never meets any power-of-two subgroup -- in particular, not
/// the trace domain, where constraint quotients would divide by zero.
pub const COSET_SHIFT: BabyBear = BabyBear::new_const(31);

pub(crate) const STATEMENT_LABEL: &[u8] = b"stark-statement";
pub(crate) const TRACE_ROOT_LABEL: &[u8] = b"stark-trace-root";
pub(crate) const ALPHA_LABEL: &[u8] = b"stark-alpha";
pub(crate) const COMPOSITION_ROOT_LABEL: &[u8] = b"stark-composition-root";
pub(crate) const Z_LABEL: &[u8] = b"stark-z";
pub(crate) const OOD_LABEL: &[u8] = b"stark-ood";
pub(crate) const AUX_CHALLENGE_LABEL: &[u8] = b"stark-aux-challenge";
pub(crate) const AUX_ROOT_LABEL: &[u8] = b"stark-aux-root";
pub(crate) const BETA_LABEL: &[u8] = b"stark-beta";
pub(crate) const PREPROCESSED_ROOT_LABEL: &[u8] = b"stark-preprocessed-root";
pub(crate) const PUBLIC_LABEL: &[u8] = b"stark-public";

/// A cell that must hold a fixed, public value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Boundary {
    pub row: usize,
    pub column: usize,
    pub value: BabyBear,
}

/// A cell of an auxiliary column that must hold a given value (which may
/// depend on the challenges).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuxBoundary {
    pub row: usize,
    pub column: usize,
    pub value: Ext,
}

/// Everything an auxiliary transition constraint can read at one row:
/// the main and auxiliary values of this row and the next, the periodic
/// values, and the challenges. Generic over the field like
/// `eval_transition`: `Ext` when proving and verifying, a symbolic
/// expression when compiling the constraints to a program (`symbolic`).
pub struct AuxFrame<'a, F> {
    pub main_current: &'a [F],
    pub main_next: &'a [F],
    pub aux_current: &'a [F],
    pub aux_next: &'a [F],
    pub periodic: &'a [F],
    pub challenges: &'a [F],
}

/// Fixed public columns, committed for one set of parameters (see
/// "Preprocessed columns" in the module docs). A prover needs the full
/// commitment (`commit`); a verifier only the cap (`from_cap`).
pub struct Preprocessed {
    pub num_columns: usize,
    pub log_lde: usize,
    pub cap: Vec<Hash>,
    prover: Option<PreprocessedData>,
}

struct PreprocessedData {
    columns: Vec<Vec<BabyBear>>,
    coeffs: Vec<Vec<BabyBear>>,
    tree: MerkleTree,
}

impl Preprocessed {
    /// Commit `columns` (each `trace_len` values) as `air`'s preprocessed
    /// columns would be under `params`.
    pub fn commit(columns: Vec<Vec<BabyBear>>, trace_len: usize, constraint_degree: usize, params: &Params) -> Self {
        let log_lde = lde_bits(trace_len, constraint_degree, params).expect("trace too large");
        assert!(columns.iter().all(|c| c.len() == trace_len));
        let coeffs: Vec<Vec<BabyBear>> = crate::parallel::map_each(columns.len(), |c| {
            let mut coeffs = columns[c].clone();
            intt(&mut coeffs);
            coeffs
        });
        let slices = Slices::new(log_lde, params.log_blowup);
        let tree = slices.commit(|r| slices.eval_all(&coeffs, r));
        Preprocessed {
            num_columns: columns.len(),
            log_lde,
            cap: tree.cap(fri::CAP_HEIGHT),
            prover: Some(PreprocessedData { columns, coeffs, tree }),
        }
    }

    /// What a verifier needs: just the shape and the cap.
    pub fn from_cap(num_columns: usize, log_lde: usize, cap: Vec<Hash>) -> Self {
        Preprocessed {
            num_columns,
            log_lde,
            cap,
            prover: None,
        }
    }

    /// The columns themselves, if this is a prover's commitment.
    pub fn columns(&self) -> Option<&[Vec<BabyBear>]> {
        self.prover.as_ref().map(|d| &d.columns[..])
    }
}

/// The rules a trace must satisfy -- the statement being proven.
pub trait Air {
    /// Number of (witness) trace columns -- not counting preprocessed ones.
    fn width(&self) -> usize;

    /// Fixed public columns, if any; constraints see them after the
    /// witness columns.
    fn preprocessed(&self) -> Option<&Preprocessed> {
        None
    }

    /// Number of rows: a power of two, at least 2.
    fn trace_len(&self) -> usize;

    /// An upper bound on every transition constraint's degree -- main and
    /// auxiliary alike -- as a polynomial in the current/next row and
    /// periodic values.
    fn constraint_degree(&self) -> usize;

    /// Columns of public, fixed values that repeat down the trace -- round
    /// constants, say. Each has a power-of-two length dividing
    /// `trace_len`; row `i` sees `column[i % len]`.
    fn periodic_columns(&self) -> Vec<Vec<BabyBear>> {
        Vec::new()
    }

    fn num_transition_constraints(&self) -> usize;

    /// Write each transition constraint's value into `out`. Every one must
    /// be zero for every pair of consecutive rows (`current` = row `i`,
    /// `next` = row `i + 1`, for `i < trace_len - 1`); `periodic` holds
    /// row `i`'s periodic values. Generic over the field so the very same
    /// code runs when proving (BabyBear) and verifying (extension).
    fn eval_transition<F: Field>(&self, current: &[F], next: &[F], periodic: &[F], out: &mut [F]);

    fn boundaries(&self) -> Vec<Boundary>;

    /// Auxiliary (extension-field) columns, built after the main trace is
    /// committed -- see "Two phases" in the module docs. None by default.
    fn num_aux_columns(&self) -> usize {
        0
    }

    /// Extension challenges drawn before the auxiliary columns are built.
    fn num_challenges(&self) -> usize {
        0
    }

    /// Build the auxiliary columns (`trace_len` values each) from the
    /// main trace (column-major) and the challenges.
    fn aux_trace(&self, _main: &[Vec<BabyBear>], _challenges: &[Ext]) -> Vec<Vec<Ext>> {
        Vec::new()
    }

    fn num_aux_constraints(&self) -> usize {
        0
    }

    /// The auxiliary transition constraints, which -- like the main ones --
    /// must be zero for every consecutive pair of rows. Evaluated over the
    /// extension (auxiliary values and challenges live there), or
    /// symbolically.
    fn eval_aux_transition<F: Field>(&self, _frame: &AuxFrame<F>, _out: &mut [F]) {}

    /// Fixed values in auxiliary columns. These may depend on the
    /// challenges, so whatever public data they're computed from must be
    /// covered by `statement`.
    fn aux_boundaries(&self, _challenges: &[Ext]) -> Vec<AuxBoundary> {
        Vec::new()
    }

    /// Field elements that pin down *which* statement this is, absorbed into the
    /// transcript before anything else. The shape and boundaries are
    /// absorbed automatically; this is for anything else that
    /// distinguishes one instance from another (an AIR's name, say).
    fn statement(&self) -> Vec<BabyBear> {
        Vec::new()
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Params {
    /// `log2` of the low-degree extension's size over the composition
    /// degree bound.
    pub log_blowup: usize,
    pub num_queries: usize,
    /// Proof-of-work bits required before the queries are drawn (see
    /// `fri`'s docs) -- each one worth a bit of soundness.
    pub grinding_bits: u32,
}

impl Params {
    pub(crate) fn fri(&self) -> fri::Settings {
        fri::Settings {
            log_blowup: self.log_blowup,
            num_queries: self.num_queries,
            grinding_bits: self.grinding_bits,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// The trace has the wrong shape for the AIR.
    WrongShape,
    /// The trace violates the transition constraint `index` going from
    /// `row` to `row + 1`.
    TransitionViolated { row: usize, index: usize },
    /// The trace violates a boundary constraint.
    BoundaryViolated(Boundary),
    /// The auxiliary trace has the wrong shape for the AIR.
    WrongAuxShape,
    /// The auxiliary trace violates auxiliary constraint `index` going
    /// from `row` to `row + 1`.
    AuxTransitionViolated { row: usize, index: usize },
    /// The auxiliary trace violates an auxiliary boundary.
    AuxBoundaryViolated(AuxBoundary),
    /// The domains needed exceed BabyBear's 2-adicity.
    TooLarge,
    /// The AIR declares preprocessed columns but holds only their cap.
    NoPreprocessedData,
}

/// The openings one FRI query needs from the trace and composition
/// commitments: at the query's point (`low`) and its negation (`high`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QueryOpenings {
    pub trace: Opening,
    /// Present exactly when the AIR has preprocessed columns.
    pub preprocessed: Option<Opening>,
    pub aux: Opening,
    pub composition: Opening,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    /// Each commitment is a Merkle cap (see `fri::CAP_HEIGHT`).
    pub trace_cap: Vec<Hash>,
    /// The auxiliary columns' commitment (rows of nothing, for an AIR
    /// without any).
    pub aux_cap: Vec<Hash>,
    pub composition_cap: Vec<Hash>,
    /// Each column's value at `z`.
    pub trace_at_z: Vec<Ext>,
    /// Each column's value at `z·g` (the next row).
    pub trace_at_zg: Vec<Ext>,
    pub aux_at_z: Vec<Ext>,
    pub aux_at_zg: Vec<Ext>,
    pub composition_at_z: Ext,
    pub fri: fri::Proof,
    pub queries: Vec<QueryOpenings>,
}

impl Proof {
    /// Roughly how many bytes this proof would take on the wire: every
    /// hash, value, and opening it carries, with no framing. A planning
    /// figure until proofs get a real encoding.
    pub fn approximate_size(&self) -> usize {
        let opening = |o: &Opening| o.leaf.len() + 32 * o.siblings.len() + 8;
        let ood = 16 * (self.trace_at_z.len() + self.trace_at_zg.len() + self.aux_at_z.len() + self.aux_at_zg.len() + 1);
        let fri_queries: usize = self
            .fri
            .query_proofs
            .iter()
            .flat_map(|q| &q.openings)
            .map(opening)
            .sum();
        let queries: usize = self
            .queries
            .iter()
            .map(|q| {
                opening(&q.trace) + q.preprocessed.as_ref().map_or(0, opening) + opening(&q.aux) + opening(&q.composition)
            })
            .sum();
        let caps: usize = [&self.trace_cap, &self.aux_cap, &self.composition_cap]
            .into_iter()
            .chain(&self.fri.caps)
            .map(|c| 4 + 32 * c.len())
            .sum();
        caps + ood + 16 + 8 + fri_queries + queries
    }
}

/// Byte encoding for proofs: little-endian `u32` lengths and indices,
/// fixed-size hashes and extension elements, every list length-prefixed.
/// Decoding is strict -- every length is checked against the bytes actually
/// left before anything is allocated, and nothing may remain at the end --
/// since proofs arrive from untrusted peers.
mod codec {
    use crate::ext::Ext;
    use crate::fri::{self, FriQueryProof};
    use crate::merkle::{Hash, Opening};

    /// The fewest bytes an encoded opening can take: index, leaf length,
    /// an empty leaf, and no siblings.
    pub const MIN_OPENING: usize = 4 + 4 + 1;

    #[derive(Default)]
    pub struct Writer(pub Vec<u8>);

    impl Writer {
        pub fn u32(&mut self, v: usize) {
            self.0.extend_from_slice(&(v as u32).to_le_bytes());
        }
        pub fn hash(&mut self, h: &Hash) {
            self.0.extend_from_slice(h);
        }
        pub fn hashes(&mut self, hashes: &[Hash]) {
            self.u32(hashes.len());
            for h in hashes {
                self.hash(h);
            }
        }
        pub fn ext(&mut self, e: Ext) {
            self.0.extend_from_slice(&e.to_bytes());
        }
        pub fn exts(&mut self, values: &[Ext]) {
            self.u32(values.len());
            for &v in values {
                self.ext(v);
            }
        }
        pub fn opening(&mut self, o: &Opening) {
            self.u32(o.index);
            self.u32(o.leaf.len());
            self.0.extend_from_slice(&o.leaf);
            self.0.push(o.siblings.len() as u8);
            for s in &o.siblings {
                self.hash(s);
            }
        }
        pub fn fri(&mut self, proof: &fri::Proof) {
            self.u32(proof.caps.len());
            for cap in &proof.caps {
                self.hashes(cap);
            }
            self.ext(proof.final_value);
            self.0.extend_from_slice(&proof.grinding_nonce.to_le_bytes());
            self.u32(proof.query_proofs.len());
            for q in &proof.query_proofs {
                self.u32(q.openings.len());
                for o in &q.openings {
                    self.opening(o);
                }
            }
        }
    }

    pub struct Reader<'a> {
        bytes: &'a [u8],
        pos: usize,
    }

    impl<'a> Reader<'a> {
        pub fn new(bytes: &'a [u8]) -> Self {
            Reader { bytes, pos: 0 }
        }
        pub fn take(&mut self, n: usize) -> Option<&'a [u8]> {
            let end = self.pos.checked_add(n)?;
            let out = self.bytes.get(self.pos..end)?;
            self.pos = end;
            Some(out)
        }
        pub fn remaining(&self) -> usize {
            self.bytes.len() - self.pos
        }
        pub fn finished(&self) -> bool {
            self.pos == self.bytes.len()
        }
        pub fn u32(&mut self) -> Option<usize> {
            Some(u32::from_le_bytes(self.take(4)?.try_into().unwrap()) as usize)
        }
        /// A list length, refused if even `min_item` bytes per item
        /// wouldn't fit in what's left.
        pub fn len(&mut self, min_item: usize) -> Option<usize> {
            let n = self.u32()?;
            (n.checked_mul(min_item)? <= self.remaining()).then_some(n)
        }
        pub fn hash(&mut self) -> Option<Hash> {
            Some(self.take(32)?.try_into().unwrap())
        }
        pub fn hashes(&mut self) -> Option<Vec<Hash>> {
            let n = self.len(32)?;
            (0..n).map(|_| self.hash()).collect()
        }
        pub fn ext(&mut self) -> Option<Ext> {
            Some(Ext::from_bytes(self.take(16)?.try_into().unwrap()))
        }
        pub fn exts(&mut self) -> Option<Vec<Ext>> {
            let n = self.len(16)?;
            (0..n).map(|_| self.ext()).collect()
        }
        pub fn opening(&mut self) -> Option<Opening> {
            let index = self.u32()?;
            let leaf_len = self.len(1)?;
            let leaf = self.take(leaf_len)?.to_vec();
            let depth = self.take(1)?[0] as usize;
            let siblings = (0..depth).map(|_| self.hash()).collect::<Option<_>>()?;
            Some(Opening { index, leaf, siblings })
        }
        pub fn fri(&mut self) -> Option<fri::Proof> {
            let rounds = self.len(4)?;
            let caps = (0..rounds).map(|_| self.hashes()).collect::<Option<_>>()?;
            let final_value = self.ext()?;
            let grinding_nonce = u64::from_le_bytes(self.take(8)?.try_into().unwrap());
            let queries = self.len(4)?;
            let query_proofs = (0..queries)
                .map(|_| {
                    let n = self.len(MIN_OPENING)?;
                    let openings = (0..n).map(|_| self.opening()).collect::<Option<_>>()?;
                    Some(FriQueryProof { openings })
                })
                .collect::<Option<_>>()?;
            Some(fri::Proof {
                caps,
                final_value,
                grinding_nonce,
                query_proofs,
            })
        }
    }
}

impl Proof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut w = codec::Writer::default();
        for cap in [&self.trace_cap, &self.aux_cap, &self.composition_cap] {
            w.hashes(cap);
        }
        for values in [&self.trace_at_z, &self.trace_at_zg, &self.aux_at_z, &self.aux_at_zg] {
            w.exts(values);
        }
        w.ext(self.composition_at_z);
        w.fri(&self.fri);
        w.u32(self.queries.len());
        for q in &self.queries {
            w.opening(&q.trace);
            w.0.push(q.preprocessed.is_some() as u8);
            if let Some(o) = &q.preprocessed {
                w.opening(o);
            }
            w.opening(&q.aux);
            w.opening(&q.composition);
        }
        w.0
    }

    /// Decode a proof, or `None` if the bytes aren't exactly one. Says
    /// nothing about whether it *verifies* -- that's `verify`'s job.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut r = codec::Reader::new(bytes);
        let trace_cap = r.hashes()?;
        let aux_cap = r.hashes()?;
        let composition_cap = r.hashes()?;
        let trace_at_z = r.exts()?;
        let trace_at_zg = r.exts()?;
        let aux_at_z = r.exts()?;
        let aux_at_zg = r.exts()?;
        let composition_at_z = r.ext()?;
        let fri = r.fri()?;
        let n = r.len(3 * codec::MIN_OPENING + 1)?;
        let queries = (0..n)
            .map(|_| {
                let trace = r.opening()?;
                let preprocessed = match r.take(1)?[0] {
                    0 => None,
                    1 => Some(r.opening()?),
                    _ => return None,
                };
                Some(QueryOpenings {
                    trace,
                    preprocessed,
                    aux: r.opening()?,
                    composition: r.opening()?,
                })
            })
            .collect::<Option<_>>()?;
        if !r.finished() {
            return None;
        }
        Some(Proof {
            trace_cap,
            aux_cap,
            composition_cap,
            trace_at_z,
            trace_at_zg,
            aux_at_z,
            aux_at_zg,
            composition_at_z,
            fri,
            queries,
        })
    }
}

/// The sizes everything is derived from.
pub(crate) struct Layout {
    pub(crate) log_n: usize,
    /// `log2` of the composition degree bound over `n`.
    pub(crate) log_composition_factor: usize,
    /// `log2` of the low-degree extension size.
    pub(crate) log_lde: usize,
}

/// `log2` of the low-degree extension for a trace of `n` rows.
fn lde_bits(n: usize, constraint_degree: usize, params: &Params) -> Option<usize> {
    if !n.is_power_of_two() || n < 2 {
        return None;
    }
    let factor = (2 * constraint_degree.max(1)).next_power_of_two();
    let log_lde = n.trailing_zeros() as usize + factor.trailing_zeros() as usize + params.log_blowup;
    (log_lde <= fri::MAX_TWO_ADICITY && params.log_blowup >= 1).then_some(log_lde)
}

/// Witness plus preprocessed columns: the row width constraints see.
pub fn full_width<A: Air>(air: &A) -> usize {
    air.width() + air.preprocessed().map_or(0, |p| p.num_columns)
}

/// The witness columns followed by the preprocessed ones -- the "main
/// trace" as constraints see it.
fn full_trace<A: Air>(air: &A, trace: &[Vec<BabyBear>]) -> Result<Vec<Vec<BabyBear>>, Error> {
    let mut all = trace.to_vec();
    if let Some(p) = air.preprocessed() {
        all.extend_from_slice(p.columns().ok_or(Error::NoPreprocessedData)?);
    }
    Ok(all)
}

pub(crate) fn layout<A: Air>(air: &A, params: &Params) -> Option<Layout> {
    let n = air.trace_len();
    if !n.is_power_of_two() || n < 2 {
        return None;
    }
    let log_n = n.trailing_zeros() as usize;
    // Trace polynomials have degree < 2n (the random rows -- see the
    // module docs), so a degree-D constraint has degree < 2D·n, and its
    // quotient by the (degree n - 1) transition divisor stays below that.
    let factor = (2 * air.constraint_degree().max(1)).next_power_of_two();
    let log_composition_factor = factor.trailing_zeros() as usize;
    let log_lde = log_n + log_composition_factor + params.log_blowup;
    if air.preprocessed().is_some_and(|p| p.log_lde != log_lde) {
        return None;
    }
    (log_lde <= fri::MAX_TWO_ADICITY && params.log_blowup >= 1).then_some(Layout {
        log_n,
        log_composition_factor,
        log_lde,
    })
}

/// Whether `air` is big enough, under `params`, for both layers of
/// randomness to hide the witness completely (see the module docs): the
/// random rows must outnumber the trace points revealed (under
/// `4 * num_queries + 2`), and the FRI mask's degrees of freedom must
/// outnumber the values FRI reveals (two per query per fold round).
pub fn hides<A: Air>(air: &A, params: &Params) -> bool {
    let Some(layout) = layout(air, params) else {
        return false;
    };
    let fri_degree_bound = 1usize << (layout.log_lde - params.log_blowup);
    let fri_revealed = params.num_queries * fri::revealed_per_query(layout.log_lde, params.log_blowup);
    air.trace_len() > 4 * params.num_queries + 2 && fri_degree_bound > fri_revealed
}

/// A deterministic stream of field elements expanded from the prover's
/// seed -- Poseidon2 over (seed, counter), eight elements per hash.
struct Randomness {
    seed: [u8; 32],
    counter: u64,
    buffer: Vec<BabyBear>,
}

impl Randomness {
    /// An independent stream for one purpose (a column, the mask) --
    /// derived from the prover's seed and a label, so streams can be drawn
    /// in parallel and none can be predicted from another.
    fn stream(seed: [u8; 32], purpose: &[u8], index: usize) -> Self {
        let mut input = seed.to_vec();
        input.extend_from_slice(purpose);
        input.extend_from_slice(&(index as u64).to_le_bytes());
        Randomness::new(crate::poseidon2::hash_bytes_32(&input))
    }

    fn new(seed: [u8; 32]) -> Self {
        Randomness {
            seed,
            counter: 0,
            buffer: Vec::new(),
        }
    }

    fn next(&mut self) -> BabyBear {
        if self.buffer.is_empty() {
            let mut input = [0u8; 40];
            input[..32].copy_from_slice(&self.seed);
            input[32..].copy_from_slice(&self.counter.to_le_bytes());
            self.counter += 1;
            let digest = crate::poseidon2::hash_bytes_32(&input);
            self.buffer = digest
                .chunks_exact(4)
                .map(|c| BabyBear::from_bytes(c.try_into().unwrap()))
                .collect();
        }
        self.buffer.pop().unwrap()
    }

    fn next_ext(&mut self) -> Ext {
        Ext([self.next(), self.next(), self.next(), self.next()])
    }
}

/// The AIR's shape -- what `start_transcript` absorbs first: sizes,
/// periodic columns, boundaries.
pub(crate) fn shape_elements<A: Air>(air: &A) -> Vec<BabyBear> {
    let n = |v: usize| BabyBear::new(v as u32);
    let mut shape = vec![
        n(air.width()),
        n(air.trace_len()),
        n(air.constraint_degree()),
        n(air.num_transition_constraints()),
        n(air.num_aux_columns()),
        n(air.num_challenges()),
        n(air.num_aux_constraints()),
        n(air.preprocessed().map_or(0, |p| p.num_columns)),
    ];
    for column in air.periodic_columns() {
        shape.push(n(column.len()));
        shape.extend(column);
    }
    for b in air.boundaries() {
        shape.extend([n(b.row), n(b.column), b.value]);
    }
    shape
}

/// A transcript that has absorbed the whole statement, each part
/// starting on a fresh octet (so a circuit replaying it can use each
/// part's cells directly): the shape, the preprocessed columns' cap, and
/// the AIR's own statement.
fn start_transcript<A: Air>(air: &A) -> Transcript {
    let mut t = Transcript::new(STATEMENT_LABEL);
    t.absorb(STATEMENT_LABEL, &shape_elements(air));
    if let Some(p) = air.preprocessed() {
        t.absorb_digests(PREPROCESSED_ROOT_LABEL, &p.cap);
    }
    t.absorb(PUBLIC_LABEL, &air.statement());
    t
}

fn row_bytes<F: Copy>(row: &[F], to_bytes: impl Fn(F) -> Vec<u8>) -> Vec<u8> {
    row.iter().flat_map(|&v| to_bytes(v)).collect()
}

fn decode_row(leaf: &[u8], width: usize) -> Option<Vec<BabyBear>> {
    if leaf.len() != 4 * width {
        return None;
    }
    Some(
        leaf.chunks_exact(4)
            .map(|c| BabyBear::from_bytes(c.try_into().unwrap()))
            .collect(),
    )
}

fn decode_ext_row(leaf: &[u8], width: usize) -> Option<Vec<Ext>> {
    if leaf.len() != 16 * width {
        return None;
    }
    Some(
        leaf.chunks_exact(16)
            .map(|c| Ext::from_bytes(c.try_into().unwrap()))
            .collect(),
    )
}

fn decode_ext(leaf: &[u8]) -> Option<Ext> {
    Some(Ext::from_bytes(leaf.try_into().ok()?))
}

/// Each periodic column's coefficients, as a polynomial in
/// `y = x^(n / len)`: the column repeats every `len` rows, so its value at
/// trace point `x` is that polynomial at `x^(n / len)`.
pub(crate) fn periodic_polys(columns: &[Vec<BabyBear>], n: usize) -> Vec<(usize, Vec<BabyBear>)> {
    columns
        .iter()
        .map(|column| {
            assert!(
                column.len().is_power_of_two() && n.is_multiple_of(column.len()),
                "periodic column length must be a power of two dividing the trace length"
            );
            let mut coeffs = column.clone();
            intt(&mut coeffs);
            (n / column.len(), coeffs)
        })
        .collect()
}

fn periodic_at<F: Field>(polys: &[(usize, Vec<BabyBear>)], x: F) -> Vec<F> {
    polys
        .iter()
        .map(|(exponent, coeffs)| {
            let mut y = F::ONE;
            let mut base = x;
            let mut e = *exponent;
            while e > 0 {
                if e & 1 == 1 {
                    y = y * base;
                }
                base = base * base;
                e >>= 1;
            }
            let lifted: Vec<F> = coeffs.iter().map(|&c| F::from_base(c)).collect();
            evaluate_at(&lifted, y)
        })
        .collect()
}

/// Check `trace` satisfies `air` directly, row by row.
fn check_trace<A: Air>(air: &A, trace: &[Vec<BabyBear>]) -> Result<(), Error> {
    let n = air.trace_len();
    if trace.len() != full_width(air) || trace.iter().any(|c| c.len() != n) {
        return Err(Error::WrongShape);
    }
    let periodic = air.periodic_columns();
    let mut out = vec![BabyBear::ZERO; air.num_transition_constraints()];
    for row in 0..n - 1 {
        let current: Vec<BabyBear> = trace.iter().map(|c| c[row]).collect();
        let next: Vec<BabyBear> = trace.iter().map(|c| c[row + 1]).collect();
        let p: Vec<BabyBear> = periodic.iter().map(|c| c[row % c.len()]).collect();
        air.eval_transition(&current, &next, &p, &mut out);
        if let Some(index) = out.iter().position(|&v| v != BabyBear::ZERO) {
            return Err(Error::TransitionViolated { row, index });
        }
    }
    for b in air.boundaries() {
        if b.column >= trace.len() || b.row >= n || trace[b.column][b.row] != b.value {
            return Err(Error::BoundaryViolated(b));
        }
    }
    Ok(())
}

/// Check the auxiliary trace satisfies `air`'s auxiliary constraints,
/// row by row.
fn check_aux<A: Air>(air: &A, main: &[Vec<BabyBear>], aux: &[Vec<Ext>], challenges: &[Ext]) -> Result<(), Error> {
    let n = air.trace_len();
    if aux.len() != air.num_aux_columns() || aux.iter().any(|c| c.len() != n) {
        return Err(Error::WrongAuxShape);
    }
    let periodic = air.periodic_columns();
    let mut out = vec![Ext::ZERO; air.num_aux_constraints()];
    let main_row = |r: usize| -> Vec<Ext> { main.iter().map(|c| Ext::from_base(c[r])).collect() };
    let aux_row = |r: usize| -> Vec<Ext> { aux.iter().map(|c| c[r]).collect() };
    for row in 0..n - 1 {
        let p: Vec<Ext> = periodic.iter().map(|c| Ext::from_base(c[row % c.len()])).collect();
        let (mc, mn, ac, an) = (main_row(row), main_row(row + 1), aux_row(row), aux_row(row + 1));
        let frame = AuxFrame {
            main_current: &mc,
            main_next: &mn,
            aux_current: &ac,
            aux_next: &an,
            periodic: &p,
            challenges,
        };
        air.eval_aux_transition(&frame, &mut out);
        if let Some(index) = out.iter().position(|v| !v.is_zero()) {
            return Err(Error::AuxTransitionViolated { row, index });
        }
    }
    for b in air.aux_boundaries(challenges) {
        if b.column >= aux.len() || b.row >= n || aux[b.column][b.row] != b.value {
            return Err(Error::AuxBoundaryViolated(b));
        }
    }
    Ok(())
}

/// Check `trace` -- and the auxiliary columns `air` builds from it under
/// `challenges` -- against every constraint directly, row by row, with no
/// proving involved. For testing circuits: a failure names the exact row
/// and constraint.
pub fn check<A: Air>(air: &A, trace: &[Vec<BabyBear>], challenges: &[Ext]) -> Result<(), Error> {
    let full = full_trace(air, trace)?;
    check_trace(air, &full)?;
    let aux = air.aux_trace(&full, challenges);
    check_aux(air, &full, &aux, challenges)
}

/// `1, alpha, alpha^2, ...` -- one weight per constraint: main
/// transitions, auxiliary transitions, main boundaries, auxiliary
/// boundaries, in that order.
fn powers(alpha: Ext, count: usize) -> Vec<Ext> {
    let mut out = Vec::with_capacity(count);
    let mut w = Ext::ONE;
    for _ in 0..count {
        out.push(w);
        w = w * alpha;
    }
    out
}

/// Combine the constraint values at one point into the composition value:
/// `sum_k weights[k] * quotient_k`, weights in the order `powers`
/// describes. Transition values (main, then auxiliary) are divided by
/// `transition_divisor_inv = 1 / Z_T(x)`; boundary terms (main, then
/// auxiliary) are `(column value - boundary value) / (x - g^row)`,
/// already divided. `scale(weight, value)` multiplies an extension weight
/// by a main-trace-field value -- cheap (`mul_base`) when proving.
#[allow(clippy::too_many_arguments)]
fn composition_value<F: Field>(
    weights: &[Ext],
    main_transition: &[F],
    aux_transition: &[Ext],
    transition_divisor_inv: F,
    main_boundary: &[F],
    aux_boundary: &[Ext],
    scale: impl Fn(Ext, F) -> Ext,
) -> Ext {
    let mut k = 0;
    let mut transition_sum = Ext::ZERO;
    for &t in main_transition {
        transition_sum = transition_sum + scale(weights[k], t);
        k += 1;
    }
    for &t in aux_transition {
        transition_sum = transition_sum + weights[k] * t;
        k += 1;
    }
    let mut acc = scale(transition_sum, transition_divisor_inv);
    for &b in main_boundary {
        acc = acc + scale(weights[k], b);
        k += 1;
    }
    for &b in aux_boundary {
        acc = acc + weights[k] * b;
        k += 1;
    }
    acc
}

/// The stated out-of-domain values.
struct Ood<'a> {
    main_z: &'a [Ext],
    main_zg: &'a [Ext],
    aux_z: &'a [Ext],
    aux_zg: &'a [Ext],
    composition_z: Ext,
}

/// The DEEP combination at one point `x`, from the main and auxiliary
/// rows, composition value, and mask value there. Term order -- main
/// columns, auxiliary columns, composition, mask -- matches the prover's.
#[allow(clippy::too_many_arguments)]
fn deep_value(x: Ext, main: &[Ext], aux: &[Ext], composition: Ext, mask: Ext, ood: &Ood, z: Ext, zg: Ext, beta: Ext) -> Ext {
    let inv_z = (x - z).inverse();
    let inv_zg = (x - zg).inverse();
    let mut acc = Ext::ZERO;
    let mut weight = Ext::ONE;
    let columns = main.iter().zip(ood.main_z.iter().zip(ood.main_zg)).chain(aux.iter().zip(ood.aux_z.iter().zip(ood.aux_zg)));
    for (&t, (&at_z, &at_zg)) in columns {
        acc = acc + weight * (t - at_z) * inv_z;
        weight = weight * beta;
        acc = acc + weight * (t - at_zg) * inv_zg;
        weight = weight * beta;
    }
    acc = acc + weight * (composition - ood.composition_z) * inv_z;
    acc + weight * beta * mask
}

/// A trace column's blinded polynomial (coefficients, degree < 2n): the
/// column's values on the even points of the size-2n domain -- which are
/// exactly the trace rows -- and fresh random values on the odd ones.
fn blind_column(column: &[BabyBear], randomness: &mut Randomness) -> Vec<BabyBear> {
    let mut values: Vec<BabyBear> = column.iter().flat_map(|&v| [v, randomness.next()]).collect();
    intt(&mut values);
    values
}

/// `blind_column`, for an auxiliary (extension) column.
fn blind_ext_column(column: &[Ext], randomness: &mut Randomness) -> Vec<Ext> {
    let mut values: Vec<Ext> = column.iter().flat_map(|&v| [v, randomness.next_ext()]).collect();
    intt(&mut values);
    values
}

/// Prove `trace` (column-major: `trace[column][row]`) satisfies `air`.
/// Refuses (rather than producing a proof that won't verify) if it
/// doesn't. `seed` must be fresh random bytes for every proof -- it's
/// what hides the witness (see the module docs); reusing one across
/// proofs of different witnesses would undo that.
pub fn prove<A: Air + Sync>(air: &A, trace: &[Vec<BabyBear>], params: &Params, seed: [u8; 32]) -> Result<Proof, Error> {
    check_trace(air, &full_trace(air, trace)?)?;
    prove_inner(air, trace, params, seed, true)
}

/// `prove`, minus the checks -- so tests can play a cheating prover and
/// confirm the *verifier* catches a bad trace.
fn prove_unchecked<A: Air + Sync>(air: &A, trace: &[Vec<BabyBear>], params: &Params, seed: [u8; 32]) -> Result<Proof, Error> {
    prove_inner(air, trace, params, seed, false)
}

/// The LDE coset in `2^log_slices` slices: slice `r` is the sub-coset
/// `shift · w^r · <w^R>` (`w` the LDE's generator, `R = 2^log_slices`),
/// i.e. LDE points `r, r + R, r + 2R, ...`. Slices partition the LDE, and
/// a point and its negation (`i`, `i + N/2`) always share one, so a leaf
/// (a row at both) can be built from one slice. Proving works one slice
/// at a time, never holding a whole extended column.
struct Slices {
    log_lde: usize,
    log_slices: usize,
}

impl Slices {
    fn new(log_lde: usize, log_slices: usize) -> Self {
        assert!(log_slices < log_lde);
        Slices { log_lde, log_slices }
    }

    fn count(&self) -> usize {
        1 << self.log_slices
    }

    fn log_size(&self) -> usize {
        self.log_lde - self.log_slices
    }

    fn shift(&self, r: usize) -> BabyBear {
        COSET_SHIFT * domain_generator(self.log_lde).pow(r as u64)
    }

    /// The LDE index of slice `r`'s `k`-th point.
    fn index(&self, r: usize, k: usize) -> usize {
        r + (k << self.log_slices)
    }

    fn eval<F: Field>(&self, coeffs: &[F], r: usize) -> Vec<F> {
        coset_evaluate(coeffs, self.shift(r), self.log_size())
    }

    fn eval_all<F: Field + Send + Sync, C: AsRef<[F]> + Sync>(&self, polys: &[C], r: usize) -> Vec<Vec<F>> {
        crate::parallel::map_each(polys.len(), |c| self.eval(polys[c].as_ref(), r))
    }

    /// Commit rows of base-field columns: leaf `i` is the row at `i` then
    /// at `i + N/2`. `slice_columns(r)` gives every column's values on
    /// slice `r`. Keeps only hashes; openings supply the leaf
    /// (`MerkleTree::open_leaf`).
    fn commit(&self, slice_columns: impl Fn(usize) -> Vec<Vec<BabyBear>>) -> MerkleTree {
        let half = 1usize << (self.log_lde - 1);
        let slice_half = 1usize << (self.log_size() - 1);
        let mut hashes = vec![[0u8; 32]; half];
        for r in 0..self.count() {
            let columns = slice_columns(r);
            let leaf_hashes = crate::parallel::map(slice_half, |k| {
                let row: Vec<BabyBear> = columns.iter().map(|c| c[k]).chain(columns.iter().map(|c| c[k + slice_half])).collect();
                crate::merkle::leaf_hash_elements(&row)
            });
            for (k, h) in leaf_hashes.into_iter().enumerate() {
                hashes[self.index(r, k)] = h;
            }
        }
        MerkleTree::from_leaf_hashes(hashes)
    }
}

/// Extension columns as base-field columns, coefficient by coefficient --
/// each value's four coefficients adjacent in a row, as in a leaf.
fn expand(columns: &[Vec<Ext>]) -> Vec<Vec<BabyBear>> {
    columns
        .iter()
        .flat_map(|c| (0..4).map(move |k| c.iter().map(|v| v.0[k]).collect()))
        .collect()
}

fn prove_inner<A: Air + Sync>(
    air: &A,
    trace: &[Vec<BabyBear>],
    params: &Params,
    seed: [u8; 32],
    check: bool,
) -> Result<Proof, Error> {
    let layout = layout(air, params).ok_or(Error::TooLarge)?;
    let n = air.trace_len();
    if trace.len() != air.width() || trace.iter().any(|c| c.len() != n) {
        return Err(Error::WrongShape);
    }
    let preprocessed = match air.preprocessed() {
        Some(p) => Some(p.prover.as_ref().ok_or(Error::NoPreprocessedData)?),
        None => None,
    };
    let full = full_trace(air, trace)?;
    // Witness columns, then preprocessed ones: the width constraints see.
    let width = full.len();
    let mut transcript = start_transcript(air);
    // Set STARK_PROFILE to see how long each phase takes.
    let profiling = std::env::var_os("STARK_PROFILE").is_some();
    let mut phase_start = std::time::Instant::now();
    let mut phase = |label: &str| {
        if profiling {
            eprintln!("  {label:<28} {:>10.2?}", phase_start.elapsed());
        }
        phase_start = std::time::Instant::now();
    };

    // The LDE is never held whole: it's handled in `2^log_blowup` slices
    // (see `Slices`), each the size of the composition's domain.
    let slices = Slices::new(layout.log_lde, params.log_blowup);

    // 1. Each column, interleaved with random rows and interpolated over
    //    the size-2n domain (see the module docs), then extended and
    //    committed row by row.
    let coeffs: Vec<Vec<BabyBear>> = crate::parallel::map_each(trace.len(), |c| {
        blind_column(&trace[c], &mut Randomness::stream(seed, b"trace column", c))
    });
    phase("trace interpolation");
    let trace_tree = slices.commit(|r| slices.eval_all(&coeffs, r));
    let trace_cap = trace_tree.cap(fri::CAP_HEIGHT);
    transcript.absorb_digests(TRACE_ROOT_LABEL, &trace_cap);
    phase("trace extension + commitment");
    // Witness columns then preprocessed ones, as constraints see them.
    let all_coeffs: Vec<&[BabyBear]> = coeffs
        .iter()
        .map(|c| &c[..])
        .chain(preprocessed.iter().flat_map(|p| p.coeffs.iter().map(|c| &c[..])))
        .collect();

    // 1b. Auxiliary columns, built from the committed trace and fresh
    //     challenges, and committed the same way.
    let challenges: Vec<Ext> = (0..air.num_challenges())
        .map(|_| transcript.challenge_ext(AUX_CHALLENGE_LABEL))
        .collect();
    let aux = air.aux_trace(&full, &challenges);
    phase("aux trace");
    if check {
        check_aux(air, &full, &aux, &challenges)?;
    } else if aux.len() != air.num_aux_columns() {
        return Err(Error::WrongAuxShape);
    }
    drop(full);
    let aux_width = aux.len();
    let aux_coeffs: Vec<Vec<Ext>> = crate::parallel::map_each(aux.len(), |c| {
        blind_ext_column(&aux[c], &mut Randomness::stream(seed, b"aux column", c))
    });
    drop(aux);
    let aux_tree = slices.commit(|r| expand(&slices.eval_all(&aux_coeffs, r)));
    let aux_cap = aux_tree.cap(fri::CAP_HEIGHT);
    transcript.absorb_digests(AUX_ROOT_LABEL, &aux_cap);
    phase("aux extension + commitment");
    let alpha = transcript.challenge_ext(ALPHA_LABEL);

    // 2. The composition polynomial, evaluated only on its own domain --
    //    slice 0 of the LDE, exactly as many points as its degree bound --
    //    then interpolated. Everything that depends only on the point (not
    //    the trace) repeats with a short period there, so it's tabulated
    //    once rather than per point.
    let log_q = slices.log_size();
    let q_size = 1usize << log_q;
    let step = q_size / n; // index distance of one trace row
    let points = coset_domain(COSET_SHIFT, log_q);
    let lde = slices.eval_all(&all_coeffs, 0);
    let aux_lde = slices.eval_all(&aux_coeffs, 0);
    let g = domain_generator(layout.log_n);
    let last_row_point = g.pow(n as u64 - 1);
    // x^n depends only on i mod `step` (x^n = shift^n · w^(i·n), w^n of order `step`).
    let vanishing_inv: Vec<BabyBear> = crate::field::batch_inverse(
        &(0..step).map(|i| points[i].pow(n as u64) - BabyBear::ONE).collect::<Vec<_>>(),
    );
    // A periodic column of length `len` is a polynomial in y = x^(n/len),
    // and y over the coset is itself a coset of size q_size·len/n.
    let periodic_tables: Vec<Vec<BabyBear>> = periodic_polys(&air.periodic_columns(), n)
        .iter()
        .map(|(exponent, coeffs)| {
            let log_period = log_q - exponent.trailing_zeros() as usize;
            coset_evaluate(coeffs, COSET_SHIFT.pow(*exponent as u64), log_period)
        })
        .collect();
    // Boundaries share rows; each distinct row's 1/(x - g^row) is
    // computed once per point, all in one batch inversion.
    let boundaries = air.boundaries();
    let aux_boundaries = air.aux_boundaries(&challenges);
    let mut boundary_rows: Vec<usize> = boundaries.iter().map(|b| b.row).chain(aux_boundaries.iter().map(|b| b.row)).collect();
    boundary_rows.sort_unstable();
    boundary_rows.dedup();
    let row_points: Vec<BabyBear> = boundary_rows.iter().map(|&r| g.pow(r as u64)).collect();
    let slot = |row: usize| boundary_rows.binary_search(&row).unwrap();
    let boundary_slot: Vec<usize> = boundaries.iter().map(|b| slot(b.row)).collect();
    let aux_boundary_slot: Vec<usize> = aux_boundaries.iter().map(|b| slot(b.row)).collect();
    let weights = powers(
        alpha,
        air.num_transition_constraints() + air.num_aux_constraints() + boundaries.len() + aux_boundaries.len(),
    );
    let lift_all = |values: &[BabyBear]| -> Vec<Ext> { values.iter().map(|&v| Ext::from_base(v)).collect() };
    // Each thread evaluates a contiguous range of points with its own
    // scratch buffers.
    let composition_values: Vec<Ext> = crate::parallel::map_ranges(q_size, |range| {
        let mut out = vec![BabyBear::ZERO; air.num_transition_constraints()];
        let mut aux_out = vec![Ext::ZERO; air.num_aux_constraints()];
        let mut current = vec![BabyBear::ZERO; width];
        let mut next = vec![BabyBear::ZERO; width];
        let mut p = vec![BabyBear::ZERO; periodic_tables.len()];
        let mut boundary_terms = vec![BabyBear::ZERO; boundaries.len()];
        let mut aux_boundary_terms = vec![Ext::ZERO; aux_boundaries.len()];
        range
            .map(|i| {
                let x = points[i];
                let j = (i + step) % q_size;
                for c in 0..width {
                    current[c] = lde[c][i];
                    next[c] = lde[c][j];
                }
                for (slot, table) in p.iter_mut().zip(&periodic_tables) {
                    *slot = table[i % table.len()];
                }
                air.eval_transition(&current, &next, &p, &mut out);
                // Z_T(x) = (x^n - 1) / (x - g^(n-1)): zero on every row but the last.
                let divisor_inv = (x - last_row_point) * vanishing_inv[i % step];
                let row_inv = crate::field::batch_inverse(&row_points.iter().map(|&r| x - r).collect::<Vec<_>>());
                for (k, b) in boundaries.iter().enumerate() {
                    boundary_terms[k] = (current[b.column] - b.value) * row_inv[boundary_slot[k]];
                }
                if !aux_out.is_empty() || !aux_boundaries.is_empty() {
                    let aux_current: Vec<Ext> = aux_lde.iter().map(|c| c[i]).collect();
                    if !aux_out.is_empty() {
                        let aux_next: Vec<Ext> = aux_lde.iter().map(|c| c[j]).collect();
                        let (mc, mn, pe) = (lift_all(&current), lift_all(&next), lift_all(&p));
                        let frame = AuxFrame {
                            main_current: &mc,
                            main_next: &mn,
                            aux_current: &aux_current,
                            aux_next: &aux_next,
                            periodic: &pe,
                            challenges: &challenges,
                        };
                        air.eval_aux_transition(&frame, &mut aux_out);
                    }
                    for (k, b) in aux_boundaries.iter().enumerate() {
                        aux_boundary_terms[k] = (aux_current[b.column] - b.value).mul_base(row_inv[aux_boundary_slot[k]]);
                    }
                }
                composition_value(
                    &weights,
                    &out,
                    &aux_out,
                    divisor_inv,
                    &boundary_terms,
                    &aux_boundary_terms,
                    |w, v| w.mul_base(v),
                )
            })
            .collect()
    });
    drop((lde, aux_lde));
    let composition_coeffs = coset_interpolate(&composition_values, COSET_SHIFT);
    drop(composition_values);
    phase("composition evaluation");
    // The random FRI mask (see the module docs), committed in the same
    // tree as the composition values -- it's independent of everything,
    // so it can be fixed this early, and sharing the tree shares the
    // openings.
    let fri_degree_bound = (1usize << layout.log_lde) >> params.log_blowup;
    let mut mask_randomness = Randomness::stream(seed, b"mask", 0);
    let mask_coeffs: Vec<Ext> = (0..fri_degree_bound).map(|_| mask_randomness.next_ext()).collect();
    let composition_polys = [&composition_coeffs[..], &mask_coeffs[..]];
    let composition_tree = slices.commit(|r| expand(&slices.eval_all(&composition_polys, r)));
    let composition_cap = composition_tree.cap(fri::CAP_HEIGHT);
    transcript.absorb_digests(COMPOSITION_ROOT_LABEL, &composition_cap);
    phase("mask + composition commitment");

    // 3. Out-of-domain evaluations.
    let z = transcript.challenge_ext(Z_LABEL);
    let zg = z.mul_base(g);
    let lift = |c: &[BabyBear]| -> Vec<Ext> { c.iter().map(|&v| Ext::from_base(v)).collect() };
    let trace_at_z: Vec<Ext> = all_coeffs.iter().map(|c| evaluate_at(&lift(c), z)).collect();
    let trace_at_zg: Vec<Ext> = all_coeffs.iter().map(|c| evaluate_at(&lift(c), zg)).collect();
    let aux_at_z: Vec<Ext> = aux_coeffs.iter().map(|c| evaluate_at(c, z)).collect();
    let aux_at_zg: Vec<Ext> = aux_coeffs.iter().map(|c| evaluate_at(c, zg)).collect();
    let composition_at_z = evaluate_at(&composition_coeffs, z);
    let ood = Ood {
        main_z: &trace_at_z,
        main_zg: &trace_at_zg,
        aux_z: &aux_at_z,
        aux_zg: &aux_at_zg,
        composition_z: composition_at_z,
    };
    absorb_ood(&mut transcript, &ood);
    phase("out-of-domain values");

    // 4. DEEP combination (mask included), proven low-degree by FRI.
    //    `deep_value`'s sum, rearranged: every term `w·(t - a)/(x - c)` is
    //    `w·t/(x - c)` minus a constant, and the weighted sums of the
    //    columns are themselves polynomials -- so combine coefficients
    //    first, then evaluate just two polynomials per point. Same
    //    weights, same order as `deep_value`, which the verifier uses.
    let beta = transcript.challenge_ext(BETA_LABEL);
    let mut beta_powers = powers(beta, 2 * (width + aux_width) + 2).into_iter();
    let mut w_z = Vec::with_capacity(width + aux_width + 1);
    let mut w_zg = Vec::with_capacity(width + aux_width);
    for _ in 0..width + aux_width {
        w_z.push(beta_powers.next().unwrap());
        w_zg.push(beta_powers.next().unwrap());
    }
    let w_composition = beta_powers.next().unwrap();
    let w_mask = beta_powers.next().unwrap();
    let dot = |weights: &[Ext], values: &[Ext]| weights.iter().zip(values).fold(Ext::ZERO, |a, (&w, &v)| a + w * v);
    let at_z_all: Vec<Ext> = trace_at_z.iter().chain(&aux_at_z).copied().collect();
    let at_zg_all: Vec<Ext> = trace_at_zg.iter().chain(&aux_at_zg).copied().collect();
    let constant_z = dot(&w_z, &at_z_all) + w_composition * composition_at_z;
    let constant_zg = dot(&w_zg, &at_zg_all);
    let combine = |weights: &[Ext], composition_weight: Option<Ext>| -> Vec<Ext> {
        crate::parallel::map(q_size, |m| {
            let mut acc = match composition_weight {
                Some(w) if m < composition_coeffs.len() => w * composition_coeffs[m],
                _ => Ext::ZERO,
            };
            for (j, c) in all_coeffs.iter().enumerate() {
                if let Some(&v) = c.get(m) {
                    acc = acc + weights[j].mul_base(v);
                }
            }
            for (j, c) in aux_coeffs.iter().enumerate() {
                if let Some(&v) = c.get(m) {
                    acc = acc + weights[width + j] * v;
                }
            }
            acc
        })
    };
    let sum_z = combine(&w_z, Some(w_composition));
    let sum_zg = combine(&w_zg, None);
    let mut deep = vec![Ext::ZERO; 1 << layout.log_lde];
    for r in 0..slices.count() {
        let [pz, pzg, mask] = [&sum_z, &sum_zg, &mask_coeffs].map(|c| slices.eval(c, r));
        let xs = coset_domain(slices.shift(r), log_q);
        let inv_z = batch_inverse(&xs.iter().map(|&x| Ext::from_base(x) - z).collect::<Vec<_>>());
        let inv_zg = batch_inverse(&xs.iter().map(|&x| Ext::from_base(x) - zg).collect::<Vec<_>>());
        for k in 0..q_size {
            deep[slices.index(r, k)] = (pz[k] - constant_z) * inv_z[k] + (pzg[k] - constant_zg) * inv_zg[k] + w_mask * mask[k];
        }
    }
    drop((sum_z, sum_zg));
    phase("DEEP combination");
    let (fri_proof, indices) = fri::Proof::prove(deep, COSET_SHIFT, params.fri(), &mut transcript);
    phase("FRI");

    // 5. Open the commitments where FRI was queried: one paired leaf each,
    //    its values recomputed from the polynomials at the two points.
    let lde_generator = domain_generator(layout.log_lde);
    let queries = indices
        .iter()
        .map(|&low| {
            let x = COSET_SHIFT * lde_generator.pow(low as u64);
            let base_leaf = |polys: &[&[BabyBear]]| -> Vec<u8> {
                [x, -x]
                    .iter()
                    .flat_map(|&p| polys.iter().map(move |c| evaluate_at(c, p)))
                    .flat_map(|v| v.to_bytes())
                    .collect()
            };
            let ext_leaf = |polys: &[&[Ext]]| -> Vec<u8> {
                [x, -x]
                    .iter()
                    .flat_map(|&p| polys.iter().map(move |c| evaluate_at(c, Ext::from_base(p))))
                    .flat_map(|v| v.to_bytes())
                    .collect()
            };
            let witness: Vec<&[BabyBear]> = coeffs.iter().map(|c| &c[..]).collect();
            let aux: Vec<&[Ext]> = aux_coeffs.iter().map(|c| &c[..]).collect();
            QueryOpenings {
                trace: trace_tree.open_leaf(low, base_leaf(&witness), fri::CAP_HEIGHT),
                preprocessed: preprocessed.map(|p| {
                    let fixed: Vec<&[BabyBear]> = p.coeffs.iter().map(|c| &c[..]).collect();
                    p.tree.open_leaf(low, base_leaf(&fixed), fri::CAP_HEIGHT)
                }),
                aux: aux_tree.open_leaf(low, ext_leaf(&aux), fri::CAP_HEIGHT),
                composition: composition_tree.open_leaf(low, ext_leaf(&composition_polys), fri::CAP_HEIGHT),
            }
        })
        .collect();

    Ok(Proof {
        trace_cap,
        aux_cap,
        composition_cap,
        trace_at_z,
        trace_at_zg,
        aux_at_z,
        aux_at_zg,
        composition_at_z,
        fri: fri_proof,
        queries,
    })
}

fn absorb_ood(transcript: &mut Transcript, ood: &Ood) {
    let values: Vec<Ext> = ood
        .main_z
        .iter()
        .chain(ood.main_zg)
        .chain(ood.aux_z)
        .chain(ood.aux_zg)
        .copied()
        .chain([ood.composition_z])
        .collect();
    transcript.absorb_ext(OOD_LABEL, &values);
}

/// Whether `proof` shows some trace satisfies `air`.
pub fn verify<A: Air>(air: &A, proof: &Proof, params: &Params) -> bool {
    verify_inner(air, proof, params).is_some()
}

fn verify_inner<A: Air>(air: &A, proof: &Proof, params: &Params) -> Option<()> {
    let layout = layout(air, params)?;
    let n = air.trace_len();
    let witness_width = air.width();
    let width = full_width(air);
    let aux_width = air.num_aux_columns();
    if proof.trace_at_z.len() != width
        || proof.trace_at_zg.len() != width
        || proof.aux_at_z.len() != aux_width
        || proof.aux_at_zg.len() != aux_width
        || proof.queries.len() != params.num_queries
    {
        return None;
    }
    let mut transcript = start_transcript(air);

    let leaves = (1usize << layout.log_lde) / 2;
    if [&proof.trace_cap, &proof.aux_cap, &proof.composition_cap]
        .iter()
        .any(|cap| cap.len() != fri::cap_len(leaves))
    {
        return None;
    }
    transcript.absorb_digests(TRACE_ROOT_LABEL, &proof.trace_cap);
    let challenges: Vec<Ext> = (0..air.num_challenges())
        .map(|_| transcript.challenge_ext(AUX_CHALLENGE_LABEL))
        .collect();
    transcript.absorb_digests(AUX_ROOT_LABEL, &proof.aux_cap);
    let alpha = transcript.challenge_ext(ALPHA_LABEL);
    transcript.absorb_digests(COMPOSITION_ROOT_LABEL, &proof.composition_cap);
    let z = transcript.challenge_ext(Z_LABEL);
    let g = domain_generator(layout.log_n);
    let zg = z.mul_base(g);

    // The constraints, evaluated on the stated values at z, must reproduce
    // the stated composition value there.
    let z_n = z.pow(n as u128);
    if z_n == Ext::ONE {
        return None; // z landed in the trace domain: astronomically unlikely
    }
    let periodic = periodic_polys(&air.periodic_columns(), n);
    let p = periodic_at(&periodic, z);
    let mut out = vec![Ext::ZERO; air.num_transition_constraints()];
    air.eval_transition(&proof.trace_at_z, &proof.trace_at_zg, &p, &mut out);
    let mut aux_out = vec![Ext::ZERO; air.num_aux_constraints()];
    let frame = AuxFrame {
        main_current: &proof.trace_at_z,
        main_next: &proof.trace_at_zg,
        aux_current: &proof.aux_at_z,
        aux_next: &proof.aux_at_zg,
        periodic: &p,
        challenges: &challenges,
    };
    air.eval_aux_transition(&frame, &mut aux_out);
    let divisor_inv = (z - Ext::from_base(g.pow(n as u64 - 1))) * (z_n - Ext::ONE).inverse();
    let row_inv = |row: usize| (z - Ext::from_base(g.pow(row as u64))).inverse();
    let boundary_terms: Vec<Ext> = air
        .boundaries()
        .iter()
        .map(|b| {
            if b.column >= width || b.row >= n {
                return None;
            }
            Some((proof.trace_at_z[b.column] - Ext::from_base(b.value)) * row_inv(b.row))
        })
        .collect::<Option<_>>()?;
    let aux_boundary_terms: Vec<Ext> = air
        .aux_boundaries(&challenges)
        .iter()
        .map(|b| {
            if b.column >= aux_width || b.row >= n {
                return None;
            }
            Some((proof.aux_at_z[b.column] - b.value) * row_inv(b.row))
        })
        .collect::<Option<_>>()?;
    let weights = powers(alpha, out.len() + aux_out.len() + boundary_terms.len() + aux_boundary_terms.len());
    let expected = composition_value(
        &weights,
        &out,
        &aux_out,
        divisor_inv,
        &boundary_terms,
        &aux_boundary_terms,
        |w, v| w * v,
    );
    if expected != proof.composition_at_z {
        return None;
    }

    let ood = Ood {
        main_z: &proof.trace_at_z,
        main_zg: &proof.trace_at_zg,
        aux_z: &proof.aux_at_z,
        aux_zg: &proof.aux_at_zg,
        composition_z: proof.composition_at_z,
    };
    absorb_ood(&mut transcript, &ood);
    let beta = transcript.challenge_ext(BETA_LABEL);

    // FRI's first layer is the DEEP combination, which the verifier
    // computes itself, at each query's point and its negation, from the
    // openings -- after checking them against the commitments.
    let lde_generator = domain_generator(layout.log_lde);
    let first_layer = |q: usize, low: usize| -> Option<(Ext, Ext)> {
        let opening = proof.queries.get(q)?;
        let checked = [
            (&opening.trace, &proof.trace_cap),
            (&opening.aux, &proof.aux_cap),
            (&opening.composition, &proof.composition_cap),
        ];
        if checked.iter().any(|(o, cap)| o.index != low || !o.verify_cap(cap, leaves)) {
            return None;
        }
        let witness_rows = decode_row(&opening.trace.leaf, 2 * witness_width)?;
        let fixed_width = width - witness_width;
        let fixed_rows = match (air.preprocessed(), &opening.preprocessed) {
            (None, None) => Vec::new(),
            (Some(p), Some(o)) if o.index == low && o.verify_cap(&p.cap, leaves) => decode_row(&o.leaf, 2 * fixed_width)?,
            _ => return None,
        };
        // Each side's full row: witness values, then preprocessed ones.
        let rows: Vec<BabyBear> = (0..2)
            .flat_map(|side| {
                witness_rows[side * witness_width..(side + 1) * witness_width]
                    .iter()
                    .chain(&fixed_rows[side * fixed_width..(side + 1) * fixed_width])
                    .copied()
                    .collect::<Vec<_>>()
            })
            .collect();
        let aux_rows = decode_ext_row(&opening.aux.leaf, 2 * aux_width)?;
        let values = decode_ext_row(&opening.composition.leaf, 4)?;
        let x = Ext::from_base(COSET_SHIFT * lde_generator.pow(low as u64));
        let at = |side: usize, x: Ext| {
            let row: Vec<Ext> = rows[side * width..(side + 1) * width].iter().map(|&v| Ext::from_base(v)).collect();
            let aux = &aux_rows[side * aux_width..(side + 1) * aux_width];
            deep_value(x, &row, aux, values[2 * side], values[2 * side + 1], &ood, z, zg, beta)
        };
        Some((at(0, x), at(1, -x)))
    };
    if !proof.fri.verify(layout.log_lde, COSET_SHIFT, params.fri(), &mut transcript, first_layer) {
        return None;
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const PARAMS: Params = Params {
        log_blowup: 2,
        num_queries: 20,
        grinding_bits: 4,
    };

    const SEED: [u8; 32] = [42; 32];

    /// Fibonacci: columns (a, b), each row (a, b) -> (b, a + b), starting
    /// from (1, 1). Claims the last row's `b` is `result`.
    struct Fibonacci {
        log_n: usize,
        result: BabyBear,
    }

    fn fibonacci_trace(n: usize) -> Vec<Vec<BabyBear>> {
        let (mut a, mut b) = (BabyBear::ONE, BabyBear::ONE);
        let mut columns = vec![Vec::with_capacity(n), Vec::with_capacity(n)];
        for _ in 0..n {
            columns[0].push(a);
            columns[1].push(b);
            (a, b) = (b, a + b);
        }
        columns
    }

    impl Air for Fibonacci {
        fn width(&self) -> usize {
            2
        }
        fn trace_len(&self) -> usize {
            1 << self.log_n
        }
        fn constraint_degree(&self) -> usize {
            1
        }
        fn num_transition_constraints(&self) -> usize {
            2
        }
        fn eval_transition<F: Field>(&self, current: &[F], next: &[F], _periodic: &[F], out: &mut [F]) {
            out[0] = next[0] - current[1];
            out[1] = next[1] - (current[0] + current[1]);
        }
        fn boundaries(&self) -> Vec<Boundary> {
            vec![
                Boundary { row: 0, column: 0, value: BabyBear::ONE },
                Boundary { row: 0, column: 1, value: BabyBear::ONE },
                Boundary { row: self.trace_len() - 1, column: 1, value: self.result },
            ]
        }
    }

    fn honest_fibonacci(log_n: usize) -> (Fibonacci, Vec<Vec<BabyBear>>) {
        let trace = fibonacci_trace(1 << log_n);
        let result = *trace[1].last().unwrap();
        (Fibonacci { log_n, result }, trace)
    }

    #[test]
    fn an_honest_fibonacci_proof_verifies() {
        for log_n in [1, 3, 6] {
            let (air, trace) = honest_fibonacci(log_n);
            let proof = prove(&air, &trace, &PARAMS, SEED).unwrap();
            assert!(verify(&air, &proof, &PARAMS), "log_n = {log_n}");
        }
    }

    #[test]
    fn the_prover_refuses_a_trace_that_breaks_the_rules() {
        let (air, mut trace) = honest_fibonacci(4);
        trace[1][5] = trace[1][5] + BabyBear::ONE;
        assert!(matches!(prove(&air, &trace, &PARAMS, SEED), Err(Error::TransitionViolated { .. })));
    }

    /// A proof of the true result doesn't verify as a proof of a false one.
    #[test]
    fn a_proof_does_not_verify_against_a_different_claim() {
        let (air, trace) = honest_fibonacci(4);
        let proof = prove(&air, &trace, &PARAMS, SEED).unwrap();
        let lie = Fibonacci {
            log_n: 4,
            result: air.result + BabyBear::ONE,
        };
        assert!(!verify(&lie, &proof, &PARAMS));
    }

    /// The real soundness test: a cheating prover that skips the check and
    /// commits to a trace breaking one transition must be caught by the
    /// verifier alone.
    #[test]
    fn a_cheating_prover_with_a_bad_trace_is_caught() {
        let (_, mut trace) = honest_fibonacci(5);
        // Break row 10 -> 11, then recompute from there so every *other*
        // transition (and the claimed result) is consistent.
        trace[1][11] = trace[1][11] + BabyBear::new(7);
        for row in 12..32 {
            trace[0][row] = trace[1][row - 1];
            trace[1][row] = trace[0][row - 1] + trace[1][row - 1];
        }
        let air = Fibonacci {
            log_n: 5,
            result: *trace[1].last().unwrap(),
        };
        let proof = prove_unchecked(&air, &trace, &PARAMS, SEED).unwrap();
        assert!(!verify(&air, &proof, &PARAMS));
    }

    /// A cheater can also violate a boundary instead.
    #[test]
    fn a_cheating_prover_with_a_bad_boundary_is_caught() {
        let (air, trace) = honest_fibonacci(4);
        let lie = Fibonacci {
            log_n: 4,
            result: air.result + BabyBear::ONE,
        };
        let proof = prove_unchecked(&lie, &trace, &PARAMS, SEED).unwrap();
        assert!(!verify(&lie, &proof, &PARAMS));
    }

    #[test]
    fn tampering_with_the_proof_is_rejected() {
        let (air, trace) = honest_fibonacci(4);
        let proof = prove(&air, &trace, &PARAMS, SEED).unwrap();
        assert!(verify(&air, &proof, &PARAMS));

        let mut p = proof.clone();
        p.trace_at_z[0] = p.trace_at_z[0] + Ext::ONE;
        assert!(!verify(&air, &p, &PARAMS));

        let mut p = proof.clone();
        p.composition_at_z = p.composition_at_z + Ext::ONE;
        assert!(!verify(&air, &p, &PARAMS));

        let mut p = proof.clone();
        p.trace_cap[0][0] ^= 1;
        assert!(!verify(&air, &p, &PARAMS));

        let mut p = proof.clone();
        p.queries[3].trace.leaf[0] ^= 1;
        assert!(!verify(&air, &p, &PARAMS));

        let mut p = proof;
        p.queries.pop();
        assert!(!verify(&air, &p, &PARAMS));
    }

    /// Degree-3 constraints with a periodic column: each row cubes the
    /// previous value and adds that row's constant. Exercises the
    /// composition degree bound growing past the trace length, and
    /// periodic columns' interpolation, end to end.
    struct CubeChain {
        log_n: usize,
        constants: Vec<BabyBear>,
        result: BabyBear,
    }

    impl Air for CubeChain {
        fn width(&self) -> usize {
            1
        }
        fn trace_len(&self) -> usize {
            1 << self.log_n
        }
        fn constraint_degree(&self) -> usize {
            3
        }
        fn periodic_columns(&self) -> Vec<Vec<BabyBear>> {
            vec![self.constants.clone()]
        }
        fn num_transition_constraints(&self) -> usize {
            1
        }
        fn eval_transition<F: Field>(&self, current: &[F], next: &[F], periodic: &[F], out: &mut [F]) {
            out[0] = next[0] - (current[0] * current[0] * current[0] + periodic[0]);
        }
        fn boundaries(&self) -> Vec<Boundary> {
            vec![
                Boundary { row: 0, column: 0, value: BabyBear::new(2) },
                Boundary { row: self.trace_len() - 1, column: 0, value: self.result },
            ]
        }
    }

    fn cube_chain(log_n: usize) -> (CubeChain, Vec<Vec<BabyBear>>) {
        let constants: Vec<BabyBear> = (0..8u32).map(|i| BabyBear::new(i * 1000 + 17)).collect();
        let n = 1 << log_n;
        let mut column = vec![BabyBear::new(2)];
        for row in 0..n - 1 {
            let x = column[row];
            column.push(x * x * x + constants[row % 8]);
        }
        let result = column[n - 1];
        (CubeChain { log_n, constants, result }, vec![column])
    }

    #[test]
    fn higher_degree_constraints_with_periodic_columns_verify() {
        let (air, trace) = cube_chain(5);
        let proof = prove(&air, &trace, &PARAMS, SEED).unwrap();
        assert!(verify(&air, &proof, &PARAMS));
    }

    #[test]
    fn changing_a_periodic_constant_breaks_verification() {
        let (air, trace) = cube_chain(5);
        let proof = prove(&air, &trace, &PARAMS, SEED).unwrap();
        let mut other = CubeChain {
            log_n: air.log_n,
            constants: air.constants.clone(),
            result: air.result,
        };
        other.constants[3] = other.constants[3] + BabyBear::ONE;
        assert!(!verify(&other, &proof, &PARAMS));
    }

    /// The blinded polynomial still *is* the trace on every trace row --
    /// which is why the constraints don't change at all.
    #[test]
    fn a_blinded_column_still_equals_the_trace_on_its_rows() {
        let column: Vec<BabyBear> = (0..16u32).map(|i| BabyBear::new(i * 7 + 1)).collect();
        let coeffs = blind_column(&column, &mut Randomness::new(SEED));
        assert_eq!(coeffs.len(), 32);
        let g = domain_generator(4);
        for (row, &value) in column.iter().enumerate() {
            assert_eq!(evaluate_at(&coeffs, g.pow(row as u64)), value, "row {row}");
        }
    }

    /// ...but off the trace rows it's genuinely randomized: the same
    /// column under two seeds gives different polynomials, and both carry
    /// degree past the n an unblinded interpolation would have.
    #[test]
    fn a_blinded_column_is_randomized_off_the_trace_rows() {
        let column: Vec<BabyBear> = (0..16u32).map(|i| BabyBear::new(i * 7 + 1)).collect();
        let a = blind_column(&column, &mut Randomness::new([1; 32]));
        let b = blind_column(&column, &mut Randomness::new([2; 32]));
        assert_ne!(a, b);
        assert!(a[16..].iter().any(|&c| c != BabyBear::ZERO));
        let off_trace = COSET_SHIFT; // not a trace row
        assert_ne!(evaluate_at(&a, off_trace), evaluate_at(&b, off_trace));
    }

    /// Different seeds give different -- and equally valid -- proofs of
    /// the same statement; the same seed gives the same proof.
    #[test]
    fn proofs_are_randomized_by_the_seed() {
        let (air, trace) = honest_fibonacci(4);
        let a = prove(&air, &trace, &PARAMS, [1; 32]).unwrap();
        let b = prove(&air, &trace, &PARAMS, [2; 32]).unwrap();
        assert!(verify(&air, &a, &PARAMS));
        assert!(verify(&air, &b, &PARAMS));
        assert_ne!(a.trace_cap, b.trace_cap);
        assert_ne!(a.trace_at_z, b.trace_at_z);
        assert_ne!(a.composition_cap, b.composition_cap);
        assert_eq!(a, prove(&air, &trace, &PARAMS, [1; 32]).unwrap());
    }

    /// Tampering with the mask -- its commitment or an opening of it --
    /// is caught like anything else.
    #[test]
    fn tampering_with_the_mask_is_rejected() {
        let (air, trace) = honest_fibonacci(4);
        let proof = prove(&air, &trace, &PARAMS, SEED).unwrap();

        let mut p = proof.clone();
        p.composition_cap[0][0] ^= 1;
        assert!(!verify(&air, &p, &PARAMS));

        // The mask shares the composition leaf: its second value is the
        // mask at the query's point.
        let mut p = proof;
        p.queries[0].composition.leaf[16] ^= 1;
        assert!(!verify(&air, &p, &PARAMS));
    }

    #[test]
    fn hiding_needs_enough_rows_and_enough_mask() {
        let fib = |log_n| Fibonacci {
            log_n,
            result: BabyBear::ZERO,
        };
        // Rows: 20 queries reveal under 4 * 20 + 2 = 82 trace points, so
        // 64 rows are too few. Mask: at 128 rows the FRI degree bound is
        // 256, under the 20 * (2 + 8 + 8 + 2) = 400 values revealed.
        assert!(!hides(&fib(6), &PARAMS));
        assert!(!hides(&fib(7), &PARAMS));
        // At 256 rows: bound 512 > 20 * (2 + 8 + 8 + 4) = 440 revealed.
        assert!(hides(&fib(8), &PARAMS));
        assert!(hides(&fib(12), &PARAMS));
    }

    /// A two-phase AIR: claims column `b` is a rearrangement of column `a`
    /// over the first `n - 1` rows (the last row is zero padding in both).
    /// An auxiliary running product `acc`, starting at 1, multiplies in
    /// `(gamma - a) / (gamma - b)` row by row -- written as
    /// `acc' · (gamma - b) = acc · (gamma - a)` -- and must end at 1, which
    /// (for a `gamma` drawn after `a` and `b` are committed) happens only
    /// if the two multisets are equal.
    struct Shuffle {
        log_n: usize,
    }

    impl Air for Shuffle {
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
            0
        }
        fn eval_transition<F: Field>(&self, _current: &[F], _next: &[F], _periodic: &[F], _out: &mut [F]) {}
        fn boundaries(&self) -> Vec<Boundary> {
            let last = self.trace_len() - 1;
            vec![
                Boundary { row: last, column: 0, value: BabyBear::ZERO },
                Boundary { row: last, column: 1, value: BabyBear::ZERO },
            ]
        }
        fn num_aux_columns(&self) -> usize {
            1
        }
        fn num_challenges(&self) -> usize {
            1
        }
        fn aux_trace(&self, main: &[Vec<BabyBear>], challenges: &[Ext]) -> Vec<Vec<Ext>> {
            let gamma = challenges[0];
            let mut acc = vec![Ext::ONE];
            for row in 0..self.trace_len() - 1 {
                let a = gamma - Ext::from_base(main[0][row]);
                let b = gamma - Ext::from_base(main[1][row]);
                acc.push(acc[row] * a * b.inverse());
            }
            vec![acc]
        }
        fn num_aux_constraints(&self) -> usize {
            1
        }
        fn eval_aux_transition<F: Field>(&self, f: &AuxFrame<F>, out: &mut [F]) {
            let gamma = f.challenges[0];
            out[0] = f.aux_next[0] * (gamma - f.main_current[1]) - f.aux_current[0] * (gamma - f.main_current[0]);
        }
        fn aux_boundaries(&self, _challenges: &[Ext]) -> Vec<AuxBoundary> {
            vec![
                AuxBoundary { row: 0, column: 0, value: Ext::ONE },
                AuxBoundary { row: self.trace_len() - 1, column: 0, value: Ext::ONE },
            ]
        }
    }

    /// `a` = 1..n-1 in order, `b` = the same values reversed (or, if
    /// `tamper`, with one of them changed), both zero on the last row.
    fn shuffle_trace(log_n: usize, tamper: bool) -> Vec<Vec<BabyBear>> {
        let n = 1 << log_n;
        let mut a: Vec<BabyBear> = (1..n as u32).map(|i| BabyBear::new(i * 13 + 5)).collect();
        let mut b: Vec<BabyBear> = a.iter().rev().copied().collect();
        if tamper {
            b[2] = b[2] + BabyBear::ONE;
        }
        a.push(BabyBear::ZERO);
        b.push(BabyBear::ZERO);
        vec![a, b]
    }

    #[test]
    fn a_two_phase_proof_of_a_true_shuffle_verifies() {
        let air = Shuffle { log_n: 5 };
        let proof = prove(&air, &shuffle_trace(5, false), &PARAMS, SEED).unwrap();
        assert!(verify(&air, &proof, &PARAMS));
    }

    #[test]
    fn the_prover_refuses_a_false_shuffle() {
        let air = Shuffle { log_n: 5 };
        assert!(matches!(
            prove(&air, &shuffle_trace(5, true), &PARAMS, SEED),
            Err(Error::AuxBoundaryViolated(_))
        ));
    }

    /// A cheating prover skipping the checks can't pass off a false
    /// shuffle: the running product doesn't end at 1, and the verifier
    /// sees that alone.
    #[test]
    fn a_cheating_prover_with_a_false_shuffle_is_caught() {
        let air = Shuffle { log_n: 5 };
        let proof = prove_unchecked(&air, &shuffle_trace(5, true), &PARAMS, SEED).unwrap();
        assert!(!verify(&air, &proof, &PARAMS));
    }

    #[test]
    fn tampering_with_the_auxiliary_commitment_is_rejected() {
        let air = Shuffle { log_n: 5 };
        let proof = prove(&air, &shuffle_trace(5, false), &PARAMS, SEED).unwrap();

        let mut p = proof.clone();
        p.aux_cap[0][0] ^= 1;
        assert!(!verify(&air, &p, &PARAMS));

        let mut p = proof.clone();
        p.aux_at_zg[0] = p.aux_at_zg[0] + Ext::ONE;
        assert!(!verify(&air, &p, &PARAMS));

        let mut p = proof;
        p.queries[1].aux.leaf[3] ^= 1;
        assert!(!verify(&air, &p, &PARAMS));
    }

    #[test]
    fn proofs_roundtrip_through_bytes_and_bad_bytes_are_refused() {
        let air = Shuffle { log_n: 5 };
        let proof = prove(&air, &shuffle_trace(5, false), &PARAMS, SEED).unwrap();
        let bytes = proof.to_bytes();
        let decoded = Proof::from_bytes(&bytes).unwrap();
        assert_eq!(decoded, proof);
        assert!(verify(&air, &decoded, &PARAMS));

        let mut trailing = bytes.clone();
        trailing.push(0);
        assert_eq!(Proof::from_bytes(&trailing), None);
        assert_eq!(Proof::from_bytes(&bytes[..bytes.len() - 1]), None);
        assert_eq!(Proof::from_bytes(&[]), None);
        // A list claiming billions of entries fails cleanly.
        let mut huge = bytes.clone();
        huge[..4].copy_from_slice(&u32::MAX.to_le_bytes());
        assert_eq!(Proof::from_bytes(&huge), None);
    }

    /// One witness column that must be 3× a preprocessed column, row by
    /// row (and start at 3).
    struct Tripled {
        fixed: Preprocessed,
    }

    impl Air for Tripled {
        fn width(&self) -> usize {
            1
        }
        fn preprocessed(&self) -> Option<&Preprocessed> {
            Some(&self.fixed)
        }
        fn trace_len(&self) -> usize {
            64
        }
        fn constraint_degree(&self) -> usize {
            1
        }
        fn num_transition_constraints(&self) -> usize {
            1
        }
        fn eval_transition<F: Field>(&self, current: &[F], _next: &[F], _periodic: &[F], out: &mut [F]) {
            out[0] = current[0] - current[1].mul_base(BabyBear::new(3));
        }
        fn boundaries(&self) -> Vec<Boundary> {
            vec![Boundary { row: 0, column: 0, value: BabyBear::new(3) }]
        }
    }

    fn tripled(start: u32) -> Tripled {
        let column = (0..64).map(|i| BabyBear::new(start + i * i)).collect();
        Tripled { fixed: Preprocessed::commit(vec![column], 64, 1, &PARAMS) }
    }

    #[test]
    fn preprocessed_columns_bind_the_proof_to_their_commitment() {
        let air = tripled(1);
        let witness: Vec<BabyBear> = air.fixed.columns().unwrap()[0].iter().map(|&v| v * BabyBear::new(3)).collect();
        let proof = prove(&air, std::slice::from_ref(&witness), &PARAMS, SEED).unwrap();
        assert!(proof.queries.iter().all(|q| q.preprocessed.is_some()));
        assert_eq!(Proof::from_bytes(&proof.to_bytes()), Some(proof.clone()));

        // A verifier needs only the cap.
        let verifier = Tripled { fixed: Preprocessed::from_cap(1, air.fixed.log_lde, air.fixed.cap.clone()) };
        assert!(verify(&verifier, &proof, &PARAMS));
        // ... and can't prove with it.
        assert!(matches!(prove(&verifier, std::slice::from_ref(&witness), &PARAMS, SEED), Err(Error::NoPreprocessedData)));

        // Different fixed columns: different statement.
        assert!(!verify(&tripled(1 + 1), &proof, &PARAMS));
        // A witness that doesn't match the fixed column is refused.
        let mut wrong = witness;
        wrong[5] = wrong[5] + BabyBear::ONE;
        assert!(matches!(prove(&air, &[wrong], &PARAMS, SEED), Err(Error::TransitionViolated { row: 5, .. })));
        // Leaving the preprocessed opening out fails.
        let mut stripped = proof.clone();
        stripped.queries[0].preprocessed = None;
        assert!(!verify(&verifier, &stripped, &PARAMS));
    }
}
