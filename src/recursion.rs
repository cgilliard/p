//! STARK verification as a circuit: `verify` re-runs `stark::verify`
//! step by step on a `circuit::Builder`, so the resulting circuit's proof
//! attests "this STARK proof verifies" -- the core of recursion (see
//! `docs/RECURSION.md`).
//!
//! It mirrors the native verifier exactly (same transcript, same checks,
//! same order), with each piece expressed in the circuit's operations:
//!
//! - **Transcript**: the octet-aligned duplex sponge (`transcript`), one
//!   Poseidon2 permutation per duplex, labels as constant octets.
//! - **Indices** (FRI queries, grinding): a full 31-bit decomposition of
//!   the sampled element, with a check that it's canonical (below `p`),
//!   so the bits are *the* bits. Merkle paths, FRI positions and the
//!   query point `x = shift · g^index` are all built from those bits.
//! - **Merkle openings**: leaf hashes (`poseidon2::hash_octets`), then one
//!   permutation per level whose rate halves are swapped by the index bit,
//!   then a lookup of the result in the committed cap.
//! - **Constraints at `z`**: the AIR's compiled program (`symbolic`).
//! - **DEEP**: per opened row, one Horner sum in `beta^2` over its values
//!   (`deep_value` rearranged: the out-of-domain terms are constants per
//!   proof, computed once).
//! - **FRI**: each round's opened coset in a table, the incoming value
//!   checked by lookup at the position the index bits give, folds as
//!   extension arithmetic.
//!
//! The circuit's *shape* depends only on the inner AIR and parameters,
//! never on the proof's values -- the proof is witness. The inner
//! statement (everything `stark` absorbs before the trace commitment) is
//! the circuit's public input.

#![allow(dead_code)]

use crate::bus::Bus;
use crate::circuit::{Builder, EVar, OVar, Octet, Table};
use crate::ext::Ext;
use crate::fri::{self, domain_generator};
use crate::merkle::{Hash, Opening};
use crate::poseidon2::{BabyBear, DOMAIN_MERKLE_LEAF, DOMAIN_MERKLE_NODE, digest_from_bytes};
use crate::stark::{self, Air, COSET_SHIFT, Params, Proof};
use crate::symbolic::{self, Node, Var};
use crate::transcript::{TRANSCRIPT_DOMAIN, label_element, octet_of, octets};

/// An AIR whose auxiliary boundaries a circuit can recompute: none, or
/// exactly one bus's running sum -- zero on the first row, the bus's
/// `public_sum` of these tuples on the last (what `Bus::boundaries`
/// gives).
///
/// Its `statement` must be `recursive_statement(statement_header(),
/// tuples)`: a fixed header (part of the AIR's shape, like its reward
/// rule), then the tuples -- so a circuit can absorb the statement and
/// compute the bus's public sum from the very same cells.
pub trait RecursiveAir: Air {
    fn bus(&self) -> Option<(Bus, PublicTuples)>;

    fn statement_header(&self) -> Vec<BabyBear> {
        Vec::new()
    }
}

/// A bus's public tuples as statement elements, octet-aligned: an octet
/// `[count]`, then per tuple an octet `[multiplicity, length]` and the
/// tuple zero-padded to whole octets.
pub fn bus_statement(tuples: &[(BabyBear, Vec<BabyBear>)]) -> Vec<BabyBear> {
    let mut out = octet_of(BabyBear::new(tuples.len() as u32)).to_vec();
    for (m, tuple) in tuples {
        let mut header = octet_of(*m);
        header[1] = BabyBear::new(tuple.len() as u32);
        out.extend(header);
        out.extend(octets(tuple).into_iter().flatten());
    }
    out
}

/// The statement a `RecursiveAir` must have: `header` zero-padded to
/// whole octets, then `bus_statement(tuples)`.
pub fn recursive_statement(header: &[BabyBear], tuples: &[(BabyBear, Vec<BabyBear>)]) -> Vec<BabyBear> {
    let mut out: Vec<BabyBear> = octets(header).into_iter().flatten().collect();
    out.extend(bus_statement(tuples));
    out
}

/// A verified proof's statement, as cells the caller can hash or
/// constrain: everything the verifier circuit took on trust.
pub struct Statement {
    /// The AIR's whole `statement()`, octet by octet (its header and the
    /// tuple count are constants; everything about the tuples is witness).
    pub octets: Vec<OVar>,
    /// Each bus tuple's header octet `[multiplicity, length]` (witness).
    pub tuple_headers: Vec<OVar>,
    /// Each bus tuple's value octets (witness).
    pub tuples: Vec<Vec<OVar>>,
    /// The preprocessed columns' cap (witness), if the AIR has any.
    pub preprocessed_cap: Option<Table>,
}

/// A bus's public side: `(multiplicity, tuple)` pairs (`Bus::public_sum`).
pub type PublicTuples = Vec<(BabyBear, Vec<BabyBear>)>;

fn bb(v: u64) -> BabyBear {
    BabyBear::new((v % crate::poseidon2::P as u64) as u32)
}

/// The transcript, in-circuit (`transcript::Transcript`, cell for cell).
struct Transcript {
    state: [OVar; 3],
    queued: Vec<OVar>,
    halves_used: usize,
}

impl Transcript {
    fn new(b: &mut Builder, label: &[u8]) -> Self {
        let zero = b.const_octet([BabyBear::ZERO; 8]);
        let capacity = b.const_octet(octet_of(BabyBear::new(TRANSCRIPT_DOMAIN)));
        let mut t = Transcript {
            state: [zero, zero, capacity],
            queued: Vec::new(),
            halves_used: 4,
        };
        t.label(b, label);
        t
    }

    fn duplex(&mut self, b: &mut Builder) {
        let lo = self.queued.first().copied().unwrap_or(self.state[0]);
        let hi = self.queued.get(1).copied().unwrap_or(self.state[1]);
        self.state = b.permute(lo, hi, self.state[2], None);
        self.queued.clear();
        self.halves_used = 0;
    }

    fn observe(&mut self, b: &mut Builder, o: OVar) {
        self.queued.push(o);
        if self.queued.len() == 2 {
            self.duplex(b);
        } else {
            self.halves_used = 4;
        }
    }

    fn sample(&mut self, b: &mut Builder) -> EVar {
        if !self.queued.is_empty() || self.halves_used == 4 {
            self.duplex(b);
        }
        let h = self.halves_used;
        self.halves_used += 1;
        let (lo, hi) = b.halves(self.state[h / 2]);
        if h.is_multiple_of(2) { lo } else { hi }
    }

    fn label(&mut self, b: &mut Builder, label: &[u8]) {
        let o = b.const_octet(octet_of(label_element(label)));
        self.observe(b, o);
    }

    fn absorb_octets(&mut self, b: &mut Builder, label: &[u8], values: &[OVar]) {
        self.label(b, label);
        for &o in values {
            self.observe(b, o);
        }
    }

    fn absorb_exts(&mut self, b: &mut Builder, label: &[u8], values: &[EVar]) {
        let zero = b.zero();
        let packed: Vec<OVar> = values
            .chunks(2)
            .map(|pair| b.pack(pair[0], pair.get(1).copied().unwrap_or(zero)))
            .collect();
        self.absorb_octets(b, label, &packed);
    }

    fn challenge_ext(&mut self, b: &mut Builder, label: &[u8]) -> EVar {
        self.label(b, label);
        self.sample(b)
    }
}

/// A sampled element's canonical binary decomposition: `rest[i]` is the
/// element shifted right by `i` (`rest[0]` unused: the element itself is
/// lane 0 of `source`), `bits[i]` its bit `i`.
struct Bits {
    source: EVar,
    rest: Vec<EVar>,
    bits: Vec<EVar>,
}

impl Bits {
    fn of(b: &mut Builder, source: EVar) -> Self {
        let mut rest = vec![source];
        let mut bits = Vec::with_capacity(31);
        for _ in 0..31 {
            let (half, bit) = b.bit_step(*rest.last().unwrap());
            rest.push(half);
            bits.push(bit);
        }
        b.assert_zero(rest[31]);
        // Canonical: below p = 15·2^27 + 1, i.e. if bits 27-30 are all set,
        // the low 27 bits are all zero.
        let mut top = b.mul(bits[27], bits[28]);
        top = b.mul(top, bits[29]);
        top = b.mul(top, bits[30]);
        let low = Bits {
            source,
            rest: rest.clone(),
            bits: bits.clone(),
        }
        .slice(b, 0, 27);
        let product = b.mul(top, low);
        b.assert_zero(product);
        Bits { source, rest, bits }
    }

    /// Bits `i..j` as an integer: `rest[i] - 2^(j-i) · rest[j]`.
    fn slice(&self, b: &mut Builder, i: usize, j: usize) -> EVar {
        if i == j {
            return b.zero();
        }
        let z = BabyBear::ZERO;
        let scale = -BabyBear::new(1 << (j - i));
        if i == 0 {
            // rest[0] is lane 0 of the source cell.
            b.arith(z, None, Some(self.rest[j]), z, scale, Some(self.source), z, [BabyBear::ONE, z, z, z])
        } else {
            b.arith(z, Some(self.rest[i]), Some(self.rest[j]), BabyBear::ONE, scale, None, z, [z; 4])
        }
    }
}

fn digest_octet(h: &Hash) -> Octet {
    digest_from_bytes(h)
}

fn leaf_elements(leaf: &[u8]) -> Vec<BabyBear> {
    leaf.chunks(4)
        .map(|c| {
            let mut padded = [0u8; 4];
            padded[..c.len()].copy_from_slice(c);
            BabyBear::from_bytes(padded)
        })
        .collect()
}

/// A Merkle cap as a table of witness octets.
fn cap_table(b: &mut Builder, cap: &[Hash]) -> Table {
    let values: Vec<Octet> = cap.iter().map(digest_octet).collect();
    b.witness_octet_table(&values)
}

pub fn table_octets(t: &Table) -> Vec<OVar> {
    (0..t.len()).map(|k| t.octet(k)).collect()
}

/// `poseidon2::hash_octets(domain, length, ...)` of `data`, in-circuit.
pub fn hash_octets(b: &mut Builder, domain: u32, length: usize, data: &[OVar]) -> OVar {
    let zero = b.const_octet([BabyBear::ZERO; 8]);
    let mut capacity_init = [BabyBear::ZERO; 8];
    capacity_init[0] = BabyBear::new(domain);
    capacity_init[1] = BabyBear::new(length as u32);
    let capacity = b.const_octet(capacity_init);
    let mut state = [zero, zero, capacity];
    if data.is_empty() {
        state = b.permute(zero, zero, capacity, None);
    }
    for pair in data.chunks(2) {
        let hi = pair.get(1).copied().unwrap_or(state[1]);
        state = b.permute(pair[0], hi, state[2], None);
    }
    state[0]
}

/// Check an opening of `leaf` against `cap`: the path's left/right
/// choices are `index_bits`, and the cap entry is `cap_index`.
fn merkle_check(b: &mut Builder, leaf: &[OVar], byte_len: usize, opening: &Opening, index_bits: &[EVar], cap: Table, cap_index: EVar) {
    let mut h = hash_octets(b, DOMAIN_MERKLE_LEAF, byte_len, leaf);
    for (k, sibling) in opening.siblings.iter().enumerate() {
        let level = k as u32 + 1;
        let s = b.witness_octet(digest_octet(sibling));
        let mut capacity = [BabyBear::ZERO; 8];
        capacity[0] = BabyBear::new(DOMAIN_MERKLE_NODE + level);
        capacity[1] = BabyBear::new(16);
        let capacity = b.const_octet(capacity);
        h = b.permute(h, s, capacity, Some(index_bits[k]))[0];
    }
    b.lookup_octet(h, cap, cap_index);
}

/// `shift · g^(Σ bits_i 2^i)`, one operation per bit:
/// `acc ← acc · (1 + (g^(2^i) - 1) · bit_i)`.
fn power_from_bits(b: &mut Builder, shift: BabyBear, g: BabyBear, bits: &[EVar]) -> EVar {
    let mut acc = b.const_base(shift);
    let mut gi = g;
    for &bit in bits {
        let z = BabyBear::ZERO;
        acc = b.arith(gi - BabyBear::ONE, Some(acc), Some(bit), BabyBear::ONE, z, None, z, [z; 4]);
        gi = gi * gi;
    }
    acc
}

/// `x^(2^k)`.
fn square_times(b: &mut Builder, x: EVar, k: usize) -> EVar {
    let mut y = x;
    for _ in 0..k {
        y = b.mul(y, y);
    }
    y
}

/// `x^e` by square-and-multiply.
fn power(b: &mut Builder, x: EVar, mut e: usize) -> EVar {
    let mut result = b.one();
    let mut base = x;
    while e > 0 {
        if e & 1 == 1 {
            result = b.mul(result, base);
        }
        e >>= 1;
        if e > 0 {
            base = b.mul(base, base);
        }
    }
    result
}

/// FRI's binary fold at one pair, given `1/x`:
/// `(f(x) + f(-x))/2 + beta · (f(x) - f(-x)) / (2x)`.
fn fold_pair(b: &mut Builder, f_x: EVar, f_neg_x: EVar, x_inv: EVar, beta: EVar) -> EVar {
    let inv2 = BabyBear::new(2).inverse();
    let sum = b.add(f_x, f_neg_x);
    let diff = b.sub(f_x, f_neg_x);
    let t = b.mul(diff, x_inv);
    let z = BabyBear::ZERO;
    b.arith(inv2, Some(beta), Some(t), z, z, Some(sum), inv2, [z; 4])
}

/// Witness extension values.
fn witness_exts(b: &mut Builder, values: &[Ext]) -> Vec<EVar> {
    values.iter().map(|&v| b.witness_ext(v)).collect()
}

/// Leaf elements as witness octets (each with its halves).
fn witness_leaf(b: &mut Builder, leaf: &[u8]) -> Vec<OVar> {
    octets(&leaf_elements(leaf)).into_iter().map(|o| b.witness_octet(o)).collect()
}

/// Element `i` of a leaf held as octets: (half cell, lane).
fn element(b: &mut Builder, leaf: &[OVar], i: usize) -> (EVar, usize) {
    let (lo, hi) = b.halves(leaf[i / 8]);
    (if i % 8 < 4 { lo } else { hi }, i % 4)
}

/// Extension value `k` of a leaf of extension values held as octets.
fn ext_element(b: &mut Builder, leaf: &[OVar], k: usize) -> EVar {
    let (lo, hi) = b.halves(leaf[k / 2]);
    if k.is_multiple_of(2) { lo } else { hi }
}

/// Add to `b` a circuit verifying `proof` for `air` under `params`. The
/// proof must verify natively (checked first: `None` otherwise) -- a
/// prover can't produce this circuit's witness for a bad proof, and this
/// way a bad proof is a clean error rather than a failed assertion.
///
/// The AIR's *shape* is built into the circuit; its *statement* --
/// public tuples and preprocessed cap -- enters as witness, returned for
/// the caller to bind (hash it into a public input, compare it with
/// something, ...). Unbound, it proves only "some statement of this shape
/// has a valid proof".
pub fn verify<A: RecursiveAir>(b: &mut Builder, air: &A, proof: &Proof, params: &Params) -> Option<Statement> {
    if !stark::verify(air, proof, params) {
        return None;
    }
    let tuples = air.bus().map(|(_, t)| t).unwrap_or_default();
    if air.statement() != recursive_statement(&air.statement_header(), &tuples) {
        return None; // not a statement this circuit knows how to lay out
    }
    let layout = stark::layout(air, params)?;
    let n = air.trace_len();
    let witness_width = air.width();
    let width = stark::full_width(air);
    let aux_width = air.num_aux_columns();
    let leaves_log = layout.log_lde - 1;

    // ---- transcript up to z ----
    let mut t = Transcript::new(b, stark::STATEMENT_LABEL);
    let shape: Vec<OVar> = octets(&stark::shape_elements(air)).into_iter().map(|o| b.const_octet(o)).collect();
    t.absorb_octets(b, stark::STATEMENT_LABEL, &shape);
    let preprocessed_cap = air.preprocessed().map(|p| {
        let table = cap_table(b, &p.cap);
        t.absorb_octets(b, stark::PREPROCESSED_ROOT_LABEL, &table_octets(&table));
        table
    });
    let mut statement: Vec<OVar> = octets(&air.statement_header()).into_iter().map(|o| b.const_octet(o)).collect();
    statement.push(b.const_octet(octet_of(BabyBear::new(tuples.len() as u32))));
    let mut tuple_cells = Vec::with_capacity(tuples.len());
    let mut tuple_headers = Vec::with_capacity(tuples.len());
    for (m, tuple) in &tuples {
        let mut header = octet_of(*m);
        header[1] = BabyBear::new(tuple.len() as u32);
        let header = b.witness_octet(header);
        statement.push(header);
        tuple_headers.push(header);
        let cells: Vec<OVar> = octets(tuple).into_iter().map(|o| b.witness_octet(o)).collect();
        statement.extend_from_slice(&cells);
        tuple_cells.push(cells);
    }
    t.absorb_octets(b, stark::PUBLIC_LABEL, &statement);
    let trace_cap = cap_table(b, &proof.trace_cap);
    t.absorb_octets(b, stark::TRACE_ROOT_LABEL, &table_octets(&trace_cap));
    let challenges: Vec<EVar> = (0..air.num_challenges())
        .map(|_| t.challenge_ext(b, stark::AUX_CHALLENGE_LABEL))
        .collect();
    let aux_cap = cap_table(b, &proof.aux_cap);
    t.absorb_octets(b, stark::AUX_ROOT_LABEL, &table_octets(&aux_cap));
    let alpha = t.challenge_ext(b, stark::ALPHA_LABEL);
    let composition_cap = cap_table(b, &proof.composition_cap);
    t.absorb_octets(b, stark::COMPOSITION_ROOT_LABEL, &table_octets(&composition_cap));
    let z = t.challenge_ext(b, stark::Z_LABEL);
    let g = domain_generator(layout.log_n);
    let zg = b.scale(z, g);

    // ---- the constraints at z reproduce the composition value ----
    let main_z = witness_exts(b, &proof.trace_at_z);
    let main_zg = witness_exts(b, &proof.trace_at_zg);
    let aux_z = witness_exts(b, &proof.aux_at_z);
    let aux_zg = witness_exts(b, &proof.aux_at_zg);
    let composition_z = b.witness_ext(proof.composition_at_z);

    let periodic: Vec<EVar> = stark::periodic_polys(&air.periodic_columns(), n)
        .iter()
        .map(|(exponent, coeffs)| {
            let y = square_times(b, z, exponent.trailing_zeros() as usize);
            let one = b.one();
            let mut acc = b.zero();
            for &c in coeffs.iter().rev() {
                let zr = BabyBear::ZERO;
                acc = b.arith(BabyBear::ONE, Some(acc), Some(y), zr, zr, Some(one), c, [zr; 4]);
            }
            acc
        })
        .collect();
    let program = symbolic::compile(air);
    let mut node_values: Vec<EVar> = Vec::with_capacity(program.nodes.len());
    for &node in &program.nodes {
        let v = |i: u32| node_values[i as usize];
        let value = match node {
            Node::Const(c) => b.const_base(BabyBear::new(c)),
            Node::Input(Var::Main { next: false, column }) => main_z[column],
            Node::Input(Var::Main { next: true, column }) => main_zg[column],
            Node::Input(Var::Aux { next: false, column }) => aux_z[column],
            Node::Input(Var::Aux { next: true, column }) => aux_zg[column],
            Node::Input(Var::Periodic(i)) => periodic[i],
            Node::Input(Var::Challenge(i)) => challenges[i],
            Node::Add(x, y) => b.add(v(x), v(y)),
            Node::Sub(x, y) => b.sub(v(x), v(y)),
            Node::Mul(x, y) => b.mul(v(x), v(y)),
            Node::Neg(x) => b.scale(v(x), -BabyBear::ONE),
        };
        node_values.push(value);
    }
    let transition_terms: Vec<EVar> = program
        .main_outputs
        .iter()
        .chain(&program.aux_outputs)
        .map(|&i| node_values[i as usize])
        .collect();

    let z_n = square_times(b, z, layout.log_n);
    let z_n_minus_one = b.add_base(z_n, -BabyBear::ONE);
    let vanishing_inv = b.inverse(z_n_minus_one);
    let z_minus_last = b.add_base(z, -g.pow(n as u64 - 1));
    let divisor_inv = b.mul(z_minus_last, vanishing_inv);
    let mut row_invs: std::collections::BTreeMap<usize, EVar> = Default::default();
    let mut row_inv = |b: &mut Builder, row: usize| -> EVar {
        *row_invs.entry(row).or_insert_with(|| {
            let d = b.add_base(z, -g.pow(row as u64));
            b.inverse(d)
        })
    };
    let mut boundary_terms = Vec::new();
    for bd in air.boundaries() {
        let d = b.add_base(main_z[bd.column], -bd.value);
        let inv = row_inv(b, bd.row);
        boundary_terms.push(b.mul(d, inv));
    }
    // Auxiliary boundaries: a bus's running sum, 0 first and the public
    // sum last -- recomputed here from the public tuples.
    let native_challenges: Vec<Ext> = challenges.iter().map(|&c| b.ext_value(c)).collect();
    let bus = air.bus();
    let expected_aux = match &bus {
        Some((bus, tuples)) => bus.boundaries(n, bus.public_sum(tuples, &native_challenges)),
        None => Vec::new(),
    };
    if air.aux_boundaries(&native_challenges) != expected_aux {
        return None; // not a shape this circuit knows how to recompute
    }
    if let Some((bus, tuples)) = bus {
        let column = bus.aux_offset + bus.slots;
        let (gamma, beta) = (challenges[bus.challenge_offset], challenges[bus.challenge_offset + 1]);
        let mut public_sum = b.zero();
        for (((_, tuple), cells), &header) in tuples.iter().zip(&tuple_cells).zip(&tuple_headers) {
            let mut acc = b.zero();
            for j in (0..tuple.len()).rev() {
                let (half, lane) = element(b, cells, j);
                acc = b.horner_lane(acc, beta, half, lane);
            }
            let fingerprint = b.sub(gamma, acc);
            let inv = b.inverse(fingerprint);
            let (header_lo, _) = b.halves(header);
            let m = b.lane(header_lo, 0);
            public_sum = b.mul_add(m, inv, public_sum);
        }
        let first = row_inv(b, 0);
        boundary_terms.push(b.mul(aux_z[column], first));
        let d = b.sub(aux_z[column], public_sum);
        let last = row_inv(b, n - 1);
        boundary_terms.push(b.mul(d, last));
    }
    // Weights alpha^k: transitions first (scaled by the divisor), then
    // boundaries.
    let mut weight = b.one();
    let mut transition_sum = b.zero();
    for &term in &transition_terms {
        transition_sum = b.mul_add(weight, term, transition_sum);
        weight = b.mul(weight, alpha);
    }
    let mut expected = b.mul(transition_sum, divisor_inv);
    for &term in &boundary_terms {
        expected = b.mul_add(weight, term, expected);
        weight = b.mul(weight, alpha);
    }
    b.assert_eq(expected, composition_z);

    // ---- DEEP constants ----
    let ood: Vec<EVar> = main_z
        .iter()
        .chain(&main_zg)
        .chain(&aux_z)
        .chain(&aux_zg)
        .copied()
        .chain([composition_z])
        .collect();
    t.absorb_exts(b, stark::OOD_LABEL, &ood);
    let beta = t.challenge_ext(b, stark::BETA_LABEL);
    let beta2 = b.mul(beta, beta);
    let horner = |b: &mut Builder, values: &[EVar]| -> EVar {
        let mut acc = b.zero();
        for &v in values.iter().rev() {
            acc = b.mul_add(acc, beta2, v);
        }
        acc
    };
    let at_z_all: Vec<EVar> = main_z.iter().chain(&aux_z).copied().collect();
    let at_zg_all: Vec<EVar> = main_zg.iter().chain(&aux_zg).copied().collect();
    let constant_z = horner(b, &at_z_all);
    let constant_zg = horner(b, &at_zg_all);
    let w_composition = power(b, beta2, width + aux_width);
    let w_mask = b.mul(w_composition, beta);
    let composition_minus = |b: &mut Builder, c: EVar| b.sub(c, composition_z);

    // ---- FRI ----
    let settings = params.fri();
    let log_size = layout.log_lde;
    let arities = fri::round_arities(log_size, settings.log_blowup);
    let beta0 = t.challenge_ext(b, fri::FOLD_CHALLENGE_LABEL);
    let mut round_caps = Vec::new();
    let mut round_betas = Vec::new();
    for cap in &proof.fri.caps {
        let table = cap_table(b, cap);
        t.absorb_octets(b, fri::ROUND_ROOT_LABEL, &table_octets(&table));
        round_caps.push(table);
        round_betas.push(t.challenge_ext(b, fri::FOLD_CHALLENGE_LABEL));
    }
    // Each round's challenge squared once per binary fold in its leaf.
    let round_betas: Vec<Vec<EVar>> = round_betas
        .iter()
        .zip(&arities)
        .map(|(&beta, &bits)| {
            let mut powers = vec![beta];
            for _ in 1..bits {
                let last = *powers.last().unwrap();
                powers.push(b.mul(last, last));
            }
            powers
        })
        .collect();
    let final_value = b.witness_ext(proof.fri.final_value);
    t.absorb_exts(b, fri::FINAL_VALUE_LABEL, &[final_value]);
    let nonce = b.witness_ext(Ext::from_base(BabyBear::new(proof.fri.grinding_nonce as u32)));
    let zero = b.zero();
    let nonce_octet = b.pack(nonce, zero);
    t.absorb_octets(b, fri::GRIND_LABEL, &[nonce_octet]);
    if settings.grinding_bits > 0 {
        // The grinding check samples the state right after absorbing the
        // nonce -- without consuming it (the next challenge absorbs its
        // label first, which re-permutes anyway).
        let (sample, _) = b.halves(t.state[0]);
        let bits = Bits::of(b, sample);
        for &bit in &bits.bits[..settings.grinding_bits as usize] {
            b.assert_zero(bit);
        }
    }

    let lde_generator = domain_generator(log_size);
    let cap_bits = fri::CAP_HEIGHT;
    // Path bits and cap index for a tree of 2^tree_log leaves opened at
    // the position given by bits 0..tree_log of `bits`.
    let path_and_cap = |b: &mut Builder, bits: &Bits, tree_log: usize| -> (usize, EVar) {
        let path = tree_log.saturating_sub(cap_bits);
        (path, bits.slice(b, path, tree_log))
    };
    for (q, query) in proof.fri.query_proofs.iter().enumerate() {
        let sample = t.challenge_ext(b, fri::QUERY_INDEX_LABEL);
        let bits = Bits::of(b, sample);
        let low_bits = &bits.bits[..leaves_log];

        // First layer: the DEEP combination at x and -x, from the STARK
        // openings at `low`.
        let openings = &proof.queries[q];
        let (path, cap_index) = path_and_cap(b, &bits, leaves_log);
        let trace_leaf = witness_leaf(b, &openings.trace.leaf);
        merkle_check(b, &trace_leaf, openings.trace.leaf.len(), &openings.trace, &low_bits[..path], trace_cap, cap_index);
        let fixed_leaf = match (&openings.preprocessed, preprocessed_cap) {
            (Some(o), Some(table)) => {
                let leaf = witness_leaf(b, &o.leaf);
                merkle_check(b, &leaf, o.leaf.len(), o, &low_bits[..path], table, cap_index);
                leaf
            }
            _ => Vec::new(),
        };
        let aux_leaf = witness_leaf(b, &openings.aux.leaf);
        merkle_check(b, &aux_leaf, openings.aux.leaf.len(), &openings.aux, &low_bits[..path], aux_cap, cap_index);
        let composition_leaf = witness_leaf(b, &openings.composition.leaf);
        merkle_check(
            b,
            &composition_leaf,
            openings.composition.leaf.len(),
            &openings.composition,
            &low_bits[..path],
            composition_cap,
            cap_index,
        );

        let x = power_from_bits(b, COSET_SHIFT, lde_generator, low_bits);
        let neg_x = b.scale(x, -BabyBear::ONE);
        let fixed_width = width - witness_width;
        let mut sides = Vec::with_capacity(2);
        for (side, point) in [x, neg_x].into_iter().enumerate() {
            // S = Σ_j beta^(2j) · t_j over the full row then aux values.
            let mut s = b.zero();
            for k in (0..aux_width).rev() {
                let v = ext_element(b, &aux_leaf, side * aux_width + k);
                s = b.mul_add(s, beta2, v);
            }
            for j in (0..width).rev() {
                let (half, lane) = if j < witness_width {
                    element(b, &trace_leaf, side * witness_width + j)
                } else {
                    element(b, &fixed_leaf, side * fixed_width + (j - witness_width))
                };
                s = b.horner_lane(s, beta2, half, lane);
            }
            let composition = ext_element(b, &composition_leaf, 2 * side);
            let mask = ext_element(b, &composition_leaf, 2 * side + 1);
            let x_minus_z = b.sub(point, z);
            let inv_z = b.inverse(x_minus_z);
            let x_minus_zg = b.sub(point, zg);
            let inv_zg = b.inverse(x_minus_zg);
            let mut e1 = b.sub(s, constant_z);
            let c = composition_minus(b, composition);
            e1 = b.mul_add(w_composition, c, e1);
            let t1 = b.mul(inv_z, e1);
            let e2 = b.sub(s, constant_zg);
            let t2 = b.mul(inv_zg, e2);
            let t2 = b.mul(t2, beta);
            let sum = b.add(t1, t2);
            sides.push(b.mul_add(w_mask, mask, sum));
        }
        let x_inv = b.inverse(x);
        let mut value = fold_pair(b, sides[0], sides[1], x_inv, beta0);

        // Committed rounds.
        let mut log = log_size - 1;
        let mut layer_shift = COSET_SHIFT * COSET_SHIFT;
        for (r, &arity) in arities.iter().enumerate() {
            let group_log = log - arity;
            let opening = &query.openings[r];
            let values: Vec<Ext> = leaf_elements(&opening.leaf).chunks(4).map(|c| Ext(c.try_into().unwrap())).collect();
            let table = b.witness_ext_table(&values);
            let leaf: Vec<OVar> = (0..values.len() / 2).map(|k| b.pack(table.ext(2 * k), table.ext(2 * k + 1))).collect();
            let (path, cap_index) = path_and_cap(b, &bits, group_log);
            merkle_check(b, &leaf, opening.leaf.len(), opening, &bits.bits[..path], round_caps[r], cap_index);
            let slot = bits.slice(b, group_log, log);
            b.lookup_ext(value, table, slot);

            // fold_leaf: points shift_r · g_log^(j + m·group), j the low
            // `group_log` bits.
            let g_log = domain_generator(log);
            let x_j = power_from_bits(b, layer_shift, g_log, &bits.bits[..group_log]);
            let mut x_inv = b.inverse(x_j);
            let mut level: Vec<EVar> = (0..values.len()).map(|k| table.ext(k)).collect();
            let mut level_log = log;
            let group = 1usize << group_log;
            for beta_level in &round_betas[r] {
                let half = level.len() / 2;
                let g = domain_generator(level_log);
                let mut next = Vec::with_capacity(half);
                for m in 0..half {
                    let xm_inv = if m == 0 {
                        x_inv
                    } else {
                        b.scale(x_inv, g.pow((m * group) as u64).inverse())
                    };
                    next.push(fold_pair(b, level[m], level[m + half], xm_inv, *beta_level));
                }
                level = next;
                x_inv = b.mul(x_inv, x_inv);
                level_log -= 1;
            }
            value = level[0];
            for _ in 0..arity {
                layer_shift = layer_shift * layer_shift;
            }
            log -= arity;
        }
        b.assert_eq(value, final_value);
    }
    Some(Statement {
        octets: statement,
        tuple_headers,
        tuples: tuple_cells,
        preprocessed_cap,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::Circuit;
    use crate::stark::Air;

    fn reward_only_witness() -> crate::block_air::Witness {
        let (_, pk) = crate::wots::keygen(&[1; 32]);
        let mut tx = crate::transaction::Transaction::new();
        tx.add_output(crate::output::Output::new(&pk, crate::prover::REWARD)).unwrap();
        crate::block_air::build(&[tx], crate::prover::REWARD).unwrap()
    }

    fn challenges() -> Vec<Ext> {
        let mut t = crate::transcript::Transcript::new(b"recursion test");
        (0..2).map(|_| t.challenge_ext(b"c")).collect()
    }

    /// Build the circuit verifying a reward-only block proof made at
    /// `inner` parameters.
    fn block_verifier(inner: &Params) -> (Circuit, crate::block_air::Witness) {
        let witness = reward_only_witness();
        let proof = stark::prove(&witness.air, &witness.trace, inner, [5; 32]).unwrap();
        let mut b = Builder::new();
        verify(&mut b, &witness.air, &proof, inner).unwrap();
        let (perms, rows) = b.size();
        let circuit = b.finish();
        println!("verifier circuit: {perms} permutations, {rows} other rows, {} rows total", circuit.trace_len);
        (circuit, witness)
    }

    /// Small parameters keep the debug-build test quick; the consensus
    /// ones are exercised by the ignored measurement below.
    const SMALL: Params = Params {
        log_blowup: 2,
        num_queries: 4,
        grinding_bits: 3,
        hiding: true,
    };

    #[test]
    fn the_verifier_circuit_accepts_a_real_block_proof() {
        let (circuit, _) = block_verifier(&SMALL);
        let air = circuit.air(&Params { log_blowup: 1, num_queries: 2, grinding_bits: 0, hiding: true });
        stark::check(&air, &circuit.witness, &challenges()).unwrap();
    }

    #[test]
    fn the_verifier_circuit_has_the_same_shape_for_every_proof() {
        let witness = reward_only_witness();
        let shape = |seed: u8| {
            let proof = stark::prove(&witness.air, &witness.trace, &SMALL, [seed; 32]).unwrap();
            let mut b = Builder::new();
            verify(&mut b, &witness.air, &proof, &SMALL).unwrap();
            b.finish()
        };
        let (a, c) = (shape(1), shape(2));
        assert_eq!(a.preprocessed, c.preprocessed);
        // Public cells (constants, the inner statement) are the same too.
        assert_eq!(a.public, c.public);
        assert_ne!(a.witness, c.witness);
    }

    /// The verified statement comes back as cells holding exactly the
    /// AIR's statement, ready for the caller to bind.
    #[test]
    fn the_statement_comes_back_as_cells() {
        let witness = reward_only_witness();
        let proof = stark::prove(&witness.air, &witness.trace, &SMALL, [5; 32]).unwrap();
        let mut b = Builder::new();
        let statement = verify(&mut b, &witness.air, &proof, &SMALL).unwrap();
        let values: Vec<BabyBear> = statement.octets.iter().flat_map(|&o| b.octet_value(o)).collect();
        assert_eq!(values, witness.air.statement());
        assert_eq!(statement.tuples.len(), witness.air.bus().unwrap().1.len());
        assert!(statement.preprocessed_cap.is_none());
    }

    #[test]
    fn a_bad_proof_gets_no_circuit() {
        let witness = reward_only_witness();
        let mut proof = stark::prove(&witness.air, &witness.trace, &SMALL, [5; 32]).unwrap();
        proof.composition_at_z = proof.composition_at_z + Ext::ONE;
        assert!(verify(&mut Builder::new(), &witness.air, &proof, &SMALL).is_none());
    }

    /// Not a correctness test: the size and cost of verifying a block
    /// proof in-circuit at the consensus parameters, and of proving that
    /// circuit. Run with
    /// `cargo test --release -- --ignored --nocapture recursion_cost`.
    #[test]
    #[ignore]
    fn recursion_cost() {
        let inner = crate::prover::PARAMS;
        let start = std::time::Instant::now();
        let (circuit, _) = block_verifier(&inner);
        println!("built in {:.2?}", start.elapsed());
        for outer in [
            Params { log_blowup: 1, num_queries: 84, grinding_bits: 16, hiding: true },
            crate::prover::PARAMS,
        ] {
            let start = std::time::Instant::now();
            let air = circuit.air(&outer);
            let commit = start.elapsed();
            let start = std::time::Instant::now();
            let proof = stark::prove(&air, &circuit.witness, &outer, [6; 32]).unwrap();
            let proving = start.elapsed();
            let start = std::time::Instant::now();
            assert!(stark::verify(&air, &proof, &outer));
            println!(
                "outer {outer:?}: fixed columns {commit:.2?}, prove {proving:.2?}, verify {:.2?}, {} KB",
                start.elapsed(),
                proof.to_bytes().len() / 1024
            );
        }
    }
}
