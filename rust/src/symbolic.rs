//! Constraints as data: run an AIR's constraint code on *symbolic* values
//! and record what it computes, as a straight-line program of field
//! operations.
//!
//! A verifier evaluates the AIR's constraints at the out-of-domain point
//! `z`. Natively that's just calling `eval_transition` /
//! `eval_aux_transition` over `Ext`; but an aggregation circuit (see
//! `docs/RECURSION.md`) has to do the same *inside* a proof, so it needs
//! the constraints as a fixed list of operations it can check one by one.
//! Both evaluation methods are generic over `Field`, so implementing
//! `Field` for `Expr` -- a handle to a node in a recorded expression graph
//! -- extracts that list from the very code the prover runs. No AIR is
//! rewritten by hand, and the program can't drift from the constraints.
//!
//! The recorded graph is deduplicated (identical subexpressions share one
//! node), constant-folded, simplified for the trivial identities (`x + 0`,
//! `x · 1`, `x · 0`, `x - x`), and pruned to what the constraints use.
//! Constraints are polynomials, so there is no inverse: an AIR that tried
//! one during compilation panics.
//!
//! `Expr` is `Copy` (as `Field` requires) by being an index into a
//! thread-local arena, which `compile` resets: an `Expr` is meaningful only
//! during the `compile` call that made it.

#![allow(dead_code)]

use std::cell::RefCell;
use std::collections::HashMap;

use crate::ext::Ext;
use crate::field::Field;
use crate::poseidon2::{BabyBear, DOMAIN_PROGRAM, hash_elements};
use crate::stark::{Air, AuxFrame};

/// An input to the program: a value the verifier has at `z`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Var {
    /// Main trace column at `z` (`next: false`) or `z·g` (`next: true`).
    Main { next: bool, column: usize },
    /// Auxiliary column, likewise.
    Aux { next: bool, column: usize },
    /// A periodic column's value at `z`.
    Periodic(usize),
    /// An auxiliary-phase challenge.
    Challenge(usize),
}

/// One operation. Operands refer to earlier nodes, so the node list is
/// already in evaluation order.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Node {
    Const(u32),
    Input(Var),
    Add(u32, u32),
    Sub(u32, u32),
    Mul(u32, u32),
    Neg(u32),
}

#[derive(Default)]
struct Arena {
    nodes: Vec<Node>,
    index: HashMap<Node, u32>,
}

thread_local! {
    static ARENA: RefCell<Arena> = RefCell::new(Arena::default());
}

/// A symbolic field value: a node in the current recording.
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Expr(u32);

impl Arena {
    fn reset(&mut self) {
        self.nodes.clear();
        self.index.clear();
        // Expr::ZERO and Expr::ONE are always nodes 0 and 1.
        self.intern(Node::Const(0));
        self.intern(Node::Const(1));
    }

    fn intern(&mut self, node: Node) -> u32 {
        if let Some(&i) = self.index.get(&node) {
            return i;
        }
        let i = self.nodes.len() as u32;
        self.nodes.push(node);
        self.index.insert(node, i);
        i
    }

    fn constant(&self, i: u32) -> Option<BabyBear> {
        match self.nodes[i as usize] {
            Node::Const(v) => Some(BabyBear::new(v)),
            _ => None,
        }
    }

    /// Record `node`, folding constants and trivial identities first.
    fn op(&mut self, node: Node) -> u32 {
        let c = |a| self.constant(a);
        let folded = match node {
            Node::Add(a, b) => match (c(a), c(b)) {
                (Some(x), Some(y)) => Some(Node::Const((x + y).value())),
                (Some(x), _) if x == BabyBear::ZERO => return b,
                (_, Some(y)) if y == BabyBear::ZERO => return a,
                // Canonical operand order, so a + b and b + a share a node.
                _ => Some(Node::Add(a.min(b), a.max(b))),
            },
            Node::Mul(a, b) => match (c(a), c(b)) {
                (Some(x), Some(y)) => Some(Node::Const((x * y).value())),
                (Some(x), _) | (_, Some(x)) if x == BabyBear::ZERO => return 0,
                (Some(x), _) if x == BabyBear::ONE => return b,
                (_, Some(y)) if y == BabyBear::ONE => return a,
                _ => Some(Node::Mul(a.min(b), a.max(b))),
            },
            Node::Sub(a, b) => match (c(a), c(b)) {
                _ if a == b => return 0,
                (Some(x), Some(y)) => Some(Node::Const((x - y).value())),
                (_, Some(y)) if y == BabyBear::ZERO => return a,
                (Some(x), _) if x == BabyBear::ZERO => Some(Node::Neg(b)),
                _ => None,
            },
            Node::Neg(a) => match c(a) {
                Some(x) => Some(Node::Const((-x).value())),
                None => match self.nodes[a as usize] {
                    Node::Neg(inner) => return inner,
                    _ => None,
                },
            },
            _ => None,
        };
        self.intern(folded.unwrap_or(node))
    }
}

fn record(node: Node) -> Expr {
    Expr(ARENA.with(|a| a.borrow_mut().op(node)))
}

impl Expr {
    fn input(var: Var) -> Expr {
        Expr(ARENA.with(|a| a.borrow_mut().intern(Node::Input(var))))
    }
}

impl std::ops::Add for Expr {
    type Output = Expr;
    fn add(self, rhs: Expr) -> Expr {
        record(Node::Add(self.0, rhs.0))
    }
}

impl std::ops::Sub for Expr {
    type Output = Expr;
    fn sub(self, rhs: Expr) -> Expr {
        record(Node::Sub(self.0, rhs.0))
    }
}

impl std::ops::Mul for Expr {
    type Output = Expr;
    fn mul(self, rhs: Expr) -> Expr {
        record(Node::Mul(self.0, rhs.0))
    }
}

impl std::ops::Neg for Expr {
    type Output = Expr;
    fn neg(self) -> Expr {
        record(Node::Neg(self.0))
    }
}

impl Field for Expr {
    const ZERO: Self = Expr(0);
    const ONE: Self = Expr(1);

    fn from_base(value: BabyBear) -> Self {
        Expr(ARENA.with(|a| a.borrow_mut().intern(Node::Const(value.value()))))
    }

    fn mul_base(self, rhs: BabyBear) -> Self {
        self * Expr::from_base(rhs)
    }

    fn inverse(self) -> Self {
        panic!("constraints must be polynomials: inverse has no symbolic form");
    }
}

/// An AIR's transition constraints -- main, then auxiliary -- as a
/// straight-line program over the values a verifier has at `z`.
#[derive(Clone, Debug, PartialEq)]
pub struct Program {
    /// Operations in evaluation order; operands index earlier entries.
    pub nodes: Vec<Node>,
    /// Which node is each main transition constraint.
    pub main_outputs: Vec<u32>,
    /// Which node is each auxiliary transition constraint.
    pub aux_outputs: Vec<u32>,
}

/// What the program reads: the values at `z` and `z·g`, the periodic
/// values at `z`, and the challenges.
pub struct Inputs<'a> {
    pub main_z: &'a [Ext],
    pub main_zg: &'a [Ext],
    pub aux_z: &'a [Ext],
    pub aux_zg: &'a [Ext],
    pub periodic: &'a [Ext],
    pub challenges: &'a [Ext],
}

/// Operation counts -- what evaluating the program in a circuit costs.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Stats {
    pub inputs: usize,
    pub constants: usize,
    pub additions: usize,
    pub multiplications: usize,
}

/// Record `air`'s constraints as a program.
pub fn compile<A: Air>(air: &A) -> Program {
    ARENA.with(|a| a.borrow_mut().reset());
    let inputs = |n: usize, var: fn(usize) -> Var| -> Vec<Expr> { (0..n).map(|i| Expr::input(var(i))).collect() };
    // Witness columns then preprocessed ones, as constraints see them.
    let width = crate::stark::full_width(air);
    let main_current = inputs(width, |column| Var::Main { next: false, column });
    let main_next = inputs(width, |column| Var::Main { next: true, column });
    let aux_current = inputs(air.num_aux_columns(), |column| Var::Aux { next: false, column });
    let aux_next = inputs(air.num_aux_columns(), |column| Var::Aux { next: true, column });
    let periodic = inputs(air.periodic_columns().len(), Var::Periodic);
    let challenges = inputs(air.num_challenges(), Var::Challenge);

    let mut main_out = vec![Expr::ZERO; air.num_transition_constraints()];
    air.eval_transition(&main_current, &main_next, &periodic, &mut main_out);
    let mut aux_out = vec![Expr::ZERO; air.num_aux_constraints()];
    let frame = AuxFrame {
        main_current: &main_current,
        main_next: &main_next,
        aux_current: &aux_current,
        aux_next: &aux_next,
        periodic: &periodic,
        challenges: &challenges,
    };
    air.eval_aux_transition(&frame, &mut aux_out);

    let recorded = ARENA.with(|a| std::mem::take(&mut a.borrow_mut().nodes));
    ARENA.with(|a| a.borrow_mut().index.clear());
    prune(&recorded, &main_out, &aux_out)
}

/// Keep only the nodes the outputs depend on, renumbered in order.
fn prune(nodes: &[Node], main_out: &[Expr], aux_out: &[Expr]) -> Program {
    let mut live = vec![false; nodes.len()];
    for e in main_out.iter().chain(aux_out) {
        live[e.0 as usize] = true;
    }
    for i in (0..nodes.len()).rev() {
        if !live[i] {
            continue;
        }
        match nodes[i] {
            Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
                live[a as usize] = true;
                live[b as usize] = true;
            }
            Node::Neg(a) => live[a as usize] = true,
            Node::Const(_) | Node::Input(_) => {}
        }
    }
    let mut renumber = vec![u32::MAX; nodes.len()];
    let mut kept = Vec::new();
    for (i, &node) in nodes.iter().enumerate() {
        if !live[i] {
            continue;
        }
        let r = |x: u32| renumber[x as usize];
        let renumbered = match node {
            Node::Add(a, b) => Node::Add(r(a), r(b)),
            Node::Sub(a, b) => Node::Sub(r(a), r(b)),
            Node::Mul(a, b) => Node::Mul(r(a), r(b)),
            Node::Neg(a) => Node::Neg(r(a)),
            other => other,
        };
        renumber[i] = kept.len() as u32;
        kept.push(renumbered);
    }
    let outputs = |es: &[Expr]| es.iter().map(|e| renumber[e.0 as usize]).collect();
    Program {
        nodes: kept,
        main_outputs: outputs(main_out),
        aux_outputs: outputs(aux_out),
    }
}

impl Program {
    /// Evaluate at the given inputs: (main constraint values, auxiliary
    /// constraint values) -- the same as calling the AIR's evaluation
    /// methods over `Ext`.
    pub fn eval(&self, inputs: &Inputs) -> (Vec<Ext>, Vec<Ext>) {
        let mut values: Vec<Ext> = Vec::with_capacity(self.nodes.len());
        for &node in &self.nodes {
            let v = |x: u32| values[x as usize];
            let value = match node {
                Node::Const(c) => Ext::from_base(BabyBear::new(c)),
                Node::Input(var) => match var {
                    Var::Main { next: false, column } => inputs.main_z[column],
                    Var::Main { next: true, column } => inputs.main_zg[column],
                    Var::Aux { next: false, column } => inputs.aux_z[column],
                    Var::Aux { next: true, column } => inputs.aux_zg[column],
                    Var::Periodic(i) => inputs.periodic[i],
                    Var::Challenge(i) => inputs.challenges[i],
                },
                Node::Add(a, b) => v(a) + v(b),
                Node::Sub(a, b) => v(a) - v(b),
                Node::Mul(a, b) => v(a) * v(b),
                Node::Neg(a) => -v(a),
            };
            values.push(value);
        }
        let pick = |outputs: &[u32]| outputs.iter().map(|&i| values[i as usize]).collect();
        (pick(&self.main_outputs), pick(&self.aux_outputs))
    }

    pub fn stats(&self) -> Stats {
        let mut s = Stats::default();
        for node in &self.nodes {
            match node {
                Node::Const(_) => s.constants += 1,
                Node::Input(_) => s.inputs += 1,
                Node::Add(..) | Node::Sub(..) | Node::Neg(_) => s.additions += 1,
                Node::Mul(..) => s.multiplications += 1,
            }
        }
        s
    }

    /// A hash identifying the program exactly -- part of a verifying key,
    /// so an aggregation proof can name which constraints it checked.
    pub fn digest(&self) -> [BabyBear; 8] {
        let n = |v: usize| BabyBear::new(v as u32);
        let mut elements = vec![n(self.nodes.len()), n(self.main_outputs.len()), n(self.aux_outputs.len())];
        for &node in &self.nodes {
            let (op, a, b) = match node {
                Node::Const(c) => (0, c, 0),
                Node::Input(Var::Main { next, column }) => (1, column as u32, next as u32),
                Node::Input(Var::Aux { next, column }) => (2, column as u32, next as u32),
                Node::Input(Var::Periodic(i)) => (3, i as u32, 0),
                Node::Input(Var::Challenge(i)) => (4, i as u32, 0),
                Node::Add(a, b) => (5, a, b),
                Node::Sub(a, b) => (6, a, b),
                Node::Mul(a, b) => (7, a, b),
                Node::Neg(a) => (8, a, 0),
            };
            elements.extend([BabyBear::new(op), BabyBear::new(a), BabyBear::new(b)]);
        }
        elements.extend(self.main_outputs.iter().chain(&self.aux_outputs).map(|&i| BabyBear::new(i)));
        hash_elements(DOMAIN_PROGRAM, &elements)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transcript::Transcript;

    fn random(t: &mut Transcript, n: usize) -> Vec<Ext> {
        (0..n).map(|_| t.challenge_ext(b"x")).collect()
    }

    /// The program and the AIR's own code agree at a random point.
    fn agrees_with_direct_evaluation<A: Air>(air: &A) -> Program {
        let program = compile(air);
        let mut t = Transcript::new(b"symbolic test");
        let (w, a) = (crate::stark::full_width(air), air.num_aux_columns());
        let (mz, mzg, az, azg) = (random(&mut t, w), random(&mut t, w), random(&mut t, a), random(&mut t, a));
        let p = random(&mut t, air.periodic_columns().len());
        let ch = random(&mut t, air.num_challenges());

        let mut main = vec![Ext::ZERO; air.num_transition_constraints()];
        air.eval_transition(&mz, &mzg, &p, &mut main);
        let mut aux = vec![Ext::ZERO; air.num_aux_constraints()];
        let frame = AuxFrame {
            main_current: &mz,
            main_next: &mzg,
            aux_current: &az,
            aux_next: &azg,
            periodic: &p,
            challenges: &ch,
        };
        air.eval_aux_transition(&frame, &mut aux);

        let inputs = Inputs {
            main_z: &mz,
            main_zg: &mzg,
            aux_z: &az,
            aux_zg: &azg,
            periodic: &p,
            challenges: &ch,
        };
        assert_eq!(program.eval(&inputs), (main, aux));
        program
    }

    fn reward_only_block() -> crate::block_air::Witness {
        let (_, pk) = crate::wots::keygen(&[1; 32]);
        let mut tx = crate::transaction::Transaction::new();
        tx.add_output(crate::output::Output::new(&pk, crate::prover::REWARD)).unwrap();
        crate::block_air::build(&[tx], crate::prover::REWARD).unwrap()
    }

    #[test]
    fn block_circuit_compiles_to_an_equivalent_program() {
        let witness = reward_only_block();
        let program = agrees_with_direct_evaluation(&witness.air);
        let s = program.stats();
        println!("block circuit: {} nodes, {s:?}", program.nodes.len());
        // Deduplication actually happened: far fewer nodes than a naive
        // recording, and every input appears once.
        assert!(s.inputs <= 2 * witness.air.width() + 2 * witness.air.num_aux_columns() + 64);
    }

    #[test]
    fn compiling_is_deterministic_and_the_digest_pins_the_program() {
        let witness = reward_only_block();
        let a = compile(&witness.air);
        let b = compile(&witness.air);
        assert_eq!(a, b);
        assert_eq!(a.digest(), b.digest());
        let mut altered = a.clone();
        let last = altered.main_outputs.len() - 1;
        altered.main_outputs.swap(0, last);
        assert_ne!(a.digest(), altered.digest());
    }

    #[test]
    fn folding_and_sharing() {
        ARENA.with(|a| a.borrow_mut().reset());
        let x = Expr::input(Var::Main { next: false, column: 0 });
        let y = Expr::input(Var::Main { next: false, column: 1 });
        let two = Expr::from_base(BabyBear::new(2));
        assert_eq!(x + Expr::ZERO, x);
        assert_eq!(x * Expr::ONE, x);
        assert_eq!(x * Expr::ZERO, Expr::ZERO);
        assert_eq!(x - x, Expr::ZERO);
        assert_eq!(-(-x), x);
        assert_eq!(two * two, Expr::from_base(BabyBear::new(4)));
        assert_eq!(x * y, y * x);
        assert_eq!(x + y, y + x);
        assert_ne!(x - y, y - x);
    }

    #[test]
    #[should_panic]
    fn inverse_is_refused() {
        ARENA.with(|a| a.borrow_mut().reset());
        let _ = Expr::input(Var::Challenge(0)).inverse();
    }
}
