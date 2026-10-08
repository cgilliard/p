//! The block statement as a STARK circuit: for public input and output
//! commitment lists and public amounts `a`, `b`, "there are transactions
//! such that every input is authorized by its owner's WOTS signature over
//! its transaction, every commitment is correctly formed, and
//! `sum(inputs) + a == sum(outputs) + b` exactly" -- with every public
//! key, amount, and signature kept private. A whole block is `a = reward`,
//! `b = 0`; a *chunk* of a block's transactions (see `aggregate`) has
//! whatever net its transactions leave, with the chunks' `a - b` summing
//! to the reward.
//!
//! # Layout
//!
//! The trace is a sequence of 32-row blocks (`poseidon2_air::ROWS`), each
//! computing one width-24 Poseidon2 permutation of its row-0 state with
//! the shared `Poseidon2Chip`. A block's *kind* -- one-hot flag columns,
//! constant within the block -- says what that permutation is for and how
//! its input is wired:
//!
//! - `CHAIN`: one WOTS chain step, `compress(param, TAG_CHAIN, c, s,
//!   value)`. Consecutive chain blocks of one chain pass the value along
//!   directly; a chain's first block takes a free starting value (the
//!   signature's) at the step its digit says, and its last (step 6) sends
//!   the chain's top on the bus. A digit of 7 means no steps at all.
//! - `PK`: one block of the public-key hash sponge (33 per key), each
//!   absorbing two whole tops (see `PublicKey::hash`). Sponge state passes
//!   block to block directly; each absorbed top is received from the bus
//!   -- from its chain's last block, or, for a chain with digit 7, straight
//!   from the signature (the digit itself is received instead).
//! - `DIG`: the digit derivation `compress(param, TAG_MESSAGE, bound,
//!   randomizer)`, whose 8 output elements are decomposed, canonically,
//!   into 3-bit digits in the block's spare rows -- the first 64 sent on
//!   the bus to their chains, and required to sum to `TARGET_SUM`. Each
//!   input's section starts with one; it receives the *bound* message
//!   from `BIND`, and sends its randomizer to `SEL`.
//! - `SEL`, `TLEAF`, `TNODE`, `BIND`: the text block the signature binds
//!   (`docs/BIBLE.md`, `wots::signed_digest`). `SEL` computes
//!   `compress(param, TAG_SELECT, message, randomizer)` and decomposes it
//!   like `DIG` does, sending its first element's low 16 bits -- the
//!   block's position -- to the path. `TLEAF` hashes the block (free
//!   witness, sent to `BIND`) into its leaf; sixteen `TNODE`s hash it up,
//!   each swapping by its bit, to `scripture::TEXT_ROOT`. `BIND` computes
//!   `compress(TAG_BIND, message, block)` and sends it to `DIG`. Both
//!   `SEL` and `BIND` receive the transaction's message.
//! - `CIN` / `COUT`: an input's / output's commitment
//!   `hash_elements(DOMAIN_COMMITMENT, pubkey_hash ‖ amount limbs)`. An
//!   input's key hash comes directly from the `PK` sponge just before it;
//!   an output's is free, and so is its recovery nonce (`NONCE`, eight
//!   16-bit limbs), which travels with its commitment everywhere below. Limbs are range-checked to 16 bits, and added
//!   to (inputs) or subtracted from (outputs) a running total -- kept
//!   normalized as it goes: four range-checked 16-bit limbs plus a small
//!   signed top limb, with carries of -1, 0, or +1 between them, so it
//!   can never wrap around the field however many commitments there are.
//!   Each sends its commitment (an output's with its nonce, in the same
//!   tuple) both to the public side of the bus and to its transaction's
//!   message.
//! - `MSG`: one block of a transaction's signing-message sponge: the first
//!   absorbs the input count, each later one exactly one item received
//!   from the bus -- an input's commitment (and zeros) or an output's
//!   commitment and nonce, whole, so a nonce can't be moved to another
//!   output. The last sends the message once per input of the
//!   transaction. Since the signatures cover the message, and the public
//!   side covers the nonces the block publishes, those are exactly the
//!   ones the outputs' owners signed.
//! - `PAD`: unused filler (the first block is always one).
//! - `BAL`: the last block, checking the running total plus `a` minus `b`
//!   comes out to exactly zero, carry by carry. `a` and `b` (as 16-bit
//!   limbs) are sent to the public side of the bus, so they're part of the
//!   statement without being built into the constraints.
//!
//! Where data must cross distant blocks it goes over one LogUp `bus`;
//! where it flows between neighbouring blocks it's wired directly. Each
//! input's blocks form one contiguous section with its own id, so no
//! section's data can be mistaken for another's.

#![allow(dead_code)]

use crate::bus::{self, Bus, Interaction};
use crate::ext::Ext;
use crate::field::Field;
use crate::output::{AMOUNT_LIMBS, amount_limbs};
use crate::poseidon2::{
    BabyBear, DOMAIN_COMMITMENT, DOMAIN_HASHLOCK, DOMAIN_KEY_NODE, DOMAIN_POLICY_LEAF, DOMAIN_POLICY_NODE, DOMAIN_PUBKEY, DOMAIN_REBIND, DOMAIN_SIGNING, Poseidon2BabyBear,
    digest_from_bytes, digest_to_bytes,
};
use crate::poseidon2_air::{Poseidon2Chip, ROWS};
use crate::stark::{Air, AuxBoundary, AuxFrame, Boundary};
use crate::transaction::{Spend, Transaction};
use crate::wots::{self, CHAIN_LEN, CHAIN_STEPS, PARAM_LEN, TAG_BIND, TAG_CHAIN, TAG_MESSAGE, TAG_SELECT, TARGET_SUM, V};

// ---- Columns -------------------------------------------------------------

const STATE: usize = 0;
const CHIP_WIDTH: usize = 48;

const K_CHAIN: usize = 48;
const K_PK: usize = 49;
const K_DIG: usize = 50;
const K_CIN: usize = 51;
const K_COUT: usize = 52;
const K_MSG: usize = 53;
const K_PAD: usize = 54;
const K_BAL: usize = 55;
const KINDS: [usize; 19] = [K_CHAIN, K_PK, K_DIG, K_CIN, K_COUT, K_MSG, K_PAD, K_BAL, K_SEL, K_TLEAF, K_TNODE, K_BIND, K_PHDR, K_PKEY, K_HLOCK, K_PNODE, K_KNODE, K_RHDR, K_RITEM];

const UID: usize = 56;
const TX: usize = 57;
/// Chain index (`CHAIN`), sponge block index (`PK`).
const C: usize = 58;
/// Chain step (`CHAIN`).
const S: usize = 59;
const START: usize = 60;
const END: usize = 61;
/// Inverse witness for `END`/`LAST`'s "is this value the limit" checks.
const W: usize = 62;
/// Whether a `PK` half is a digit-7 chain's top (taken from the signature).
const FLO: usize = 63;
const FHI: usize = 64;
const FIRST: usize = 65;
const LAST: usize = 66;
/// A `MSG` sponge's transaction input count.
const NIN: usize = 67;
/// Whether a `MSG` half is an input's commitment (vs an output's).
const RLO: usize = 68;
const RHI: usize = 69;
/// Whether a `MSG` half absorbs a commitment at all.
const ALO: usize = 70;
const AHI: usize = 71;
const FLAGS: [usize; 11] = [START, END, FLO, FHI, FIRST, LAST, RLO, RHI, ALO, AHI, RB];

/// The block's row-0 state, rate part -- kept constant down the block.
const IN: usize = 72;
/// The block's output state (row `OUT_ROW`) -- kept constant down the block.
const CARRY: usize = 88;
/// The previous block's output state, for sponge continuation.
const PREV: usize = 112;
/// The current input section's WOTS parameter.
const PARAM: usize = 136;
/// A commitment's amount limbs.
const LIMB: usize = 141;
const BIT: usize = 145;
const LACC: usize = 149;
/// The running total, inputs minus outputs: four 16-bit limbs (plus
/// `ACC_TOP` above them).
const ACC: usize = 153;
/// Carries between the running total's limbs (`CRY`..+3, then `CRY3`) --
/// at a commitment, its update's; in `BAL`, the final check's.
const CRY: usize = 157;
/// Digit decomposition lanes: remainder, then the digit's three bits.
const REM: usize = 160;
const B0: usize = 168;
const B1: usize = 176;
const B2: usize = 184;
/// Helpers for the canonical-decomposition check.
const H1: usize = 192;
const H2: usize = 200;
const DSUM: usize = 208;
/// The running total's signed top limb, holding carries out of the four
/// 16-bit ones.
const ACC_TOP: usize = 209;
const CRY3: usize = 210;
/// Range checks of the running total's limbs after each update.
const BIT2: usize = 211;
const LACC2: usize = 215;
/// An output's recovery nonce, as eight 16-bit limbs (`COUT`).
const NONCE: usize = 219;
const K_SEL: usize = 227;
const K_TLEAF: usize = 228;
const K_TNODE: usize = 229;
const K_BIND: usize = 230;
/// Policy blocks (`policy`): a branch leaf's header and key blocks, a
/// hash lock, a node of the path to the policy's root.
const K_PHDR: usize = 231;
const K_PKEY: usize = 232;
const K_HLOCK: usize = 233;
const K_PNODE: usize = 234;
/// A signer's policy section and key index (`PK`'s last block).
const GROUP: usize = 235;
const KIDX: usize = 236;
/// A `MSG` sponge's transaction signature count.
const NSIG: usize = 237;
/// The block's height: the same in every row.
const HEIGHT: usize = 238;
/// The spent output's creation height, through an input's sections.
const CREATED: usize = 239;
/// A node of the path from a signing key to its key tree's root
/// (`keytree`).
const K_KNODE: usize = 240;
/// A REBIND message's sponge (`transaction::rebind_message`): its header
/// `[m, state]`, then one block per output it names.
const K_RHDR: usize = 241;
const K_RITEM: usize = 242;
/// Whether a section signs (or a branch takes) REBIND signatures.
const RB: usize = 243;
/// How many REBIND messages name an output (`COUT`).
const NAMED: usize = 244;
pub const WIDTH: usize = 245;

/// The column holding carry `k` out of limb `k` of the running total.
fn carry_column(k: usize) -> usize {
    if k < 3 { CRY + k } else { CRY3 }
}

/// Columns constant within a block.
fn constant_columns() -> impl Iterator<Item = usize> {
    (K_CHAIN..LIMB + AMOUNT_LIMBS).chain(CRY..CRY + 3).chain([CRY3]).chain(NONCE..NONCE + 8).chain(K_SEL..WIDTH)
}

// ---- Periodic columns (after the chip's own) ----------------------------

const OUT_ROW: usize = 30;
const CHIP_PERIODIC: usize = 27;
const PR_ROW0: usize = CHIP_PERIODIC;
const PR_OUT: usize = CHIP_PERIODIC + 1;
/// Row 31: the transition into the next block.
const PR_X: usize = CHIP_PERIODIC + 2;
/// Rows 0..=30: transitions within the block.
const PR_IN: usize = CHIP_PERIODIC + 3;
const PR_LT16: usize = CHIP_PERIODIC + 4;
const PR_ROW16: usize = CHIP_PERIODIC + 5;
const PR_POW2: usize = CHIP_PERIODIC + 6;
const PR_LT10: usize = CHIP_PERIODIC + 7;
const PR_ROW9: usize = CHIP_PERIODIC + 8;
const PR_ROW10: usize = CHIP_PERIODIC + 9;
const PR_DROW: usize = CHIP_PERIODIC + 10;
const PR_LMASK6: usize = CHIP_PERIODIC + 11;
/// Rows 0-4 / row 5: where `SEL` sends its 16 position bits (three per
/// row, then one).
const PR_LT5: usize = CHIP_PERIODIC + 12;
const PR_ROW5: usize = CHIP_PERIODIC + 13;
const NUM_PERIODIC: usize = CHIP_PERIODIC + 14;

// ---- Bus ----------------------------------------------------------------

const TAG_CH: u32 = 1;
const TAG_TOP: u32 = 2;
const TAG_MSG: u32 = 3;
const TAG_ITEM: u32 = 4;
pub const TAG_PIN: u32 = 5;
pub const TAG_POUT: u32 = 6;
/// The public amounts `a`, `b`: `[TAG_NET, 0, 0, a limbs, b limbs]`.
pub const TAG_NET: u32 = 7;
/// `DIG` to `SEL`: the randomizer.
const TAG_RAND: u32 = 8;
/// `BIND` to `DIG`: the bound message.
const TAG_BOUND: u32 = 9;
/// `TLEAF` to `BIND`: the text block.
const TAG_TEXT: u32 = 10;
/// Up the text path: a level's input hash.
const TAG_TNODE: u32 = 11;
/// `SEL` to the path: one bit of the position.
const TAG_IDX: u32 = 12;
/// A signer's key hash, to its policy branch: `[TAG_KEY, section, key
/// index, key hash, transaction]`.
const TAG_KEY: u32 = 13;
/// A hash lock's image, to its branch's header.
const TAG_HASH: u32 = 14;
/// Up a policy's path: a level's input hash.
const TAG_PNODE: u32 = 15;
/// Up a key tree's path: a level's input hash.
const TAG_KNODE: u32 = 16;
/// A REBIND input's declared state, to its branch's header.
const TAG_RSTATE: u32 = 17;
/// An output a REBIND message names, from its `COUT`.
const TAG_RITEM: u32 = 18;
/// A REBIND message, to its signers: `[TAG_RMSG, section, 0, message]`.
const TAG_RMSG: u32 = 19;
/// The text path's length.
const TEXT_LEVELS: u32 = crate::scripture::DEPTH as u32;
/// `[tag, a, b]` and 16 values: an output's commitment and nonce, the
/// widest thing sent.
const TUPLE_LEN: usize = 19;
const BUS: Bus = Bus {
    slots: 9,
    aux_offset: 0,
    challenge_offset: 0,
};

/// Digit lanes: 8 elements of 10 base-8 digits, of which chains use the
/// first 64 (lanes 0-5 whole, lane 6's first 4).
const LANES: usize = 8;
const DIGITS_PER_LANE: usize = 10;
const PK_BLOCKS: usize = 33;
const PK_HASH_LEN: u32 = 8 + (V * CHAIN_LEN) as u32;
const COMMITMENT_LEN: u32 = 8 + AMOUNT_LIMBS as u32;

/// `log2` of the largest trace this circuit accepts under `params`: the
/// most rows whose low-degree extension -- 8× for the constraint degree,
/// times the blowup -- still fits in BabyBear's largest power-of-two
/// subgroup (2^27). Nothing about the circuit itself is bounded below
/// this: the running total stays normalized however many commitments
/// there are.
pub fn max_log_rows(params: &crate::stark::Params) -> usize {
    crate::fri::MAX_TWO_ADICITY - 3 - params.log_blowup
}

fn bb(v: u32) -> BabyBear {
    BabyBear::new(v)
}

/// The public statement: commitments spent and created, the amounts
/// `a` (added) and `b` (taken), and how many blocks the trace has.
pub struct BlockAir {
    chip: Poseidon2Chip<24>,
    num_blocks: usize,
    inputs: Vec<[BabyBear; 8]>,
    outputs: Vec<[BabyBear; 8]>,
    /// Each output's recovery nonce limbs, in `outputs`' order.
    nonces: Vec<[BabyBear; 8]>,
    net: (u64, u64),
    /// Public commitment slots, `(inputs, outputs)`: the lists padded to
    /// these lengths with unused entries (multiplicity 0), so every chunk
    /// of a given shape has the same statement layout. `None`: no padding.
    capacity: Option<(usize, usize)>,
    /// Each input's spent output's creation height, in `inputs`' order,
    /// and the block's height (`with_heights`).
    input_heights: Vec<u32>,
    height: u32,
    num_constraints: usize,
}

/// A fixed chunk shape: trace size and public commitment slots. Chunks of
/// one shape are all verified by one wrap circuit (`aggregate`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChunkShape {
    pub num_blocks: usize,
    pub inputs: usize,
    pub outputs: usize,
}

impl BlockAir {
    /// A whole block's statement: `a = reward`, `b = 0`.
    pub fn new(num_blocks: usize, inputs: Vec<[BabyBear; 8]>, outputs: Vec<[BabyBear; 8]>, nonces: Vec<[BabyBear; 8]>, reward: u64) -> Self {
        Self::with_net(num_blocks, inputs, outputs, nonces, (reward, 0))
    }

    /// `sum(inputs) + a == sum(outputs) + b`, `net = (a, b)`.
    pub fn with_net(
        num_blocks: usize,
        inputs: Vec<[BabyBear; 8]>,
        outputs: Vec<[BabyBear; 8]>,
        nonces: Vec<[BabyBear; 8]>,
        net: (u64, u64),
    ) -> Self {
        Self::chunk(num_blocks, inputs, outputs, nonces, net, None)
    }

    /// A chunk's statement, its commitment lists padded to `capacity`.
    pub fn chunk(
        num_blocks: usize,
        inputs: Vec<[BabyBear; 8]>,
        outputs: Vec<[BabyBear; 8]>,
        nonces: Vec<[BabyBear; 8]>,
        net: (u64, u64),
        capacity: Option<(usize, usize)>,
    ) -> Self {
        if let Some((i, o)) = capacity {
            assert!(inputs.len() <= i && outputs.len() <= o, "more commitments than slots");
        }
        assert_eq!(nonces.len(), outputs.len(), "one nonce per output");
        let inputs_len = inputs.len();
        let mut air = BlockAir {
            chip: Poseidon2Chip::<24>::new(),
            num_blocks,
            inputs,
            outputs,
            nonces,
            net,
            capacity,
            input_heights: vec![0; inputs_len],
            height: 0,
            num_constraints: 0,
        };
        let zeros = vec![BabyBear::ZERO; WIDTH];
        air.num_constraints = air.constraints(&zeros, &zeros, &[BabyBear::ZERO; NUM_PERIODIC]).len();
        air
    }

    pub fn num_blocks(&self) -> usize {
        self.num_blocks
    }

    /// The public commitment slots `(inputs, outputs)`, if padded.
    pub fn capacity(&self) -> Option<(usize, usize)> {
        self.capacity
    }

    /// The statement for a block at `height` whose inputs spend outputs
    /// created at `input_heights` (in `inputs`' order): both public, so
    /// timelocks are checked against them, and the wrap checks each input's
    /// against its spent leaf (`aggregate`).
    pub fn with_heights(mut self, height: u32, input_heights: Vec<u32>) -> Self {
        assert_eq!(input_heights.len(), self.inputs.len(), "one height per input");
        self.height = height;
        self.input_heights = input_heights;
        self
    }

    pub fn height(&self) -> u32 {
        self.height
    }

    pub fn public_input_heights(&self) -> &[u32] {
        &self.input_heights
    }

    pub fn public_inputs(&self) -> &[[BabyBear; 8]] {
        &self.inputs
    }

    pub fn public_outputs(&self) -> &[[BabyBear; 8]] {
        &self.outputs
    }

    pub fn public_nonces(&self) -> &[[BabyBear; 8]] {
        &self.nonces
    }

    pub fn net(&self) -> (u64, u64) {
        self.net
    }

    /// Every transition constraint, in a fixed order.
    fn constraints<F: Field>(&self, c: &[F], n: &[F], p: &[F]) -> Vec<F> {
        let mut out = Vec::with_capacity(600);
        let one = F::ONE;
        let k = |v: u32| F::from_base(bb(v));
        let (p0, pout, px, pin) = (p[PR_ROW0], p[PR_OUT], p[PR_X], p[PR_IN]);

        // The permutation itself.
        let mut chip = vec![F::ZERO; CHIP_WIDTH];
        self.chip.eval(&c[..CHIP_WIDTH], &n[..CHIP_WIDTH], &p[..CHIP_PERIODIC], &mut chip);
        out.extend(chip);

        // Block structure: constants, flags, bindings.
        for col in constant_columns() {
            out.push(pin * (n[col] - c[col]));
        }
        for &kind in &KINDS {
            out.push(c[kind] * (c[kind] - one));
        }
        out.push(KINDS.iter().fold(F::ZERO, |a, &kind| a + c[kind]) - one);
        for &flag in &FLAGS {
            out.push(c[flag] * (c[flag] - one));
        }
        for i in 0..16 {
            out.push(p0 * (c[IN + i] - c[STATE + i]));
        }
        for i in 0..24 {
            out.push(pout * (c[CARRY + i] - c[STATE + i]));
        }
        // Section ids, transaction ids, and the section's parameter and
        // creation height. A section starts at a signature's `DIG` or a
        // policy branch's `PHDR`.
        let starts = n[K_DIG] + n[K_PHDR];
        out.push(px * (n[UID] - c[UID] - starts));
        let continuing = n[K_CHAIN] + n[K_PK] + n[K_CIN] + n[K_SEL] + n[K_BIND] + n[K_PKEY] + n[K_HLOCK] + n[K_PNODE] + n[K_KNODE] + n[K_RHDR] + n[K_RITEM];
        out.push(px * (one - n[K_DIG]) * continuing * (n[TX] - c[TX]));
        for i in 0..PARAM_LEN {
            out.push(px * (one - starts) * (n[PARAM + i] - c[PARAM + i]));
        }
        out.push(px * (one - starts) * (n[CREATED] - c[CREATED]));
        // A signature section's mode (`RB`) and, for a policy signer, its
        // branch's section (`GROUP`), which a REBIND message comes from.
        out.push(px * (one - starts) * (n[RB] - c[RB]));
        out.push(px * (one - starts) * (n[GROUP] - c[GROUP]));
        // The block's height, everywhere.
        out.push(n[HEIGHT] - c[HEIGHT]);

        // CHAIN: input structure, end detection, continuity.
        let kc = c[K_CHAIN];
        for i in 0..PARAM_LEN {
            out.push(kc * (c[IN + i] - c[PARAM + i]));
        }
        out.push(kc * (c[IN + 5] - k(TAG_CHAIN)));
        out.push(kc * (c[IN + 6] - c[C]));
        out.push(kc * (c[IN + 7] - c[S]));
        for i in 16..24 {
            out.push(p0 * kc * c[STATE + i]);
        }
        let six = k(CHAIN_STEPS - 1);
        out.push(kc * c[END] * (c[S] - six));
        out.push(kc * (one - c[END]) * (one - (c[S] - six) * c[W]));
        let continues = n[K_CHAIN] * (one - n[START]);
        out.push(px * continues * (c[K_CHAIN] - one));
        out.push(px * continues * c[END]);
        out.push(px * kc * (one - c[END]) * (n[K_CHAIN] - one));
        out.push(px * kc * (one - c[END]) * n[START]);
        out.push(px * continues * (n[C] - c[C]));
        out.push(px * continues * (n[S] - c[S] - one));
        for i in 0..CHAIN_LEN {
            out.push(px * continues * (n[STATE + 8 + i] - c[CARRY + i] - c[IN + i]));
        }

        // Sponges (PK, MSG, a branch's PHDR and PKEY): initial state,
        // capacity, continuity.
        let (kp, km, kph, kpk, krh, kri) = (c[K_PK], c[K_MSG], c[K_PHDR], c[K_PKEY], c[K_RHDR], c[K_RITEM]);
        let sponge = kp + km + kph + kpk + krh + kri;
        for i in 16..24 {
            out.push(p0 * sponge * (c[STATE + i] - c[PREV + i]));
        }
        for i in (0..16).chain(18..24) {
            out.push(sponge * c[FIRST] * c[PREV + i]);
        }
        out.push(c[FIRST] * (kp * (c[PREV + 16] - k(DOMAIN_PUBKEY)) + km * (c[PREV + 16] - k(DOMAIN_SIGNING)) + kph * (c[PREV + 16] - k(DOMAIN_POLICY_LEAF))
                + krh * (c[PREV + 16] - k(DOMAIN_REBIND))));
        out.push(kp * c[FIRST] * (c[PREV + 17] - k(PK_HASH_LEN)));
        let n_continues = (n[K_PK] + n[K_MSG] + n[K_PKEY] + n[K_RITEM]) * (one - n[FIRST]);
        for i in 0..24 {
            out.push(px * n_continues * (n[PREV + i] - c[CARRY + i]));
        }
        let pk_continues = n[K_PK] * (one - n[FIRST]);
        out.push(px * pk_continues * (c[K_PK] - one));
        out.push(px * pk_continues * (n[C] - c[C] - one));
        let msg_continues = n[K_MSG] * (one - n[FIRST]);
        out.push(px * msg_continues * (c[K_MSG] - one));
        out.push(px * msg_continues * (n[TX] - c[TX]));
        out.push(px * msg_continues * (n[NIN] - c[NIN]));
        out.push(px * msg_continues * (n[NSIG] - c[NSIG]));

        // PK: param in the first block, nothing in the last's second half,
        // the end at block 32, and -- unless it signs for a policy branch
        // (`ALO`), sending its key hash there, or its key is in a key tree
        // (`RHI`), climbing to the root -- the input commitment right
        // after.
        out.push(kp * c[FIRST] * c[C]);
        for i in 0..8 {
            let absorbed = c[IN + i] - c[PREV + i];
            let expected = if i < PARAM_LEN { c[PARAM + i] } else { F::ZERO };
            out.push(kp * c[FIRST] * (absorbed - expected));
        }
        for i in 8..16 {
            out.push(kp * c[LAST] * (c[IN + i] - c[PREV + i]));
        }
        let last_block = k(PK_BLOCKS as u32 - 1);
        out.push(kp * c[LAST] * (c[C] - last_block));
        out.push(kp * (one - c[LAST]) * (one - (c[C] - last_block) * c[W]));
        out.push(kp * c[RHI] * c[ALO]);
        out.push(px * kp * c[LAST] * (one - c[ALO] - c[RHI]) * (n[K_CIN] - one));
        // (A plain input's signature signs the transaction.)
        out.push(kp * c[LAST] * (one - c[ALO] - c[RHI]) * c[RB]);
        // An input commitment's lock comes from the block before: a key's
        // id (its hash, or its key tree's root), or a policy's root (a
        // branch leaf without a path, or the path's top).
        let (kpn, khl, kkn) = (c[K_PNODE], c[K_HLOCK], c[K_KNODE]);
        let lockout = kp * c[LAST] * (one - c[ALO] - c[RHI]) + kkn * c[LAST] * (one - c[ALO]) + kpk * c[LAST] * (one - c[ALO]) + kpn * c[LAST];
        out.push(px * n[K_CIN] * (lockout - one));
        for i in 0..8 {
            out.push(px * n[K_CIN] * (n[STATE + i] - c[CARRY + i]));
        }

        // MSG: the input count first (and nothing else), then one item
        // per block.
        out.push(km * c[FIRST] * (c[IN] - c[PREV] - c[NIN]));
        for i in 1..16 {
            out.push(km * c[FIRST] * (c[IN + i] - c[PREV + i]));
        }
        out.push(km * (one - c[FIRST]) * (one - c[ALO]));

        // DIG: input structure, canonical 3-bit decomposition, target sum.
        let kd = c[K_DIG];
        for i in 0..PARAM_LEN {
            out.push(kd * (c[IN + i] - c[PARAM + i]));
        }
        out.push(kd * (c[IN + 5] - k(TAG_MESSAGE)));
        for i in 21..24 {
            out.push(p0 * kd * c[STATE + i]);
        }
        let (lt10, row9, row10) = (p[PR_LT10], p[PR_ROW9], p[PR_ROW10]);
        // The decomposition serves `SEL` too, and range checks in `PHDR`
        // and `BAL` (their lanes bound below, not to a hash output).
        let kdig = kd + c[K_SEL];
        let kdec = kdig + c[K_PHDR] + c[K_BAL] + c[K_RHDR];
        let eight = k(8);
        let eight_pow_9 = k(8u32.pow(9));
        let mut digit_sum = F::ZERO;
        for e in 0..LANES {
            let digit = c[B0 + e] + c[B1 + e] + c[B1 + e] + k(4) * c[B2 + e];
            out.push(kdec * lt10 * (c[REM + e] - digit - eight * n[REM + e]));
            for bit in [B0, B1, B2] {
                out.push(kdec * lt10 * c[bit + e] * (c[bit + e] - one));
            }
            let output = c[CARRY + e] + c[IN + e];
            out.push(kdig * p0 * (c[REM + e] - output));
            out.push(kdec * row10 * c[REM + e] * (c[REM + e] - one));
            out.push(c[H1 + e] - n[REM + e] * c[B0 + e] * c[B1 + e]);
            out.push(c[H2 + e] - c[H1 + e] * c[B2 + e]);
            // Canonical: a top bit of 1 with top digit 7 leaves no room
            // below P for any lower bits.
            out.push(kdec * row9 * c[H2 + e] * (output - eight_pow_9 * c[REM + e]));
            if e < 6 {
                digit_sum = digit_sum + digit;
            } else if e == 6 {
                digit_sum = digit_sum + p[PR_LMASK6] * digit;
            }
        }
        out.push(kd * lt10 * (n[DSUM] - c[DSUM] - digit_sum));
        out.push(kd * p0 * c[DSUM]);
        out.push(kd * row10 * (c[DSUM] - k(TARGET_SUM)));

        // SEL: compress(param, TAG_SELECT, message, randomizer).
        let ks = c[K_SEL];
        for i in 0..PARAM_LEN {
            out.push(ks * (c[IN + i] - c[PARAM + i]));
        }
        out.push(ks * (c[IN + 5] - k(TAG_SELECT)));
        for i in 21..24 {
            out.push(p0 * ks * c[STATE + i]);
        }

        // TLEAF: the text block's leaf, `scripture::leaf`.
        let ktl = c[K_TLEAF];
        for i in crate::scripture::BLOCK_ELEMENTS..16 {
            out.push(ktl * c[IN + i]);
        }
        out.push(p0 * ktl * (c[STATE + 16] - k(crate::scripture::DOMAIN_TEXT_LEAF)));
        out.push(p0 * ktl * (c[STATE + 17] - k(crate::scripture::BLOCK_LEN as u32)));
        for i in 18..24 {
            out.push(p0 * ktl * c[STATE + i]);
        }

        // TNODE: one level of the text path -- the hash from below (PREV)
        // on the side its bit (FLO) says, the level's capacity, and at the
        // top (LAST, level 15) the text's root.
        let ktn = c[K_TNODE];
        out.push(p0 * ktn * (c[STATE + 16] - k(crate::scripture::DOMAIN_TEXT_NODE) - c[C]));
        out.push(p0 * ktn * (c[STATE + 17] - k(16)));
        for i in 18..24 {
            out.push(p0 * ktn * c[STATE + i]);
        }
        for i in 0..8 {
            let left = c[IN + i] - c[PREV + i];
            let right = c[IN + 8 + i] - c[PREV + i];
            out.push(ktn * ((one - c[FLO]) * left + c[FLO] * right));
        }
        let top = k(TEXT_LEVELS - 1);
        out.push(ktn * c[LAST] * (c[C] - top));
        out.push(ktn * (one - c[LAST]) * (one - (c[C] - top) * c[W]));
        let root = crate::scripture::text_root();
        for i in 0..8 {
            out.push(ktn * c[LAST] * (c[CARRY + i] - F::from_base(root[i])));
        }

        // BIND: compress(TAG_BIND, message, block).
        let kbind = c[K_BIND];
        out.push(kbind * (c[IN] - k(TAG_BIND)));
        for i in 20..24 {
            out.push(p0 * kbind * c[STATE + i]);
        }

        // PHDR: a branch leaf's first block, absorbing its header `[k, n,
        // after_height, after_age, has_hash, 0, 0, 0, hash lock]`. Its
        // first five are the section's parameter; the sponge's length is
        // the header and n key hashes.
        out.push(kph * (c[FIRST] - one));
        out.push(kph * (c[PREV + 17] - k(16) - k(8) * c[IN + 1]));
        for i in 0..PARAM_LEN {
            out.push(kph * (c[PARAM + i] - c[IN + i]));
        }
        out.push(kph * c[IN + 4] * (c[IN + 4] - one));
        // REBIND (`IN[5]`, the section's `RB`) with its state (`IN[6]`), or
        // neither.
        out.push(kph * c[IN + 5] * (c[IN + 5] - one));
        out.push(kph * (c[RB] - c[IN + 5]));
        out.push(kph * (one - c[IN + 5]) * c[IN + 6]);
        out.push(kph * c[IN + 7]);
        for i in 8..16 {
            out.push(kph * (one - c[IN + 4]) * c[IN + i]);
        }
        for col in [C, S, FLO, FHI, RLO, ALO, LAST] {
            out.push(kph * c[col]);
        }
        out.push(px * kph * (n[K_PKEY] - one));
        // Its locks and bounds, as 30-bit numbers in the digit lanes (top
        // bit zero): the heights, ages and states below 2^30 make each
        // difference's sign certain. (The creation height is: the wrap
        // ties it to the spent leaf, whose block proved its height below
        // 2^30, `BAL`.) A REBIND input's declared state (`KIDX`, from its
        // message, `RHDR`) is above the branch's.
        let height_bound = [
            c[HEIGHT] - c[IN + 2],                       // height >= after_height
            c[HEIGHT] - c[CREATED],                      // height >= created
            c[HEIGHT] - c[CREATED] - c[IN + 3],          // height >= created + after_age
            c[IN + 2],
            c[IN + 3],
            c[IN + 6],
            c[IN] - one,                                 // k >= 1
            c[IN + 5] * (c[KIDX] - c[IN + 6] - one),     // declared > state
        ];
        for (e, value) in height_bound.into_iter().enumerate() {
            out.push(kph * p0 * (c[REM + e] - value));
            out.push(kph * p[PR_ROW10] * c[REM + e]);
        }

        // PKEY: the branch's key hashes, two per block, block `C` holding
        // keys `2C - 2` and `2C - 1`; `FLO`/`FHI` say which signed (each
        // received from its signer). `S` counts the signers so far: `k` by
        // the last block, which holds key `n - 1` (and, `RLO`, nothing else
        // if `n` is odd). With `ALO` there's a path to the root after it.
        out.push(kpk * c[FIRST]);
        out.push(px * n[K_PKEY] * (kph + kpk - one));
        out.push(px * n[K_PKEY] * (n[C] - c[C] - one));
        out.push(px * n[K_PKEY] * (n[S] - c[S] - c[FLO] - c[FHI]));
        out.push(px * kpk * (one - c[LAST]) * (n[K_PKEY] - one));
        out.push(kpk * c[LAST] * (c[S] + c[FLO] + c[FHI] - c[PARAM]));
        out.push(kpk * c[LAST] * (c[PARAM + 1] - c[C] - c[C] + c[RLO]));
        out.push(kpk * (one - c[LAST]) * c[RLO]);
        out.push(kpk * c[RLO] * c[FHI]);
        for i in 0..8 {
            out.push(kpk * c[RLO] * (c[IN + 8 + i] - c[PREV + 8 + i]));
        }
        out.push(px * kpk * c[LAST] * (one - c[ALO]) * (n[K_CIN] - one));

        // HLOCK: `H(DOMAIN_HASHLOCK, preimage)`, its image sent to the
        // branch's header.
        for i in 8..16 {
            out.push(khl * c[IN + i]);
        }
        out.push(p0 * khl * (c[STATE + 16] - k(DOMAIN_HASHLOCK)));
        out.push(p0 * khl * (c[STATE + 17] - k(8)));
        for i in 18..24 {
            out.push(p0 * khl * c[STATE + i]);
        }

        // PNODE: one level of a policy's path -- as `TNODE`, without a
        // fixed depth; the top (`LAST`) is the policy's root, the input
        // commitment's lock.
        out.push(p0 * kpn * (c[STATE + 16] - k(DOMAIN_POLICY_NODE) - c[C]));
        out.push(p0 * kpn * (c[STATE + 17] - k(16)));
        for i in 18..24 {
            out.push(p0 * kpn * c[STATE + i]);
        }
        for i in 0..8 {
            let left = c[IN + i] - c[PREV + i];
            let right = c[IN + 8 + i] - c[PREV + i];
            out.push(kpn * ((one - c[FLO]) * left + c[FLO] * right));
        }
        out.push(px * kpn * c[LAST] * (n[K_CIN] - one));

        // KNODE: one level of a key tree's path, as `PNODE`; the top
        // (`LAST`) is the key's id -- sent to its branch (`ALO`) or the
        // input commitment's lock.
        out.push(p0 * kkn * (c[STATE + 16] - k(DOMAIN_KEY_NODE) - c[C]));
        out.push(p0 * kkn * (c[STATE + 17] - k(16)));
        for i in 18..24 {
            out.push(p0 * kkn * c[STATE + i]);
        }
        for i in 0..8 {
            let left = c[IN + i] - c[PREV + i];
            let right = c[IN + 8 + i] - c[PREV + i];
            out.push(kkn * ((one - c[FLO]) * left + c[FLO] * right));
        }
        out.push(px * kkn * c[LAST] * (one - c[ALO]) * (n[K_CIN] - one));
        out.push(kkn * c[LAST] * (one - c[ALO]) * c[RB]);

        // RHDR: a REBIND message's first block, absorbing `[m, state]`
        // (`m >= 1` outputs named, each in an `RITEM` after it; `NIN` holds
        // `m` throughout); the state sent to its branch's header, and
        // range-checked with `m - 1`. The last `RITEM` sends the message to
        // the branch's signers, twice each (`SEL` and `BIND`).
        out.push(krh * (c[FIRST] - one));
        out.push(krh * (c[PREV + 17] - k(16) - k(16) * c[IN]));
        for i in 2..16 {
            out.push(krh * c[IN + i]);
        }
        out.push(krh * (c[NIN] - c[IN]));
        out.push(krh * c[C]);
        out.push(krh * c[LAST]);
        out.push(px * krh * (n[K_RITEM] - one));
        for e in 0..LANES {
            let value = match e {
                0 => c[IN + 1],
                1 => c[IN] - one,
                _ => F::ZERO,
            };
            out.push(krh * p0 * (c[REM + e] - value));
            out.push(krh * p[PR_ROW10] * c[REM + e]);
        }
        out.push(kri * c[FIRST]);
        out.push(px * n[K_RITEM] * (krh + kri - one));
        out.push(px * n[K_RITEM] * (n[C] - c[C] - one));
        out.push(px * n[K_RITEM] * (n[NIN] - c[NIN]));
        out.push(px * kri * (one - c[LAST]) * (n[K_RITEM] - one));
        out.push(kri * c[LAST] * (c[C] - c[NIN]));

        // CIN / COUT: input structure and 16-bit limbs.
        let commit = c[K_CIN] + c[K_COUT];
        for i in 12..16 {
            out.push(commit * c[IN + i]);
        }
        out.push(p0 * commit * (c[STATE + 16] - k(DOMAIN_COMMITMENT)));
        out.push(p0 * commit * (c[STATE + 17] - k(COMMITMENT_LEN)));
        for i in 18..24 {
            out.push(p0 * commit * c[STATE + i]);
        }
        for j in 0..AMOUNT_LIMBS {
            out.push(commit * (c[LIMB + j] - c[IN + 8 + j]));
            out.push(commit * p[PR_LT16] * c[BIT + j] * (c[BIT + j] - one));
            out.push(commit * p[PR_LT16] * (n[LACC + j] - c[LACC + j] - p[PR_POW2] * c[BIT + j]));
            out.push(commit * p0 * c[LACC + j]);
            out.push(commit * p[PR_ROW16] * (c[LACC + j] - c[LIMB + j]));
        }

        // The running total: at a commitment's row 0, add (input) or
        // subtract (output) its limbs with carries, leaving every limb in
        // 16 bits (checked over rows 0-15, against row 16's updated value)
        // and the overflow in the top limb.
        let base = k(1 << 16);
        let sign = c[K_CIN] - c[K_COUT];
        for j in 0..AMOUNT_LIMBS {
            let carry_in = if j == 0 { F::ZERO } else { c[carry_column(j - 1)] };
            let delta = sign * c[LIMB + j] + commit * (carry_in - base * c[carry_column(j)]);
            out.push(n[ACC + j] - c[ACC + j] - p0 * delta);
            out.push(commit * p[PR_LT16] * c[BIT2 + j] * (c[BIT2 + j] - one));
            out.push(commit * p[PR_LT16] * (n[LACC2 + j] - c[LACC2 + j] - p[PR_POW2] * c[BIT2 + j]));
            out.push(commit * p0 * c[LACC2 + j]);
            out.push(commit * p[PR_ROW16] * (c[LACC2 + j] - c[ACC + j]));
        }
        out.push(n[ACC_TOP] - c[ACC_TOP] - p0 * commit * c[carry_column(3)]);
        let kb = c[K_BAL];
        for j in 0..AMOUNT_LIMBS {
            let carry = c[carry_column(j)];
            out.push((commit + kb) * carry * (carry - one) * (carry + one));
        }

        // The final balance: the running total plus `a` minus `b` (row 0's
        // LIMB and LACC, both otherwise unused here), carried limb by
        // limb, must come out to exactly zero.
        for j in 0..AMOUNT_LIMBS {
            let carry_in = if j == 0 { F::ZERO } else { c[carry_column(j - 1)] };
            out.push(kb * p0 * (c[ACC + j] + c[LIMB + j] - c[LACC + j] + carry_in - base * c[carry_column(j)]));
        }
        out.push(kb * (c[ACC_TOP] + c[carry_column(3)]));
        // The height, below 2^30 (lane 0; the others zero).
        for e in 0..LANES {
            let value = if e == 0 { c[HEIGHT] } else { F::ZERO };
            out.push(kb * p0 * (c[REM + e] - value));
            out.push(kb * p[PR_ROW10] * c[REM + e]);
        }

        out
    }

    /// The bus interactions at one row, in slot order.
    fn interactions<F: Field>(&self, c: &[F], p: &[F]) -> Vec<Interaction<F>> {
        let one = F::ONE;
        let k = |v: u32| F::from_base(bb(v));
        let (p0, pout, lt10) = (p[PR_ROW0], p[PR_OUT], p[PR_LT10]);
        let tuple = |tag: u32, a: F, b: F, values: &[F]| -> Vec<F> {
            let mut t = vec![k(tag), a, b];
            t.extend_from_slice(values);
            t.resize(TUPLE_LEN, F::ZERO);
            t
        };
        let mix = |parts: &[(F, Vec<F>)]| -> Vec<F> {
            let mut t = vec![F::ZERO; TUPLE_LEN];
            for (gate, values) in parts {
                for (slot, &v) in t.iter_mut().zip(values) {
                    *slot = *slot + *gate * v;
                }
            }
            t
        };
        let range = |start: usize, len: usize| -> Vec<F> { (start..start + len).map(|i| c[i]).collect() };
        let absorbed = |half: usize| -> Vec<F> { (0..8).map(|i| c[IN + 8 * half + i] - c[PREV + 8 * half + i]).collect() };
        let carry8 = range(CARRY, 8);
        // An output's commitment and nonce, as sent together.
        let committed: Vec<F> = range(CARRY, 8).into_iter().chain(range(NONCE, 8)).collect();
        let item: Vec<F> = absorbed(0).into_iter().chain(absorbed(1)).collect();
        let compress_out: Vec<F> = (0..8).map(|i| c[CARRY + i] + c[IN + i]).collect();
        let (kc, kp, kd, kin, kout, km) = (c[K_CHAIN], c[K_PK], c[K_DIG], c[K_CIN], c[K_COUT], c[K_MSG]);
        let (ks, ktl, ktn, kbind) = (c[K_SEL], c[K_TLEAF], c[K_TNODE], c[K_BIND]);
        let (kph, kpk, khl, kpn, kkn, krh, kri) = (c[K_PHDR], c[K_PKEY], c[K_HLOCK], c[K_PNODE], c[K_KNODE], c[K_RHDR], c[K_RITEM]);
        // A policy key block's half: the key hash it absorbs, its
        // transaction and its branch's mode.
        let key_half = |half: usize| -> Vec<F> { absorbed(half).into_iter().chain([c[TX], c[RB]]).collect() };
        let keyed: Vec<F> = range(CARRY, 8).into_iter().chain([c[TX], c[RB]]).collect();
        // The message a signature section signs: its transaction's, or (in
        // REBIND mode) its branch's REBIND message.
        let msg_tuple = |values: &[F]| -> Vec<F> {
            let mut t = vec![k(TAG_MSG) + c[RB] * k(TAG_RMSG - TAG_MSG), c[TX] + c[RB] * (c[GROUP] - c[TX]), F::ZERO];
            t.extend_from_slice(values);
            t.resize(TUPLE_LEN, F::ZERO);
            t
        };
        // Row 0's state from element 14 on: the randomizer (DIG, SEL), or
        // the text block's tail (BIND).
        let state_at = |i: usize| if i < 16 { c[IN + i] } else { c[STATE + i] };
        let randomizer: Vec<F> = (14..21).map(state_at).collect();
        let bound_block: Vec<F> = (9..9 + crate::scripture::BLOCK_ELEMENTS).map(state_at).collect();
        let lt5 = p[PR_LT5];
        let three_rows = p[PR_DROW] + p[PR_DROW] + p[PR_DROW];
        let digit = |e: usize| c[B0 + e] + c[B1 + e] + c[B1 + e] + k(4) * c[B2 + e];
        let pk_half = |half: usize, flag: usize, chain: F| -> Vec<F> {
            let trivial = tuple(TAG_CH, c[UID], chain, &[k(CHAIN_STEPS)]);
            let top = tuple(TAG_TOP, c[UID], chain, &absorbed(half));
            mix(&[(c[flag], trivial), (one - c[flag], top)])
        };
        let two_c = c[C] + c[C];

        let mut slots = Vec::with_capacity(BUS.slots);
        // Slot 0.
        slots.push(Interaction {
            multiplicity: -(kc * p0 * c[START]) - kp * p0 * (one - c[FIRST]) - kd * p0
                - km * p0 * (one - c[FIRST]) * c[ALO]
                + (kin + kout) * pout
                - ks * p0
                + ktl * p0
                - ktn * p0
                - kbind * p0
                - kph * p0 * c[IN + 4]
                - kpk * p0 * c[FLO]
                + khl * pout
                - kpn * p0
                - kkn * p0
                + krh * p0
                - kri * p0,
            values: mix(&[
                (krh, tuple(TAG_RSTATE, c[UID], F::ZERO, &[c[IN + 1]])),
                (kri, tuple(TAG_RITEM, c[TX], F::ZERO, &item)),
                (kkn, tuple(TAG_KNODE, c[UID], c[C], &range(PREV, 8))),
                (kph, tuple(TAG_HASH, c[UID], F::ZERO, &range(IN + 8, 8))),
                (kpk, tuple(TAG_KEY, c[UID], two_c - k(2), &key_half(0))),
                (khl, tuple(TAG_HASH, c[UID], F::ZERO, &carry8)),
                (kpn, tuple(TAG_PNODE, c[UID], c[C], &range(PREV, 8))),
                (kc, tuple(TAG_CH, c[UID], c[C], &[c[S]])),
                (kp, pk_half(0, FLO, two_c - one)),
                (kd, tuple(TAG_BOUND, c[UID], F::ZERO, &range(IN + 6, 8))),
                (km, tuple(TAG_ITEM, c[TX], c[RLO], &item)),
                (kin, tuple(TAG_PIN, c[CREATED], F::ZERO, &carry8)),
                (kout, tuple(TAG_POUT, F::ZERO, F::ZERO, &committed)),
                (ks, msg_tuple(&range(IN + 6, 8))),
                (ktl, tuple(TAG_TEXT, c[UID], F::ZERO, &range(IN, crate::scripture::BLOCK_ELEMENTS))),
                (ktn, tuple(TAG_TNODE, c[UID], c[C], &range(PREV, 8))),
                (kbind, msg_tuple(&range(IN + 1, 8))),
            ]),
        });
        // Slot 1.
        slots.push(Interaction {
            multiplicity: kc * pout * c[END] - kp * p0 * (one - c[LAST]) + (kin + kout) * pout + kd * p0 - ks * p0 + ktl * pout
                - ktn * p0
                - kbind * p0
                - kpk * p0 * c[FHI]
                + kpn * pout * (one - c[LAST])
                + kkn * pout * (one - c[LAST])
                - kph * p0 * c[IN + 5]
                + kri * pout * c[LAST] * (c[PARAM] + c[PARAM]),
            values: mix(&[
                (kph, tuple(TAG_RSTATE, c[UID], F::ZERO, &[c[KIDX]])),
                (kri, tuple(TAG_RMSG, c[UID], F::ZERO, &carry8)),
                (kkn, tuple(TAG_KNODE, c[UID], c[C] + one, &carry8)),
                (kpk, tuple(TAG_KEY, c[UID], two_c - one, &key_half(1))),
                (kpn, tuple(TAG_PNODE, c[UID], c[C] + one, &carry8)),
                (kc, tuple(TAG_TOP, c[UID], c[C], &compress_out)),
                (kp, pk_half(1, FHI, two_c)),
                (kin, tuple(TAG_ITEM, c[TX], one, &carry8)),
                (kout, tuple(TAG_ITEM, c[TX], F::ZERO, &committed)),
                (kd, tuple(TAG_RAND, c[UID], F::ZERO, &randomizer)),
                (ks, tuple(TAG_RAND, c[UID], F::ZERO, &randomizer)),
                (ktl, tuple(TAG_TNODE, c[UID], F::ZERO, &carry8)),
                (ktn, tuple(TAG_IDX, c[UID], c[C], &[c[FLO]])),
                (kbind, tuple(TAG_TEXT, c[UID], F::ZERO, &bound_block)),
            ]),
        });
        // Slot 2: a message, once per input; or digit lane 0; or the
        // public amounts.
        let kb = c[K_BAL];
        let net: Vec<F> = range(LIMB, AMOUNT_LIMBS).into_iter().chain(range(LACC, AMOUNT_LIMBS)).collect();
        // (Twice per signature: SEL and BIND each receive it.)
        slots.push(Interaction {
            multiplicity: km * pout * c[LAST] * (c[NSIG] + c[NSIG]) + kd * lt10 + kb * p0
                + ktn * pout * (one - c[LAST])
                + kbind * pout
                + ks * (lt5 + p[PR_ROW5])
                + kp * pout * c[LAST] * c[ALO]
                + kkn * pout * c[LAST] * c[ALO]
                + kpk * pout * c[LAST] * c[ALO]
                + kout * pout * c[NAMED],
            values: mix(&[
                (kout, tuple(TAG_RITEM, c[TX], F::ZERO, &committed)),
                (kp, tuple(TAG_KEY, c[GROUP], c[KIDX], &keyed)),
                (kkn, tuple(TAG_KEY, c[GROUP], c[KIDX], &keyed)),
                (kpk, tuple(TAG_PNODE, c[UID], F::ZERO, &carry8)),
                (km, tuple(TAG_MSG, c[TX], F::ZERO, &carry8)),
                (kd, tuple(TAG_CH, c[UID], p[PR_DROW], &[digit(0)])),
                (kb, tuple(TAG_NET, c[HEIGHT], F::ZERO, &net)),
                (ktn, tuple(TAG_TNODE, c[UID], c[C] + one, &carry8)),
                (kbind, tuple(TAG_BOUND, c[UID], F::ZERO, &compress_out)),
                (ks, tuple(TAG_IDX, c[UID], three_rows, &[c[B0]])),
            ]),
        });
        // Slots 3-8: digit lanes 1-6.
        // (Slots 3-4 also carry SEL's position bits 1 and 2 of each row.)
        for e in 1..7 {
            let mask = if e < 6 { lt10 } else { p[PR_LMASK6] };
            let chain = k((DIGITS_PER_LANE * e) as u32) + p[PR_DROW];
            let mut parts = vec![(kd, tuple(TAG_CH, c[UID], chain, &[digit(e)]))];
            let mut multiplicity = kd * mask;
            if e == 1 {
                // (A key in a key tree: its hash, up the path.)
                parts.push((kp, tuple(TAG_KNODE, c[UID], F::ZERO, &carry8)));
                multiplicity = multiplicity + kp * pout * c[LAST] * c[RHI];
            }
            if e <= 2 {
                let bit = [B1, B2][e - 1];
                parts.push((ks, tuple(TAG_IDX, c[UID], three_rows + k(e as u32), &[c[bit]])));
                multiplicity = multiplicity + ks * lt5;
            }
            slots.push(Interaction {
                multiplicity,
                values: mix(&parts),
            });
        }
        slots
    }

    fn public_tuples(&self) -> Vec<(BabyBear, Vec<BabyBear>)> {
        let entry = |tag: u32, a: u32, commitment: &[BabyBear; 8], nonce: Option<&[BabyBear; 8]>| {
            let mut t = vec![bb(tag), bb(a), BabyBear::ZERO];
            t.extend_from_slice(commitment);
            t.extend_from_slice(nonce.unwrap_or(&[BabyBear::ZERO; 8]));
            (BabyBear::ONE, t)
        };
        let mut amounts = vec![bb(TAG_NET), bb(self.height), BabyBear::ZERO];
        amounts.extend(amount_limbs(self.net.0));
        amounts.extend(amount_limbs(self.net.1));
        let (in_slots, out_slots) = self.capacity.unwrap_or((self.inputs.len(), self.outputs.len()));
        let unused = |tag: u32| {
            let mut t = vec![bb(tag)];
            t.resize(TUPLE_LEN, BabyBear::ZERO);
            (BabyBear::ZERO, t)
        };
        std::iter::once((BabyBear::ONE, amounts))
            .chain(self.inputs.iter().zip(&self.input_heights).map(|(c, &h)| entry(TAG_PIN, h, c, None)))
            .chain((self.inputs.len()..in_slots).map(|_| unused(TAG_PIN)))
            .chain(self.outputs.iter().zip(&self.nonces).map(|(c, n)| entry(TAG_POUT, 0, c, Some(n))))
            .chain((self.outputs.len()..out_slots).map(|_| unused(TAG_POUT)))
            .collect()
    }
}

impl Air for BlockAir {
    fn width(&self) -> usize {
        WIDTH
    }

    fn trace_len(&self) -> usize {
        self.num_blocks * ROWS
    }

    fn constraint_degree(&self) -> usize {
        4
    }

    fn periodic_columns(&self) -> Vec<Vec<BabyBear>> {
        let mut columns = self.chip.periodic_columns();
        let column = |f: &dyn Fn(usize) -> u32| -> Vec<BabyBear> { (0..ROWS).map(|r| bb(f(r))).collect() };
        columns.push(column(&|r| (r == 0) as u32));
        columns.push(column(&|r| (r == OUT_ROW) as u32));
        columns.push(column(&|r| (r == ROWS - 1) as u32));
        columns.push(column(&|r| (r < ROWS - 1) as u32));
        columns.push(column(&|r| (r < 16) as u32));
        columns.push(column(&|r| (r == 16) as u32));
        columns.push(column(&|r| if r < 16 { 1 << r } else { 0 }));
        columns.push(column(&|r| (r < DIGITS_PER_LANE) as u32));
        columns.push(column(&|r| (r == 9) as u32));
        columns.push(column(&|r| (r == 10) as u32));
        columns.push(column(&|r| if r < DIGITS_PER_LANE { r as u32 } else { 0 }));
        columns.push(column(&|r| (r < V - 6 * DIGITS_PER_LANE) as u32));
        columns.push(column(&|r| (r < 5) as u32));
        columns.push(column(&|r| (r == 5) as u32));
        columns
    }

    fn num_transition_constraints(&self) -> usize {
        self.num_constraints
    }

    fn eval_transition<F: Field>(&self, current: &[F], next: &[F], periodic: &[F], out: &mut [F]) {
        out.copy_from_slice(&self.constraints(current, next, periodic));
    }

    fn boundaries(&self) -> Vec<Boundary> {
        let last = self.trace_len() - 1;
        let mut out = vec![
            Boundary { row: 0, column: K_PAD, value: BabyBear::ONE },
            Boundary { row: 0, column: UID, value: BabyBear::ZERO },
            Boundary { row: last, column: K_BAL, value: BabyBear::ONE },
        ];
        for column in (ACC..ACC + AMOUNT_LIMBS).chain([ACC_TOP]) {
            out.push(Boundary { row: 0, column, value: BabyBear::ZERO });
        }
        out
    }

    fn num_aux_columns(&self) -> usize {
        BUS.num_aux_columns()
    }

    fn num_challenges(&self) -> usize {
        bus::NUM_CHALLENGES
    }

    fn aux_trace(&self, main: &[Vec<BabyBear>], challenges: &[Ext]) -> Vec<Vec<Ext>> {
        let periodic = self.periodic_columns();
        BUS.aux_trace(
            self.trace_len(),
            |i| {
                let row: Vec<BabyBear> = main.iter().map(|col| col[i]).collect();
                let p: Vec<BabyBear> = periodic.iter().map(|col| col[i % ROWS]).collect();
                self.interactions(&row, &p)
            },
            challenges,
        )
    }

    fn num_aux_constraints(&self) -> usize {
        BUS.num_constraints()
    }

    fn eval_aux_transition<F: Field>(&self, frame: &AuxFrame<F>, out: &mut [F]) {
        let interactions = self.interactions(frame.main_current, frame.periodic);
        BUS.eval(&interactions, frame, out);
    }

    fn aux_boundaries(&self, challenges: &[Ext]) -> Vec<AuxBoundary> {
        BUS.boundaries(self.trace_len(), BUS.public_sum(&self.public_tuples(), challenges))
    }

    fn statement(&self) -> Vec<BabyBear> {
        use crate::recursion::RecursiveAir;
        crate::recursion::recursive_statement(&self.statement_header(), &self.public_tuples())
    }
}

// ---- Witness ------------------------------------------------------------

/// One block of the trace, before its rows are generated: its kind, its
/// header values, and its row-0 state.
#[derive(Clone)]
struct Spec {
    kind: usize,
    header: Vec<(usize, BabyBear)>,
    state: [BabyBear; 24],
    prev: [BabyBear; 24],
    limbs: [BabyBear; AMOUNT_LIMBS],
    carries: [i64; AMOUNT_LIMBS],
    nonce: [BabyBear; 8],
    /// Values to decompose in the digit lanes, for a range check (`PHDR`,
    /// `BAL`); `DIG` and `SEL` decompose their hash outputs.
    lanes: Option<[u32; LANES]>,
}

impl Spec {
    fn new(kind: usize, state: [BabyBear; 24]) -> Self {
        Spec {
            kind,
            header: Vec::new(),
            state,
            prev: [BabyBear::ZERO; 24],
            limbs: [BabyBear::ZERO; AMOUNT_LIMBS],
            carries: [0; AMOUNT_LIMBS],
            nonce: [BabyBear::ZERO; 8],
            lanes: None,
        }
    }

    fn set(mut self, column: usize, value: BabyBear) -> Self {
        self.header.push((column, value));
        self
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum WitnessError {
    /// A transaction's own signatures don't check out.
    InvalidTransaction(usize),
    /// The block doesn't balance against the reward.
    Unbalanced,
    /// More than the circuit can hold.
    TooLarge,
    /// A transaction's policy input's timelocks don't hold at this height.
    LockNotMet(usize),
}

/// The block's height, and the creation height of each output its
/// transactions spend (by commitment): what a chunk's statement publishes,
/// and policy inputs' timelocks are checked against.
#[derive(Clone, Debug, Default)]
pub struct Heights {
    pub block: u32,
    pub created: std::collections::HashMap<[u8; 32], u32>,
}

impl Heights {
    fn created(&self, commitment: &[u8; 32]) -> u32 {
        self.created.get(commitment).copied().unwrap_or(0)
    }
}

/// A block's trace, and the statement it proves.
pub struct Witness {
    pub air: BlockAir,
    pub trace: Vec<Vec<BabyBear>>,
}

fn iv(domain: u32, len: u32) -> [BabyBear; 24] {
    let mut s = [BabyBear::ZERO; 24];
    s[16] = bb(domain);
    s[17] = bb(len);
    s
}

/// Lay out `transactions` (each already signed) and the block reward as
/// a trace, along with the public statement it proves: the sorted input
/// and output commitment lists a `BlockBody` built from the same
/// transactions would publish.
pub fn build(transactions: &[Transaction], reward: u64) -> Result<Witness, WitnessError> {
    build_inner(transactions, (reward, 0), true)
}

/// Lay out a chunk of a block's transactions, proving
/// `sum(inputs) + a == sum(outputs) + b` for `net = (a, b)`, in a block at
/// `heights`.
pub fn build_chunk(transactions: &[Transaction], net: (u64, u64), shape: ChunkShape, heights: &Heights) -> Result<Witness, WitnessError> {
    build_shaped(transactions, net, Some(shape), true, heights)
}

/// `build`, optionally skipping the native signature check -- so tests can
/// play a miner laying out a transaction whose signatures *don't* cover
/// it, and confirm the circuit itself refuses.
// Indexing several parallel arrays (digits, signature values, tops) by
// chain is clearer than zipping them.
#[allow(clippy::needless_range_loop)]
fn build_inner(transactions: &[Transaction], net: (u64, u64), check_signatures: bool) -> Result<Witness, WitnessError> {
    build_shaped(transactions, net, None, check_signatures, &Heights::default())
}

fn build_shaped(
    transactions: &[Transaction],
    net: (u64, u64),
    shape: Option<ChunkShape>,
    check_signatures: bool,
    heights: &Heights,
) -> Result<Witness, WitnessError> {
    let perm = crate::poseidon2::perm24();
    let mut specs = vec![Spec::new(K_PAD, [BabyBear::ZERO; 24])];
    let mut public_inputs = Vec::new();
    let mut public_outputs = Vec::new();
    let mut total = RunningTotal::default();
    let mut uid = 0u32;

    for (t, tx) in transactions.iter().enumerate() {
        if check_signatures && !tx.verify() {
            return Err(WitnessError::InvalidTransaction(t));
        }
        let tx_id = bb(t as u32);
        let message = tx.signing_message();
        // Each signed item: a commitment, the rest of its block (an
        // output's nonce; zeros for an input), and whether it's an input.
        let mut items: Vec<([BabyBear; 8], [BabyBear; 8], bool)> = Vec::new();

        for input in &tx.inputs {
            let commitment_bytes = input.commitment();
            let created = heights.created(&commitment_bytes);
            // What its signatures sign: the transaction, or its REBIND
            // message.
            let message = tx.message_for(input).ok_or(WitnessError::InvalidTransaction(t))?;
            let lock = match &input.spend {
                Spend::Key { pubkey, proof, signature } => {
                    uid += 1;
                    let signature = signature.as_ref().expect("verified transactions are signed");
                    signature_section(&mut specs, uid, tx_id, message, pubkey, proof, signature, check_signatures, bb(created), None)
                }
                Spend::Policy(p) => {
                    if check_signatures && !p.branch.locks_hold(heights.block, created) {
                        return Err(WitnessError::LockNotMet(t));
                    }
                    let section = uid + p.signers.len() as u32 + 1;
                    for signer in &p.signers {
                        uid += 1;
                        let signature = signer.signature.as_ref().expect("verified transactions are signed");
                        let signer_of = Some((section, signer.index, p.branch.rebind.is_some()));
                        signature_section(&mut specs, uid, tx_id, message, &signer.pubkey, &signer.proof, signature, check_signatures, bb(created), signer_of);
                    }
                    uid += 1;
                    let signed: Vec<u8> = p.signers.iter().map(|s| s.index).collect();
                    let path: Vec<[BabyBear; 8]> = p.path.iter().map(digest_from_bytes).collect();
                    policy_section(&mut specs, tx_id, &p.branch, p.index, &path, &signed, heights, created, p.state)
                }
            };
            debug_assert_eq!(lock, digest_from_bytes(&input.lock()));

            // Input commitment.
            let commitment = commit_spec(&mut specs, K_CIN, lock, input.amount, tx_id, perm);
            specs.last_mut().unwrap().carries = total.add(input.amount, 1);
            public_inputs.push((commitment, created));
            items.push((commitment, [BabyBear::ZERO; 8], true));
            // A hash lock, after it: in the branch's section, sending its
            // image to the header.
            if let Spend::Policy(p) = &input.spend
                && let Some(preimage) = &p.preimage
            {
                let mut state = iv(DOMAIN_HASHLOCK, 8);
                state[..8].copy_from_slice(&digest_from_bytes(preimage));
                specs.push(Spec::new(K_HLOCK, state).set(TX, tx_id));
            }
            // A REBIND message, after it too: its signers' message.
            if let Spend::Policy(p) = &input.spend
                && p.branch.rebind.is_some()
            {
                let named: Vec<([BabyBear; 8], [BabyBear; 8])> = p
                    .named
                    .iter()
                    .map(|c| {
                        let nonce = tx.outputs.iter().find(|o| &o.commitment() == c).map_or([0; crate::recovery::NONCE_LEN], |o| o.nonce);
                        (digest_from_bytes(c), crate::output::nonce_limbs(&nonce))
                    })
                    .collect();
                let m = named.len();
                let mut sponge = iv(DOMAIN_REBIND, 16 * (1 + m) as u32);
                let prev = sponge;
                sponge[0] = sponge[0] + bb(m as u32);
                sponge[1] = sponge[1] + bb(p.state);
                let mut spec = Spec::new(K_RHDR, sponge).set(TX, tx_id).set(FIRST, BabyBear::ONE).set(NIN, bb(m as u32));
                spec.prev = prev;
                spec.lanes = Some([p.state, (bb(m as u32) - BabyBear::ONE).value(), 0, 0, 0, 0, 0, 0]);
                specs.push(spec);
                sponge = perm.permute(sponge);
                for (b, (commitment, nonce)) in named.iter().enumerate() {
                    let prev = sponge;
                    for i in 0..8 {
                        sponge[i] = sponge[i] + commitment[i];
                        sponge[8 + i] = sponge[8 + i] + nonce[i];
                    }
                    let mut spec = Spec::new(K_RITEM, sponge)
                        .set(TX, tx_id)
                        .set(C, bb(b as u32 + 1))
                        .set(NIN, bb(m as u32))
                        .set(LAST, bb((b + 1 == m) as u32));
                    spec.prev = prev;
                    specs.push(spec);
                    sponge = perm.permute(sponge);
                }
                debug_assert_eq!(sponge[..8], message[..]);
            }
        }

        for output in &tx.outputs {
            let pkh = digest_from_bytes(&output.lock);
            let commitment = commit_spec(&mut specs, K_COUT, pkh, output.amount, tx_id, perm);
            let nonce = crate::output::nonce_limbs(&output.nonce);
            let commitment_bytes = output.commitment();
            let named = tx.inputs.iter().filter(|i| matches!(&i.spend, Spend::Policy(p) if p.branch.rebind.is_some() && p.named.contains(&commitment_bytes))).count();
            let spec = specs.last_mut().unwrap();
            spec.header.push((NAMED, bb(named as u32)));
            spec.carries = total.add(output.amount, -1);
            spec.nonce = nonce;
            public_outputs.push((commitment, nonce));
            items.push((commitment, nonce, false));
        }

        // Signing message: the input count, then one item per block.
        let n_in = bb(tx.inputs.len() as u32);
        let num_blocks = 1 + items.len();
        let mut sponge = iv(DOMAIN_SIGNING, 16 * num_blocks as u32);
        for b in 0..num_blocks {
            let prev = sponge;
            let item = b.checked_sub(1).map(|i| items[i]);
            match item {
                None => sponge[0] = sponge[0] + n_in,
                Some((commitment, rest, _)) => {
                    for i in 0..8 {
                        sponge[i] = sponge[i] + commitment[i];
                        sponge[8 + i] = sponge[8 + i] + rest[i];
                    }
                }
            }
            let mut spec = Spec::new(K_MSG, sponge)
                .set(TX, tx_id)
                .set(NIN, n_in)
                .set(NSIG, bb(tx.all_signature_count() as u32))
                .set(FIRST, bb((b == 0) as u32))
                .set(LAST, bb((b == num_blocks - 1) as u32))
                .set(RLO, bb(item.is_some_and(|(_, _, is_input)| is_input) as u32))
                .set(ALO, bb(item.is_some() as u32));
            spec.prev = prev;
            specs.push(spec);
            sponge = perm.permute(sponge);
        }
        debug_assert_eq!(sponge[..8], message[..]);
    }

    // Balance: the running total plus a minus b must carry out to
    // exactly zero.
    let carries = total.finish(net).ok_or(WitnessError::Unbalanced)?;

    let mut num_blocks = (specs.len() + 1).next_power_of_two().max(2);
    if let Some(shape) = shape {
        if num_blocks > shape.num_blocks {
            return Err(WitnessError::TooLarge);
        }
        num_blocks = shape.num_blocks;
    }
    if num_blocks * ROWS > 1 << max_log_rows(&crate::prover::PARAMS) {
        return Err(WitnessError::TooLarge);
    }
    while specs.len() < num_blocks - 1 {
        specs.push(Spec::new(K_PAD, [BabyBear::ZERO; 24]));
    }
    let mut bal = Spec::new(K_BAL, [BabyBear::ZERO; 24]);
    bal.carries = carries;
    bal.limbs = amount_limbs(net.0);
    bal.lanes = Some([heights.block, 0, 0, 0, 0, 0, 0, 0]);
    specs.push(bal);

    // The same order a `BlockBody` publishes them in.
    public_inputs.sort_by_key(|(c, _)| digest_to_bytes(*c));
    public_outputs.sort_by_key(|(c, _)| digest_to_bytes(*c));
    if let Some(shape) = shape
        && (public_inputs.len() > shape.inputs || public_outputs.len() > shape.outputs)
    {
        return Err(WitnessError::TooLarge);
    }
    let capacity = shape.map(|s| (s.inputs, s.outputs));
    let (public_outputs, public_nonces) = public_outputs.into_iter().unzip();
    let (public_inputs, input_heights) = public_inputs.into_iter().unzip();
    let air = BlockAir::chunk(num_blocks, public_inputs, public_outputs, public_nonces, net, capacity).with_heights(heights.block, input_heights);
    let mut trace = fill(&air, &specs);
    let bal_row = (num_blocks - 1) * ROWS;
    for (j, limb) in amount_limbs(net.1).into_iter().enumerate() {
        trace[LACC + j][bal_row] = limb;
    }
    Ok(Witness { air, trace })
}

/// A small signed integer as a field element (negative values wrap to
/// `p - |v|`).
fn from_signed(v: i64) -> BabyBear {
    let p = crate::poseidon2::P as i64;
    BabyBear::new(v.rem_euclid(p) as u32)
}

/// The circuit's running total, natively: inputs minus outputs as four
/// 16-bit limbs (each always in range) and a signed top limb -- what the
/// `ACC` columns hold.
#[derive(Default)]
struct RunningTotal {
    limbs: [i64; AMOUNT_LIMBS],
    top: i64,
}

impl RunningTotal {
    /// Add `sign * amount`, renormalizing; returns the carries out of each
    /// limb (each -1, 0, or 1).
    fn add(&mut self, amount: u64, sign: i64) -> [i64; AMOUNT_LIMBS] {
        let mut carries = [0; AMOUNT_LIMBS];
        let mut carry = 0;
        for (j, limb) in amount_limbs(amount).iter().enumerate() {
            let value = self.limbs[j] + sign * limb.value() as i64 + carry;
            carry = value.div_euclid(1 << 16);
            self.limbs[j] = value.rem_euclid(1 << 16);
            carries[j] = carry;
        }
        self.top += carry;
        carries
    }

    /// The final check's carries: adding `a` and taking `b` must bring
    /// the total to exactly zero, or `None`.
    fn finish(&self, (a, b): (u64, u64)) -> Option<[i64; AMOUNT_LIMBS]> {
        let mut carries = [0; AMOUNT_LIMBS];
        let mut carry = 0;
        for (j, (x, y)) in amount_limbs(a).iter().zip(amount_limbs(b)).enumerate() {
            let value = self.limbs[j] + x.value() as i64 - y.value() as i64 + carry;
            if value.rem_euclid(1 << 16) != 0 {
                return None;
            }
            carry = value.div_euclid(1 << 16);
            carries[j] = carry;
        }
        (self.top + carry == 0).then_some(carries)
    }
}

/// One signature's section: its digits, the Bible passage it binds, its
/// chains, its key hash, and -- for a key in a key tree (`proof`) -- the
/// path to the tree's root, the key's id. A plain input's commitment
/// follows it; a policy signer's (`signer`: its branch's section, key
/// index, and whether it signs REBIND) sends the key's id to the branch
/// instead. Returns the key's id.
#[allow(clippy::too_many_arguments, clippy::needless_range_loop)]
fn signature_section(
    specs: &mut Vec<Spec>,
    uid: u32,
    tx_id: BabyBear,
    message: [BabyBear; 8],
    pk: &wots::PublicKey,
    proof: &crate::keytree::KeyProof,
    signature: &wots::Signature,
    check_signatures: bool,
    created: BabyBear,
    signer: Option<(u32, u8, bool)>,
) -> [BabyBear; 8] {
    let perm = crate::poseidon2::perm24();
    let param = pk.param;
    let (group, rebind) = signer.map_or((0, false), |(section, _, rebind)| (section, rebind));
    // A miner forging a spend would at least pick a randomizer whose
    // digits hit the target sum (a few dozen tries) -- so the unchecked
    // path does too, leaving the chains themselves as the only thing that
    // can give the forgery away.
    let randomizer = if check_signatures {
        signature.randomizer
    } else {
        (0u32..)
            .map(|trial| {
                let mut r = signature.randomizer;
                r[1] = r[1] + bb(trial);
                r
            })
            .find(|&r| wots::derive_digits(&param, wots::signed_digest(&param, message, r), r).iter().sum::<u32>() == TARGET_SUM)
            .unwrap()
    };
    // The text block the signature binds.
    let position = wots::select(&param, message, randomizer);
    let text = crate::scripture::block_elements(position % crate::scripture::BLOCKS);
    let bound = wots::bind(message, position);
    let digits = wots::derive_digits(&param, bound, randomizer);
    let param_header = |spec: Spec| -> Spec { (0..PARAM_LEN).fold(spec, |s, i| s.set(PARAM + i, param[i])) };

    // Digit derivation.
    let mut state = [BabyBear::ZERO; 24];
    state[..PARAM_LEN].copy_from_slice(&param);
    state[5] = bb(TAG_MESSAGE);
    state[6..14].copy_from_slice(&bound);
    state[14..21].copy_from_slice(&randomizer);
    specs.push(
        param_header(Spec::new(K_DIG, state))
            .set(UID, bb(uid))
            .set(TX, tx_id)
            .set(CREATED, created)
            .set(GROUP, bb(group))
            .set(RB, bb(rebind as u32)),
    );

    // The text block: selected, proven in the text tree, bound.
    let mut state = [BabyBear::ZERO; 24];
    state[..PARAM_LEN].copy_from_slice(&param);
    state[5] = bb(TAG_SELECT);
    state[6..14].copy_from_slice(&message);
    state[14..21].copy_from_slice(&randomizer);
    specs.push(param_header(Spec::new(K_SEL, state)).set(UID, bb(uid)).set(TX, tx_id));
    let mut state = iv(crate::scripture::DOMAIN_TEXT_LEAF, crate::scripture::BLOCK_LEN as u32);
    state[..text.len()].copy_from_slice(&text);
    specs.push(param_header(Spec::new(K_TLEAF, state)).set(UID, bb(uid)));
    let mut hash: [BabyBear; 8] = perm.permute(state)[..8].try_into().unwrap();
    for (level, sibling) in crate::scripture::tree().path(position).into_iter().enumerate() {
        let bit = (position >> level) & 1;
        let mut state = iv(crate::scripture::DOMAIN_TEXT_NODE + level as u32, 16);
        let (left, right) = if bit == 1 { (sibling, hash) } else { (hash, sibling) };
        state[..8].copy_from_slice(&left);
        state[8..16].copy_from_slice(&right);
        let last = level as u32 == TEXT_LEVELS - 1;
        let gap = bb(level as u32) - bb(TEXT_LEVELS - 1);
        let mut spec = param_header(Spec::new(K_TNODE, state))
            .set(UID, bb(uid))
            .set(C, bb(level as u32))
            .set(FLO, bb(bit as u32))
            .set(LAST, bb(last as u32))
            .set(W, if last { BabyBear::ZERO } else { gap.inverse() });
        spec.prev[..8].copy_from_slice(&hash);
        specs.push(spec);
        hash = perm.permute(state)[..8].try_into().unwrap();
    }
    debug_assert_eq!(hash, crate::scripture::text_root());
    let mut state = [BabyBear::ZERO; 24];
    state[0] = bb(TAG_BIND);
    state[1..9].copy_from_slice(&message);
    state[9..9 + text.len()].copy_from_slice(&text);
    specs.push(param_header(Spec::new(K_BIND, state)).set(UID, bb(uid)).set(TX, tx_id));

    // Chains.
    for c in 0..V {
        let mut value = signature.values[c];
        for s in digits[c]..CHAIN_STEPS {
            let mut state = [BabyBear::ZERO; 24];
            state[..PARAM_LEN].copy_from_slice(&param);
            state[5] = bb(TAG_CHAIN);
            state[6] = bb(c as u32);
            state[7] = bb(s);
            state[8..16].copy_from_slice(&value);
            let last = s == CHAIN_STEPS - 1;
            let gap = bb(s) - bb(CHAIN_STEPS - 1);
            specs.push(
                param_header(Spec::new(K_CHAIN, state))
                    .set(UID, bb(uid))
                    .set(TX, tx_id)
                    .set(C, bb(c as u32))
                    .set(S, bb(s))
                    .set(START, bb((s == digits[c]) as u32))
                    .set(END, bb(last as u32))
                    .set(W, if last { BabyBear::ZERO } else { gap.inverse() }),
            );
            value = wots::chain_step(perm, &param, c, s, value);
        }
        debug_assert!(!check_signatures || value == pk.tops[c]);
    }

    // Public-key hash.
    let input_elements = pk.hash_input();
    let mut sponge = iv(DOMAIN_PUBKEY, PK_HASH_LEN);
    for b in 0..PK_BLOCKS {
        let prev = sponge;
        for (i, slot) in sponge.iter_mut().take(16).enumerate() {
            if let Some(&e) = input_elements.get(16 * b + i) {
                *slot = *slot + e;
            }
        }
        let trivial = |chain: usize| bb((chain < V && digits[chain] == CHAIN_STEPS) as u32);
        let last = b == PK_BLOCKS - 1;
        let gap = bb(b as u32) - bb(PK_BLOCKS as u32 - 1);
        let mut spec = param_header(Spec::new(K_PK, sponge))
            .set(UID, bb(uid))
            .set(TX, tx_id)
            .set(C, bb(b as u32))
            .set(FIRST, bb((b == 0) as u32))
            .set(LAST, bb(last as u32))
            .set(W, if last { BabyBear::ZERO } else { gap.inverse() })
            .set(FLO, if b == 0 { BabyBear::ZERO } else { trivial(2 * b - 1) })
            .set(FHI, trivial(2 * b));
        let to_branch = |spec: Spec| match signer {
            Some((_, index, _)) => spec.set(ALO, BabyBear::ONE).set(KIDX, bb(index as u32)),
            None => spec,
        };
        if last {
            spec = if proof.path.is_empty() { to_branch(spec) } else { spec.set(RHI, BabyBear::ONE) };
        }
        spec.prev = prev;
        specs.push(spec);
        sponge = perm.permute(sponge);
    }
    let mut hash: [BabyBear; 8] = sponge[..8].try_into().unwrap();
    debug_assert_eq!(hash, pk.hash());

    // The key tree's path.
    for (level, sibling) in proof.path.iter().enumerate() {
        let sibling = digest_from_bytes(sibling);
        let bit = (proof.index >> level) & 1;
        let mut state = iv(DOMAIN_KEY_NODE + level as u32, 16);
        let (left, right) = if bit == 1 { (sibling, hash) } else { (hash, sibling) };
        state[..8].copy_from_slice(&left);
        state[8..16].copy_from_slice(&right);
        let last = level + 1 == proof.path.len();
        let mut spec = Spec::new(K_KNODE, state)
            .set(TX, tx_id)
            .set(C, bb(level as u32))
            .set(FLO, bb(bit))
            .set(LAST, bb(last as u32));
        if last && let Some((_, index, _)) = signer {
            spec = spec.set(ALO, BabyBear::ONE).set(KIDX, bb(index as u32));
        }
        spec.prev[..8].copy_from_slice(&hash);
        specs.push(spec);
        hash = perm.permute(state)[..8].try_into().unwrap();
    }
    hash
}

/// A policy branch's section, its input's commitment to follow: the
/// leaf's header (`PHDR`, with the timelocks' range checks) and key blocks
/// (`PKEY`; `signed` the key indices that signed, increasing), then the
/// path to the root (`PNODE`s). Returns the root.
#[allow(clippy::too_many_arguments)]
fn policy_section(
    specs: &mut Vec<Spec>,
    tx_id: BabyBear,
    branch: &crate::policy::Branch,
    index: u32,
    path: &[[BabyBear; 8]],
    signed: &[u8],
    heights: &Heights,
    created: u32,
    state: u32,
) -> [BabyBear; 8] {
    let perm = crate::poseidon2::perm24();
    let elements = branch.elements();
    let n = branch.keys.len();
    let key_blocks = n.div_ceil(2);
    // The header, with its checks: each as a field element, so a false
    // claim (a lock not yet met) shows up as a top bit.
    let height = bb(heights.block);
    let (after_height, after_age, created_e) = (bb(branch.after_height), bb(branch.after_age), bb(created));
    let rebind = branch.rebind.unwrap_or(0);
    let lanes = [
        height - after_height,
        height - created_e,
        height - created_e - after_age,
        after_height,
        after_age,
        bb(rebind),
        bb(branch.threshold as u32) - BabyBear::ONE,
        if branch.rebind.is_some() { bb(state) - bb(rebind) - BabyBear::ONE } else { BabyBear::ZERO },
    ]
    .map(|v| v.value());
    let mut sponge = iv(DOMAIN_POLICY_LEAF, elements.len() as u32);
    let prev = sponge;
    for i in 0..16 {
        sponge[i] = sponge[i] + elements[i];
    }
    let mut spec = Spec::new(K_PHDR, sponge)
        .set(TX, tx_id)
        .set(FIRST, BabyBear::ONE)
        .set(CREATED, bb(created))
        .set(RB, bb(branch.rebind.is_some() as u32))
        .set(GROUP, BabyBear::ZERO)
        .set(KIDX, bb(if branch.rebind.is_some() { state } else { 0 }));
    spec.prev = prev;
    spec.lanes = Some(lanes);
    specs.push(spec);
    sponge = perm.permute(sponge);

    // The key blocks.
    let signed_at = |key: usize| bb(signed.contains(&(key as u8)) as u32);
    let mut count = 0u32;
    for b in 1..=key_blocks {
        let prev = sponge;
        for i in 0..16 {
            if let Some(&e) = elements.get(16 * b + i) {
                sponge[i] = sponge[i] + e;
            }
        }
        let last = b == key_blocks;
        let (lo, hi) = (2 * b - 2, 2 * b - 1);
        let mut spec = Spec::new(K_PKEY, sponge)
            .set(TX, tx_id)
            .set(C, bb(b as u32))
            .set(S, bb(count))
            .set(FLO, signed_at(lo))
            .set(FHI, if hi < n { signed_at(hi) } else { BabyBear::ZERO })
            .set(LAST, bb(last as u32))
            .set(RLO, bb((last && n % 2 == 1) as u32))
            .set(ALO, bb((last && !path.is_empty()) as u32));
        spec.prev = prev;
        specs.push(spec);
        count += signed.iter().filter(|&&k| k as usize == lo || k as usize == hi).count() as u32;
        sponge = perm.permute(sponge);
    }
    let mut hash: [BabyBear; 8] = sponge[..8].try_into().unwrap();
    debug_assert_eq!(hash, branch.leaf());

    // The path.
    for (level, sibling) in path.iter().enumerate() {
        let bit = (index >> level) & 1;
        let mut state = iv(DOMAIN_POLICY_NODE + level as u32, 16);
        let (left, right) = if bit == 1 { (*sibling, hash) } else { (hash, *sibling) };
        state[..8].copy_from_slice(&left);
        state[8..16].copy_from_slice(&right);
        let mut spec = Spec::new(K_PNODE, state)
            .set(TX, tx_id)
            .set(C, bb(level as u32))
            .set(FLO, bb(bit))
            .set(LAST, bb((level + 1 == path.len()) as u32));
        spec.prev[..8].copy_from_slice(&hash);
        specs.push(spec);
        hash = perm.permute(state)[..8].try_into().unwrap();
    }
    hash
}

fn commit_spec(
    specs: &mut Vec<Spec>,
    kind: usize,
    pkh: [BabyBear; 8],
    amount: u64,
    tx_id: BabyBear,
    perm: &Poseidon2BabyBear<24>,
) -> [BabyBear; 8] {
    let limbs = amount_limbs(amount);
    let mut state = iv(DOMAIN_COMMITMENT, COMMITMENT_LEN);
    state[..8].copy_from_slice(&pkh);
    state[8..12].copy_from_slice(&limbs);
    let mut spec = Spec::new(kind, state).set(TX, tx_id);
    spec.limbs = limbs;
    specs.push(spec);
    let commitment: [BabyBear; 8] = perm.permute(state)[..8].try_into().unwrap();
    commitment
}

/// Generate every row of every block, column-major.
#[allow(clippy::needless_range_loop)]
fn fill(air: &BlockAir, specs: &[Spec]) -> Vec<Vec<BabyBear>> {
    let n = specs.len() * ROWS;
    let mut columns = vec![vec![BabyBear::ZERO; n]; WIDTH];
    let mut param = [BabyBear::ZERO; PARAM_LEN];
    let mut uid = BabyBear::ZERO;
    let mut tx = BabyBear::ZERO;
    let mut created = BabyBear::ZERO;
    let mut rb = BabyBear::ZERO;
    let mut group = BabyBear::ZERO;
    let mut acc = [BabyBear::ZERO; AMOUNT_LIMBS];
    let mut acc_top = BabyBear::ZERO;

    for (b, spec) in specs.iter().enumerate() {
        let (rows, _) = air.chip.generate(spec.state);
        let base = b * ROWS;
        let carry: Vec<BabyBear> = rows[OUT_ROW][..24].to_vec();

        // Registers that persist across blocks unless this block sets them.
        if spec.kind == K_DIG || spec.kind == K_PHDR {
            param.copy_from_slice(&spec.state[..PARAM_LEN]);
            uid = uid + BabyBear::ONE;
        }
        let mut header: Vec<(usize, BabyBear)> = vec![(spec.kind, BabyBear::ONE)];
        for (i, &v) in param.iter().enumerate() {
            header.push((PARAM + i, v));
        }
        header.push((UID, uid));
        if let Some(&(_, t)) = spec.header.iter().find(|(col, _)| *col == TX) {
            tx = t;
        }
        header.push((TX, tx));
        for (register, value) in [(CREATED, &mut created), (RB, &mut rb), (GROUP, &mut group)] {
            if let Some(&(_, v)) = spec.header.iter().find(|(col, _)| *col == register) {
                *value = v;
            }
            header.push((register, *value));
        }
        header.push((HEIGHT, bb(air.height)));
        let registers = [TX, UID, CREATED, HEIGHT, RB, GROUP];
        header.extend(spec.header.iter().filter(|(col, _)| !registers.contains(col) && !(PARAM..PARAM + PARAM_LEN).contains(col)));
        for i in 0..16 {
            header.push((IN + i, spec.state[i]));
        }
        for (i, &v) in carry.iter().enumerate() {
            header.push((CARRY + i, v));
        }
        for i in 0..24 {
            header.push((PREV + i, spec.prev[i]));
        }
        for j in 0..AMOUNT_LIMBS {
            header.push((LIMB + j, spec.limbs[j]));
        }
        for j in 0..AMOUNT_LIMBS {
            header.push((carry_column(j), from_signed(spec.carries[j])));
        }
        for i in 0..8 {
            header.push((NONCE + i, spec.nonce[i]));
        }

        let is_commit = spec.kind == K_CIN || spec.kind == K_COUT;
        let ranged: [u64; AMOUNT_LIMBS] = if is_commit {
            spec.limbs.map(|l| l.value() as u64)
        } else {
            [0; AMOUNT_LIMBS]
        };
        // A commitment's update to the running total, applied after row 0.
        let mut updated = acc;
        let mut updated_top = acc_top;
        if is_commit {
            let base = bb(1 << 16);
            for j in 0..AMOUNT_LIMBS {
                let carry_in = if j == 0 { BabyBear::ZERO } else { from_signed(spec.carries[j - 1]) };
                let signed = if spec.kind == K_CIN { spec.limbs[j] } else { -spec.limbs[j] };
                updated[j] = acc[j] + signed + carry_in - base * from_signed(spec.carries[j]);
            }
            updated_top = acc_top + from_signed(spec.carries[AMOUNT_LIMBS - 1]);
        }
        let checked_total: [u64; AMOUNT_LIMBS] = if is_commit {
            updated.map(|l| l.value() as u64)
        } else {
            [0; AMOUNT_LIMBS]
        };
        // Digit lanes, 3 bits at a time: the compress output (`DIG`,
        // `SEL`), or values range-checked (`PHDR`, `BAL`).
        let lanes: Option<Vec<u32>> = match spec.lanes {
            Some(values) => Some(values.to_vec()),
            None if spec.kind == K_DIG || spec.kind == K_SEL => Some((0..LANES).map(|e| (carry[e] + spec.state[e]).value()).collect()),
            None => None,
        };

        for r in 0..ROWS {
            let row = base + r;
            for (col, value) in rows[r].iter().enumerate() {
                columns[col][row] = *value;
            }
            for &(col, value) in &header {
                columns[col][row] = value;
            }
            for j in 0..AMOUNT_LIMBS {
                columns[ACC + j][row] = if r == 0 { acc[j] } else { updated[j] };
                if r < 16 {
                    columns[BIT + j][row] = bb(((ranged[j] >> r) & 1) as u32);
                    columns[BIT2 + j][row] = bb(((checked_total[j] >> r) & 1) as u32);
                }
                let mask = (1u64 << r.min(16)) - 1;
                columns[LACC + j][row] = bb((ranged[j] & mask) as u32);
                columns[LACC2 + j][row] = bb((checked_total[j] & mask) as u32);
            }
            columns[ACC_TOP][row] = if r == 0 { acc_top } else { updated_top };
            if let Some(lanes) = &lanes
                && r <= DIGITS_PER_LANE
            {
                let mut dsum = 0u32;
                for e in 0..LANES {
                    let rem = lanes[e] >> (3 * r);
                    columns[REM + e][row] = bb(rem);
                    if r < DIGITS_PER_LANE {
                        columns[B0 + e][row] = bb(rem & 1);
                        columns[B1 + e][row] = bb((rem >> 1) & 1);
                        columns[B2 + e][row] = bb((rem >> 2) & 1);
                    }
                    for q in 0..r {
                        let counted = e < 6 || (e == 6 && q < V - 6 * DIGITS_PER_LANE);
                        if counted {
                            dsum += (lanes[e] >> (3 * q)) & 7;
                        }
                    }
                }
                columns[DSUM][row] = bb(dsum);
            }
        }
        acc = updated;
        acc_top = updated_top;
    }

    // Helpers that read the next row.
    for row in 0..n - 1 {
        for e in 0..LANES {
            let h1 = columns[REM + e][row + 1] * columns[B0 + e][row] * columns[B1 + e][row];
            columns[H1 + e][row] = h1;
            columns[H2 + e][row] = h1 * columns[B2 + e][row];
        }
    }
    columns
}

impl crate::recursion::RecursiveAir for BlockAir {
    fn bus(&self) -> Option<(Bus, crate::recursion::PublicTuples)> {
        Some((BUS, self.public_tuples()))
    }

    /// A version tag; everything else -- the amounts, then both
    /// commitment lists -- is in the tuples.
    fn statement_header(&self) -> Vec<BabyBear> {
        vec![bb(1)]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::{self, Params};

    use crate::output::Output;

    const REWARD: u64 = 1_000_000_000;

    fn challenges() -> Vec<Ext> {
        vec![
            Ext([bb(11), bb(22), bb(33), bb(44)]),
            Ext([bb(55), bb(66), bb(77), bb(88)]),
        ]
    }

    fn keypair(byte: u8) -> (wots::SecretKey, wots::PublicKey) {
        wots::keygen(&[byte; 32])
    }

    fn reward_tx(to: &wots::PublicKey, amount: u64) -> Transaction {
        let mut tx = Transaction::new();
        tx.add_output(Output::new(to, amount)).unwrap();
        tx
    }

    #[test]
    fn a_reward_only_block_satisfies_every_constraint() {
        let (_, pk) = keypair(1);
        let witness = build(&[reward_tx(&pk, REWARD)], REWARD).unwrap();
        stark::check(&witness.air, &witness.trace, &challenges()).unwrap();
    }

    #[test]
    fn an_unbalanced_block_is_refused() {
        let (_, pk) = keypair(1);
        assert_eq!(
            build(&[reward_tx(&pk, REWARD + 1)], REWARD).err(),
            Some(WitnessError::Unbalanced)
        );
    }

    /// A real spend: an earlier reward output, spent to two outputs, plus
    /// this block's own reward claim.
    fn spend_block() -> Witness {
        let (sk_a, pk_a) = keypair(1);
        let (_, pk_b) = keypair(2);
        let (_, pk_c) = keypair(3);
        let (_, pk_m) = keypair(4);
        let mut spend = Transaction::new();
        spend.add_input(&pk_a, 700).unwrap();
        spend.add_output(Output::new(&pk_b, 500)).unwrap();
        spend.add_output(Output::new(&pk_c, 150)).unwrap();
        assert!(spend.sign_input(&pk_a, &sk_a));
        // The 50 left over is the fee, claimed with the reward.
        build(&[spend, reward_tx(&pk_m, REWARD + 50)], REWARD).unwrap()
    }

    #[test]
    fn a_block_spending_a_signed_input_satisfies_every_constraint() {
        let witness = spend_block();
        assert_eq!(witness.air.inputs.len(), 1);
        assert_eq!(witness.air.outputs.len(), 3);
        stark::check(&witness.air, &witness.trace, &challenges()).unwrap();
    }

    #[test]
    fn the_public_lists_match_what_a_block_body_publishes() {
        let (sk_a, pk_a) = keypair(1);
        let (_, pk_b) = keypair(2);
        let mut spend = Transaction::new();
        spend.add_input(&pk_a, 700).unwrap();
        spend.add_output(Output::new(&pk_b, 700)).unwrap();
        assert!(spend.sign_input(&pk_a, &sk_a));
        let txs = [spend, reward_tx(&pk_b, REWARD)];
        let witness = build(&txs, REWARD).unwrap();
        let body = crate::block::BlockBody::from_transactions(&txs).unwrap();
        let as_elements = |list: &[[u8; 32]]| -> Vec<[BabyBear; 8]> { list.iter().map(digest_from_bytes).collect() };
        assert_eq!(witness.air.inputs, as_elements(&body.inputs));
        assert_eq!(witness.air.outputs, as_elements(&body.outputs));
    }

    /// Tampering anywhere a cheating miner might -- a chain value, an
    /// amount, a digit -- breaks some constraint.
    #[test]
    fn tampering_with_the_witness_breaks_a_constraint() {
        let witness = spend_block();
        let first_chain_row = (0..witness.trace[0].len())
            .find(|&r| witness.trace[K_CHAIN][r] == BabyBear::ONE)
            .unwrap();
        let first_cout_row = (0..witness.trace[0].len())
            .find(|&r| witness.trace[K_COUT][r] == BabyBear::ONE)
            .unwrap();
        let first_dig_row = (0..witness.trace[0].len())
            .find(|&r| witness.trace[K_DIG][r] == BabyBear::ONE)
            .unwrap();
        let cases: [(usize, usize); 4] = [
            (STATE + 8, first_chain_row),     // a chain's starting value
            (STATE + 8, first_cout_row),      // an output's amount limb
            (B0, first_dig_row + 3),          // a digit bit
            (LIMB, first_cout_row + 5),       // a limb copy mid-block
        ];
        for (col, row) in cases {
            let mut trace = witness.trace.clone();
            trace[col][row] = trace[col][row] + BabyBear::ONE;
            assert!(stark::check(&witness.air, &trace, &challenges()).is_err(), "column {col}, row {row}");
        }
    }

    /// Changing the public lists -- an extra output, a missing input --
    /// leaves the bus unbalanced.
    #[test]
    fn a_different_public_statement_is_refused() {
        let witness = spend_block();
        let (inputs, nonces) = (witness.air.inputs.clone(), witness.air.nonces.clone());
        let mut outputs = witness.air.outputs.clone();
        outputs.push([bb(1); 8]);
        let mut more_nonces = nonces.clone();
        more_nonces.push([bb(0); 8]);
        let air = BlockAir::new(witness.air.num_blocks, inputs.clone(), outputs, more_nonces, REWARD);
        assert!(stark::check(&air, &witness.trace, &challenges()).is_err());
        let air = BlockAir::new(witness.air.num_blocks, vec![], witness.air.outputs.clone(), nonces.clone(), REWARD);
        assert!(stark::check(&air, &witness.trace, &challenges()).is_err());
        // A different nonce for an output than the one signed.
        let mut altered = nonces.clone();
        altered[0][3] = altered[0][3] + BabyBear::ONE;
        let air = BlockAir::new(witness.air.num_blocks, inputs.clone(), witness.air.outputs.clone(), altered, REWARD);
        assert!(stark::check(&air, &witness.trace, &challenges()).is_err());
        // The honest statement passes.
        let air = BlockAir::new(witness.air.num_blocks, inputs, witness.air.outputs.clone(), nonces, REWARD);
        assert!(stark::check(&air, &witness.trace, &challenges()).is_ok());
    }

    #[test]
    fn a_reward_only_block_proves_and_verifies() {
        let (_, pk) = keypair(1);
        let witness = build(&[reward_tx(&pk, REWARD)], REWARD).unwrap();
        let params = Params {
            log_blowup: 1,
            num_queries: 8,
            grinding_bits: 4,
            hiding: true,
        };
        let proof = stark::prove(&witness.air, &witness.trace, &params, [9; 32]).unwrap();
        assert!(stark::verify(&witness.air, &proof, &params));
    }

    /// Not a correctness test: what proving costs at the consensus
    /// parameters, for a reward-only block and a block with one spend.
    /// Run with `cargo test --release -- --ignored --nocapture spend_block_cost`.
    #[test]
    #[ignore]
    fn spend_block_cost() {
        let (_, pk) = keypair(1);
        let reward_only = build(&[reward_tx(&pk, REWARD)], REWARD).unwrap();
        let candidates = [
            ("blowup 4, 42 queries, 16-bit grind", Params { log_blowup: 2, num_queries: 42, grinding_bits: 16, hiding: true }),
            ("blowup 8, 27 queries, 20-bit grind", Params { log_blowup: 3, num_queries: 27, grinding_bits: 20, hiding: true }),
            ("blowup 16, 20 queries, 20-bit grind", Params { log_blowup: 4, num_queries: 20, grinding_bits: 20, hiding: true }),
        ];
        let blocks = [("reward-only", reward_only), ("one spend", spend_block())];
        for ((name, witness), (label, params)) in blocks.iter().flat_map(|b| candidates.iter().map(move |c| (b, c))) {
            let start = std::time::Instant::now();
            let proof = stark::prove(&witness.air, &witness.trace, params, [9; 32]).unwrap();
            let proving = start.elapsed();
            let start = std::time::Instant::now();
            assert!(stark::verify(&witness.air, &proof, params));
            println!(
                "{name} [{label}]: {} rows x {WIDTH} columns -- prove {proving:.2?}, verify {:.2?}, {} KB",
                witness.air.trace_len(),
                start.elapsed(),
                proof.to_bytes().len() / 1024
            );
        }
    }

    /// The running total, natively: any mix of additions and
    /// subtractions -- going negative, past 2^64 -- that nets to minus the
    /// reward finishes cleanly; anything else doesn't.
    #[test]
    fn the_running_total_tracks_any_signed_sum_exactly() {
        let mut total = RunningTotal::default();
        total.add(u64::MAX, -1); // well below zero
        total.add(u64::MAX, 1);
        total.add(1 << 63, 1);
        total.add(1 << 63, 1); // 2^64 above zero now
        total.add(u64::MAX, -1);
        total.add(1, -1);
        assert_eq!((total.limbs, total.top), ([0; AMOUNT_LIMBS], 0));
        total.add(REWARD, -1);
        assert!(total.finish((REWARD, 0)).is_some());
        total.add(1, -1);
        assert!(total.finish((REWARD, 0)).is_none());
    }

    /// Amounts far past what a single limb-sum could hold without
    /// wrapping: two inputs of 2^63 (2^64 together -- more than any u64),
    /// spent to outputs that are laid out *before* the inputs' running
    /// total catches up, so it goes deeply negative on the way.
    #[test]
    fn huge_amounts_balance_exactly_through_the_circuit() {
        let (sk_a, pk_a) = keypair(1);
        let (sk_b, pk_b) = keypair(2);
        let (_, pk_c) = keypair(3);
        let (_, pk_d) = keypair(4);
        let (_, pk_m) = keypair(5);
        let half = 1u64 << 63;
        // Outputs first: a transaction with no inputs can't create value,
        // so pay the reward out in it, ahead of the big spend.
        let reward = reward_tx(&pk_m, REWARD);
        let mut spend = Transaction::new();
        spend.add_input(&pk_a, half).unwrap();
        spend.add_input(&pk_b, half).unwrap();
        spend.add_output(Output::new(&pk_c, u64::MAX)).unwrap();
        spend.add_output(Output::new(&pk_d, 1)).unwrap();
        assert!(spend.sign_input(&pk_a, &sk_a));
        assert!(spend.sign_input(&pk_b, &sk_b));
        let witness = build(&[reward, spend], REWARD).unwrap();
        stark::check(&witness.air, &witness.trace, &challenges()).unwrap();

        // One unit off anywhere and it no longer balances.
        let mut greedy = Transaction::new();
        greedy.add_input(&pk_a, half).unwrap();
        greedy.add_input(&pk_b, half).unwrap();
        greedy.add_output(Output::new(&pk_c, u64::MAX)).unwrap();
        greedy.add_output(Output::new(&pk_d, 2)).unwrap();
        assert!(greedy.sign_input(&pk_a, &sk_a));
        assert!(greedy.sign_input(&pk_b, &sk_b));
        assert_eq!(build(&[greedy], REWARD).err(), Some(WitnessError::Unbalanced));
    }

    /// A miner fudging a carry in the running total -- to make a block
    /// look balanced when it isn't -- breaks a constraint.
    #[test]
    fn a_fudged_running_total_carry_breaks_a_constraint() {
        let witness = spend_block();
        let commit_row = (0..witness.trace[0].len())
            .find(|&r| witness.trace[K_COUT][r] == BabyBear::ONE)
            .unwrap();
        for col in [CRY, ACC + 1, ACC_TOP] {
            let mut trace = witness.trace.clone();
            for value in &mut trace[col][commit_row..commit_row + ROWS] {
                *value = *value + BabyBear::ONE;
            }
            assert!(stark::check(&witness.air, &trace, &challenges()).is_err(), "column {col}");
        }
    }

    /// The attack the whole circuit exists to stop: a miner takes a
    /// properly signed spend, redirects one of its outputs to itself after
    /// the fact, and lays the result out as faithfully as it can. The
    /// signature covers the original outputs, not these, so the chains no
    /// longer reach the owner's public key -- and the circuit refuses.
    #[test]
    fn a_spend_with_outputs_changed_after_signing_is_refused() {
        let (sk_a, pk_a) = keypair(1);
        let (_, pk_b) = keypair(2);
        let (_, pk_thief) = keypair(66);
        let mut spend = Transaction::new();
        spend.add_input(&pk_a, 700).unwrap();
        spend.add_output(Output::new(&pk_b, 700)).unwrap();
        assert!(spend.sign_input(&pk_a, &sk_a));
        spend.outputs[0] = Output::new(&pk_thief, 700);
        assert!(!spend.verify());

        let (_, pk_m) = keypair(4);
        let witness = build_inner(&[spend, reward_tx(&pk_m, REWARD)], (REWARD, 0), false).unwrap();
        // Every per-row rule holds -- the layout is faithful -- but the
        // bus can't balance: the chains' ends aren't the owner's tops.
        assert!(matches!(
            stark::check(&witness.air, &witness.trace, &challenges()),
            Err(stark::Error::AuxBoundaryViolated(_))
        ));
    }

    /// Likewise a spend whose signature belongs to a different key.
    #[test]
    fn a_spend_signed_by_the_wrong_key_is_refused() {
        let (_, pk_a) = keypair(1);
        let (sk_other, _) = keypair(5);
        let (_, pk_b) = keypair(2);
        let mut spend = Transaction::new();
        spend.add_input(&pk_a, 700).unwrap();
        spend.add_output(Output::new(&pk_b, 700)).unwrap();
        // `sign_input` can't tell the key is wrong; it just signs.
        assert!(spend.sign_input(&pk_a, &sk_other));
        assert!(!spend.verify());

        let witness = build_inner(&[spend], (0, 0), false);
        // Zero reward here keeps the block balanced on its own terms, so
        // only the signature is wrong.
        let witness = witness.unwrap();
        assert!(matches!(
            stark::check(&witness.air, &witness.trace, &challenges()),
            Err(stark::Error::AuxBoundaryViolated(_))
        ));
    }

    // ---- policy inputs ----

    use crate::policy::{Branch, Policy};
    use crate::transaction::Signer;

    fn key_hash(byte: u8) -> [u8; 32] {
        digest_to_bytes(keypair(byte).1.hash())
    }

    fn branch(threshold: u8, keys: &[u8]) -> Branch {
        Branch { threshold, keys: keys.iter().map(|&k| key_hash(k)).collect(), after_height: 0, after_age: 0, hashlock: None, rebind: None }
    }

    /// A transaction spending `amount` from `policy` by branch `index`
    /// (revealing `preimage`), signed by the keys `signers` (key indices,
    /// with their keys' seeds), paying it all to a fresh key.
    fn policy_spend(policy: &Policy, index: u32, preimage: Option<[u8; 32]>, signers: &[(u8, u8)], amount: u64) -> Transaction {
        let mut tx = Transaction::new();
        let path = policy.path(index).iter().map(|h| digest_to_bytes(*h)).collect();
        tx.add_policy_input(policy.branches[index as usize].clone(), index, path, preimage, amount).unwrap();
        tx.add_output(Output::new(&keypair(99).1, amount)).unwrap();
        let commitment = tx.inputs[0].commitment();
        for &(index, seed) in signers {
            let (sk, pk) = keypair(seed);
            assert!(tx.sign_policy_input(&commitment, index, &pk, crate::keytree::KeyProof::one_time(), &sk));
        }
        tx
    }

    /// Every input of `txs` created at `created`, in a block at `height`.
    fn heights(txs: &[Transaction], height: u32, created: u32) -> Heights {
        let created = txs.iter().flat_map(|t| &t.inputs).map(|i| (i.commitment(), created)).collect();
        Heights { block: height, created }
    }

    fn satisfies(txs: &[Transaction], height: u32, created: u32) -> bool {
        let witness = build_shaped(txs, (0, 0), None, true, &heights(txs, height, created)).unwrap();
        stark::check(&witness.air, &witness.trace, &challenges()).is_ok()
    }

    /// Laid out without the native checks -- as a miner forging it would
    /// -- the circuit itself must refuse.
    fn refused(txs: &[Transaction], height: u32, created: u32) -> bool {
        let witness = build_shaped(txs, (0, 0), None, false, &heights(txs, height, created)).expect("a forger can lay it out");
        stark::check(&witness.air, &witness.trace, &challenges()).is_err()
    }

    /// A 2-of-3 branch, alone in its policy (no path), spent by keys 0 and
    /// 2 -- alongside a plain input in the same transaction, which both
    /// sign.
    #[test]
    fn a_threshold_policy_spend_satisfies_every_constraint() {
        let policy = Policy { branches: vec![branch(2, &[11, 12, 13])] };
        let mut tx = Transaction::new();
        tx.add_policy_input(policy.branches[0].clone(), 0, vec![], None, 500).unwrap();
        let (sk_a, pk_a) = keypair(1);
        tx.add_input(&pk_a, 200).unwrap();
        tx.add_output(Output::new(&keypair(99).1, 700)).unwrap();
        let commitment = Output::locked(policy.lock(), 500).commitment();
        assert!(tx.sign_policy_input(&commitment, 0, &keypair(11).1, crate::keytree::KeyProof::one_time(), &keypair(11).0));
        assert!(tx.sign_policy_input(&commitment, 2, &keypair(13).1, crate::keytree::KeyProof::one_time(), &keypair(13).0));
        assert!(tx.sign_input(&pk_a, &sk_a));
        assert!(tx.verify());
        assert_eq!(tx.signature_count(), 3);
        assert!(satisfies(&[tx], 10, 3));
    }

    /// A three-branch policy -- a refund after height 100, a claim by hash
    /// lock, and a cooperative 2-of-2 after an age of 5 -- each spent
    /// within its locks; the even and odd key counts both covered.
    #[test]
    fn every_branch_of_a_policy_spends_within_its_locks() {
        let preimage = digest_to_bytes([bb(7); 8]);
        let refund = Branch { after_height: 100, ..branch(1, &[21]) };
        let claim = Branch { hashlock: crate::policy::hashlock(&preimage), ..branch(1, &[22]) };
        let coop = Branch { after_age: 5, ..branch(2, &[21, 22]) };
        let policy = Policy { branches: vec![refund, claim, coop] };
        assert!(policy.is_valid());
        assert!(satisfies(&[policy_spend(&policy, 0, None, &[(0, 21)], 300)], 100, 3));
        assert!(satisfies(&[policy_spend(&policy, 1, Some(preimage), &[(0, 22)], 300)], 7, 3));
        assert!(satisfies(&[policy_spend(&policy, 2, None, &[(0, 21), (1, 22)], 300)], 8, 3));
    }

    /// Timelocks not yet met: refused natively, and by the circuit.
    #[test]
    fn a_spend_before_its_timelocks_is_refused() {
        let policy = Policy { branches: vec![Branch { after_height: 100, after_age: 5, ..branch(1, &[21]) }] };
        let tx = policy_spend(&policy, 0, None, &[(0, 21)], 300);
        assert_eq!(build_shaped(std::slice::from_ref(&tx), (0, 0), None, true, &heights(std::slice::from_ref(&tx), 99, 3)).err(), Some(WitnessError::LockNotMet(0)));
        assert!(satisfies(std::slice::from_ref(&tx), 100, 95));
        assert!(refused(std::slice::from_ref(&tx), 99, 3), "too early");
        assert!(refused(std::slice::from_ref(&tx), 100, 96), "too young");
        assert!(refused(std::slice::from_ref(&tx), 100, 101), "created after the spend");
    }

    /// Too few signers, a signer whose key isn't the branch's, a wrong
    /// preimage, or none: each refused by the circuit.
    #[test]
    fn a_forged_policy_spend_is_refused() {
        let policy = Policy { branches: vec![branch(2, &[31, 32, 33]), Branch { hashlock: crate::policy::hashlock(&digest_to_bytes([bb(5); 8])), ..branch(1, &[34]) }] };
        let few = policy_spend(&policy, 0, None, &[(0, 31)], 300);
        assert!(!few.verify());
        assert!(refused(&[few], 10, 3));

        let mut stranger = policy_spend(&policy, 0, None, &[(0, 31), (1, 32)], 300);
        assert!(stranger.verify());
        // Key 1 signed by someone else entirely (a valid signature, from
        // the wrong key). The message doesn't depend on who signs.
        let (sk, pk) = keypair(40);
        let message = stranger.signing_message();
        let Spend::Policy(p) = &mut stranger.inputs[0].spend else { unreachable!() };
        p.signers[1] = Signer { index: 1, pubkey: pk, proof: crate::keytree::KeyProof::one_time(), signature: wots::sign(&sk, message) };
        assert!(!stranger.verify());
        assert!(refused(&[stranger], 10, 3));

        let wrong = policy_spend(&policy, 1, Some(digest_to_bytes([bb(6); 8])), &[(0, 34)], 300);
        assert!(!wrong.verify());
        assert!(refused(&[wrong], 10, 3));
    }


    // ---- multi-use keys ----

    use crate::keytree::{KeyProof, KeyTree};

    /// An output locked to a key tree, spent by one of its leaves: every
    /// constraint holds, and the input it publishes is that output's.
    #[test]
    fn a_tree_key_spend_satisfies_every_constraint() {
        let tree = KeyTree::generate(&[7; 32], 3);
        let (sk, pk) = tree.leaf(5);
        let mut tx = Transaction::new();
        tx.add_tree_input(&pk, tree.proof(5), 400).unwrap();
        tx.add_output(Output::new(&keypair(99).1, 400)).unwrap();
        assert!(tx.sign_input(&pk, &sk));
        assert!(tx.verify());
        let witness = build_shaped(std::slice::from_ref(&tx), (0, 0), None, true, &heights(std::slice::from_ref(&tx), 4, 1)).unwrap();
        assert_eq!(witness.air.public_inputs(), [digest_from_bytes(&Output::locked(tree.id(), 400).commitment())]);
        stark::check(&witness.air, &witness.trace, &challenges()).unwrap();
    }

    /// A branch listing a key tree and a one-time key, signed by a leaf of
    /// the one and by the other; and the same with the leaf's key paired
    /// with another leaf's path, refused.
    #[test]
    fn a_policy_signer_may_hold_a_key_tree() {
        let tree = KeyTree::generate(&[8; 32], 2);
        let b = Branch { threshold: 2, keys: vec![tree.id(), key_hash(12)], after_height: 0, after_age: 0, hashlock: None, rebind: None };
        let policy = Policy { branches: vec![b.clone()] };
        let commitment = Output::locked(policy.lock(), 300).commitment();
        let spend = |proof: KeyProof| {
            let mut tx = Transaction::new();
            tx.add_policy_input(b.clone(), 0, vec![], None, 300).unwrap();
            tx.add_output(Output::new(&keypair(99).1, 300)).unwrap();
            let (sk, pk) = tree.leaf(2);
            let honest = proof == tree.proof(2);
            assert_eq!(tx.sign_policy_input(&commitment, 0, &pk, proof.clone(), &sk), honest);
            if !honest {
                // Forced in, as a forger would.
                let message = tx.signing_message();
                let Spend::Policy(p) = &mut tx.inputs[0].spend else { unreachable!() };
                p.signers.push(Signer { index: 0, pubkey: pk, proof, signature: wots::sign(&sk, message) });
            }
            assert!(tx.sign_policy_input(&commitment, 1, &keypair(12).1, KeyProof::one_time(), &keypair(12).0));
            tx
        };
        let good = spend(tree.proof(2));
        assert!(good.verify());
        assert!(satisfies(&[good], 4, 1));
        let bad = spend(KeyProof { index: 2, path: tree.proof(3).path });
        assert!(!bad.verify());
        assert!(refused(&[bad], 4, 1));
    }


    // ---- REBIND ----

    /// An eltoo-style update output: a 2-of-2 REBIND branch at `state`,
    /// alone in its policy.
    fn update_policy(state: u32) -> Policy {
        Policy { branches: vec![Branch { rebind: Some(state), ..branch(2, &[51, 52]) }] }
    }

    /// Update `declared`: spending the update output at `from`, naming its
    /// one output (the channel's next update output), signed by both
    /// parties in REBIND mode.
    fn update(from: u32, declared: u32) -> Transaction {
        let (spent, next) = (update_policy(from), update_policy(declared));
        let output = Output::locked(next.lock(), 1_000).with_nonce([declared as u8; 16]);
        let mut tx = Transaction::new();
        tx.add_rebind_input(spent.branches[0].clone(), 0, vec![], None, 1_000, declared, vec![output.commitment()]).unwrap();
        tx.add_output(output).unwrap();
        let commitment = Output::locked(spent.lock(), 1_000).commitment();
        for (index, seed) in [(0u8, 51u8), (1, 52)] {
            let (sk, pk) = keypair(seed);
            assert!(tx.sign_policy_input(&commitment, index, &pk, KeyProof::one_time(), &sk));
        }
        assert!(!tx.is_finalized(), "REBIND signatures leave room for a fee");
        tx
    }

    /// An update spends an earlier one, with a fee input and change output
    /// added after both parties signed; re-pointed (before the fee) at
    /// another earlier update, it still does -- the same signatures -- but
    /// not at one that isn't earlier.
    #[test]
    fn a_rebind_update_spends_any_earlier_update() {
        // The fee: an input and its change, added (and signed) by whoever
        // publishes it.
        let with_fee = |mut tx: Transaction| {
            let (sk_f, pk_f) = keypair(53);
            tx.add_input(&pk_f, 70).unwrap();
            tx.add_output(Output::new(&keypair(54).1, 60).with_nonce([9; 16])).unwrap();
            assert!(tx.sign_input(&pk_f, &sk_f));
            assert_eq!(tx.fee(), Some(10));
            tx
        };
        let check = |tx: &Transaction, ok: bool| {
            let txs = std::slice::from_ref(tx);
            let witness = build_shaped(txs, (0, tx.fee().unwrap()), None, ok, &heights(txs, 10, 2)).unwrap();
            stark::check(&witness.air, &witness.trace, &challenges()).is_ok()
        };
        let tx = with_fee(update(3, 5));
        assert!(tx.verify());
        assert!(check(&tx, true));
        let mut fee_first = tx.clone();
        let old = Output::locked(update_policy(3).lock(), 1_000).commitment();
        assert!(!fee_first.rebind(&old, update_policy(4).branches[0].clone(), 0, vec![], 1_000), "the fee's signature covers the input");
        // Re-pointed at the update at state 4 instead, then the fee.
        let mut repointed = update(3, 5);
        assert!(repointed.rebind(&old, update_policy(4).branches[0].clone(), 0, vec![], 1_000));
        let repointed = with_fee(repointed);
        assert!(repointed.verify());
        assert!(check(&repointed, true));
        // Not at one that isn't earlier.
        for later in [5, 6] {
            let mut stale = update(3, 5);
            assert!(stale.rebind(&old, update_policy(later).branches[0].clone(), 0, vec![], 1_000));
            let stale = with_fee(stale);
            assert!(!stale.verify());
            assert!(!check(&stale, false), "an update at {later} spent by 5");
        }
    }

    /// REBIND signatures must sign the REBIND message: signatures over the
    /// transaction's message instead, or a named output changed after
    /// signing, are refused.
    #[test]
    fn a_rebind_signature_signs_only_its_message() {
        let tx = update(3, 5);
        let mut all_mode = tx.clone();
        let message = all_mode.signing_message();
        let Spend::Policy(p) = &mut all_mode.inputs[0].spend else { unreachable!() };
        for s in &mut p.signers {
            s.signature = wots::sign(&keypair(50 + s.index + 1).0, message);
        }
        assert!(!all_mode.verify());
        assert!(refused(&[all_mode], 10, 2));

        let mut changed = tx.clone();
        let Spend::Policy(p) = &mut changed.inputs[0].spend else { unreachable!() };
        let named = p.named[0];
        let output = changed.outputs.iter_mut().find(|o| o.commitment() == named).unwrap();
        output.nonce[0] ^= 1;
        assert!(!changed.verify());
        assert!(refused(&[changed], 10, 2));
    }

}

