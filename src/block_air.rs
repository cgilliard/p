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
//! - `DIG`: the digit derivation `compress(param, TAG_MESSAGE, message,
//!   randomizer)`, whose 8 output elements are decomposed, canonically,
//!   into 3-bit digits in the block's spare rows -- the first 64 sent on
//!   the bus to their chains, and required to sum to `TARGET_SUM`. Each
//!   input's section starts with one; it receives its transaction's
//!   message from the bus.
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
    BabyBear, DOMAIN_COMMITMENT, DOMAIN_PUBKEY, DOMAIN_SIGNING, Poseidon2BabyBear, digest_from_bytes, digest_to_bytes,
};
use crate::poseidon2_air::{Poseidon2Chip, ROWS};
use crate::stark::{Air, AuxBoundary, AuxFrame, Boundary};
use crate::transaction::Transaction;
use crate::wots::{self, CHAIN_LEN, CHAIN_STEPS, PARAM_LEN, TAG_CHAIN, TAG_MESSAGE, TARGET_SUM, V};

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
const KINDS: [usize; 8] = [K_CHAIN, K_PK, K_DIG, K_CIN, K_COUT, K_MSG, K_PAD, K_BAL];

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
const FLAGS: [usize; 10] = [START, END, FLO, FHI, FIRST, LAST, RLO, RHI, ALO, AHI];

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
pub const WIDTH: usize = 227;

/// The column holding carry `k` out of limb `k` of the running total.
fn carry_column(k: usize) -> usize {
    if k < 3 { CRY + k } else { CRY3 }
}

/// Columns constant within a block.
fn constant_columns() -> impl Iterator<Item = usize> {
    (K_CHAIN..LIMB + AMOUNT_LIMBS).chain(CRY..CRY + 3).chain([CRY3]).chain(NONCE..NONCE + 8)
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
const NUM_PERIODIC: usize = CHIP_PERIODIC + 12;

// ---- Bus ----------------------------------------------------------------

const TAG_CH: u32 = 1;
const TAG_TOP: u32 = 2;
const TAG_MSG: u32 = 3;
const TAG_ITEM: u32 = 4;
const TAG_PIN: u32 = 5;
const TAG_POUT: u32 = 6;
/// The public amounts `a`, `b`: `[TAG_NET, 0, 0, a limbs, b limbs]`.
pub const TAG_NET: u32 = 7;
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
        let mut air = BlockAir {
            chip: Poseidon2Chip::<24>::new(),
            num_blocks,
            inputs,
            outputs,
            nonces,
            net,
            capacity,
            num_constraints: 0,
        };
        let zeros = vec![BabyBear::ZERO; WIDTH];
        air.num_constraints = air.constraints(&zeros, &zeros, &[BabyBear::ZERO; NUM_PERIODIC]).len();
        air
    }

    pub fn num_blocks(&self) -> usize {
        self.num_blocks
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
        // Section ids, transaction ids, and the section's parameter.
        out.push(px * (n[UID] - c[UID] - n[K_DIG]));
        out.push(px * (one - n[K_DIG]) * (n[K_CHAIN] + n[K_PK] + n[K_CIN]) * (n[TX] - c[TX]));
        for i in 0..PARAM_LEN {
            out.push(px * (one - n[K_DIG]) * (n[PARAM + i] - c[PARAM + i]));
        }

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

        // Sponges (PK and MSG): initial state, capacity, continuity.
        let (kp, km) = (c[K_PK], c[K_MSG]);
        let sponge = kp + km;
        for i in 16..24 {
            out.push(p0 * sponge * (c[STATE + i] - c[PREV + i]));
        }
        for i in (0..16).chain(18..24) {
            out.push(sponge * c[FIRST] * c[PREV + i]);
        }
        out.push(c[FIRST] * (kp * (c[PREV + 16] - k(DOMAIN_PUBKEY)) + km * (c[PREV + 16] - k(DOMAIN_SIGNING))));
        out.push(kp * c[FIRST] * (c[PREV + 17] - k(PK_HASH_LEN)));
        let n_continues = (n[K_PK] + n[K_MSG]) * (one - n[FIRST]);
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

        // PK: param in the first block, nothing in the last's second half,
        // the end at block 32, and the input commitment right after.
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
        out.push(px * kp * c[LAST] * (n[K_CIN] - one));
        out.push(px * n[K_CIN] * (kp * c[LAST] - one));
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
        let eight = k(8);
        let eight_pow_9 = k(8u32.pow(9));
        let mut digit_sum = F::ZERO;
        for e in 0..LANES {
            let digit = c[B0 + e] + c[B1 + e] + c[B1 + e] + k(4) * c[B2 + e];
            out.push(kd * lt10 * (c[REM + e] - digit - eight * n[REM + e]));
            for bit in [B0, B1, B2] {
                out.push(kd * lt10 * c[bit + e] * (c[bit + e] - one));
            }
            let output = c[CARRY + e] + c[IN + e];
            out.push(kd * p0 * (c[REM + e] - output));
            out.push(kd * row10 * c[REM + e] * (c[REM + e] - one));
            out.push(c[H1 + e] - n[REM + e] * c[B0 + e] * c[B1 + e]);
            out.push(c[H2 + e] - c[H1 + e] * c[B2 + e]);
            // Canonical: a top bit of 1 with top digit 7 leaves no room
            // below P for any lower bits.
            out.push(kd * row9 * c[H2 + e] * (output - eight_pow_9 * c[REM + e]));
            if e < 6 {
                digit_sum = digit_sum + digit;
            } else if e == 6 {
                digit_sum = digit_sum + p[PR_LMASK6] * digit;
            }
        }
        out.push(kd * lt10 * (n[DSUM] - c[DSUM] - digit_sum));
        out.push(kd * p0 * c[DSUM]);
        out.push(kd * row10 * (c[DSUM] - k(TARGET_SUM)));

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
                + (kin + kout) * pout,
            values: mix(&[
                (kc, tuple(TAG_CH, c[UID], c[C], &[c[S]])),
                (kp, pk_half(0, FLO, two_c - one)),
                (kd, tuple(TAG_MSG, c[TX], F::ZERO, &range(IN + 6, 8))),
                (km, tuple(TAG_ITEM, c[TX], c[RLO], &item)),
                (kin, tuple(TAG_PIN, F::ZERO, F::ZERO, &carry8)),
                (kout, tuple(TAG_POUT, F::ZERO, F::ZERO, &committed)),
            ]),
        });
        // Slot 1.
        slots.push(Interaction {
            multiplicity: kc * pout * c[END] - kp * p0 * (one - c[LAST]) + (kin + kout) * pout,
            values: mix(&[
                (kc, tuple(TAG_TOP, c[UID], c[C], &compress_out)),
                (kp, pk_half(1, FHI, two_c)),
                (kin, tuple(TAG_ITEM, c[TX], one, &carry8)),
                (kout, tuple(TAG_ITEM, c[TX], F::ZERO, &committed)),
            ]),
        });
        // Slot 2: a message, once per input; or digit lane 0; or the
        // public amounts.
        let kb = c[K_BAL];
        let net: Vec<F> = range(LIMB, AMOUNT_LIMBS).into_iter().chain(range(LACC, AMOUNT_LIMBS)).collect();
        slots.push(Interaction {
            multiplicity: km * pout * c[LAST] * c[NIN] + kd * lt10 + kb * p0,
            values: mix(&[
                (km, tuple(TAG_MSG, c[TX], F::ZERO, &carry8)),
                (kd, tuple(TAG_CH, c[UID], p[PR_DROW], &[digit(0)])),
                (kb, tuple(TAG_NET, F::ZERO, F::ZERO, &net)),
            ]),
        });
        // Slots 3-8: digit lanes 1-6.
        for e in 1..7 {
            let mask = if e < 6 { lt10 } else { p[PR_LMASK6] };
            let chain = k((DIGITS_PER_LANE * e) as u32) + p[PR_DROW];
            slots.push(Interaction {
                multiplicity: kd * mask,
                values: mix(&[(kd, tuple(TAG_CH, c[UID], chain, &[digit(e)]))]),
            });
        }
        slots
    }

    fn public_tuples(&self) -> Vec<(BabyBear, Vec<BabyBear>)> {
        let entry = |tag: u32, commitment: &[BabyBear; 8], nonce: Option<&[BabyBear; 8]>| {
            let mut t = vec![bb(tag), BabyBear::ZERO, BabyBear::ZERO];
            t.extend_from_slice(commitment);
            t.extend_from_slice(nonce.unwrap_or(&[BabyBear::ZERO; 8]));
            (BabyBear::ONE, t)
        };
        let mut amounts = vec![bb(TAG_NET), BabyBear::ZERO, BabyBear::ZERO];
        amounts.extend(amount_limbs(self.net.0));
        amounts.extend(amount_limbs(self.net.1));
        let (in_slots, out_slots) = self.capacity.unwrap_or((self.inputs.len(), self.outputs.len()));
        let unused = |tag: u32| {
            let mut t = vec![bb(tag)];
            t.resize(TUPLE_LEN, BabyBear::ZERO);
            (BabyBear::ZERO, t)
        };
        std::iter::once((BabyBear::ONE, amounts))
            .chain(self.inputs.iter().map(|c| entry(TAG_PIN, c, None)))
            .chain((self.inputs.len()..in_slots).map(|_| unused(TAG_PIN)))
            .chain(self.outputs.iter().zip(&self.nonces).map(|(c, n)| entry(TAG_POUT, c, Some(n))))
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
/// `sum(inputs) + a == sum(outputs) + b` for `net = (a, b)`.
pub fn build_chunk(transactions: &[Transaction], net: (u64, u64), shape: ChunkShape) -> Result<Witness, WitnessError> {
    build_shaped(transactions, net, Some(shape), true)
}

/// `build`, optionally skipping the native signature check -- so tests can
/// play a miner laying out a transaction whose signatures *don't* cover
/// it, and confirm the circuit itself refuses.
// Indexing several parallel arrays (digits, signature values, tops) by
// chain is clearer than zipping them.
#[allow(clippy::needless_range_loop)]
fn build_inner(transactions: &[Transaction], net: (u64, u64), check_signatures: bool) -> Result<Witness, WitnessError> {
    build_shaped(transactions, net, None, check_signatures)
}

fn build_shaped(
    transactions: &[Transaction],
    net: (u64, u64),
    shape: Option<ChunkShape>,
    check_signatures: bool,
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
            uid += 1;
            let pk = &input.pubkey;
            let signature = input.signature.as_ref().expect("verified transactions are signed");
            let param = pk.param;
            // A miner forging a spend would at least pick a randomizer
            // whose digits hit the target sum (a few dozen tries) -- so
            // the unchecked path does too, leaving the chains themselves
            // as the only thing that can give the forgery away.
            let randomizer = if check_signatures {
                signature.randomizer
            } else {
                (0u32..)
                    .map(|trial| {
                        let mut r = signature.randomizer;
                        r[1] = r[1] + bb(trial);
                        r
                    })
                    .find(|&r| wots::derive_digits(&param, message, r).iter().sum::<u32>() == TARGET_SUM)
                    .unwrap()
            };
            let digits = wots::derive_digits(&param, message, randomizer);
            let param_header = |spec: Spec| -> Spec {
                (0..PARAM_LEN).fold(spec, |s, i| s.set(PARAM + i, param[i]))
            };

            // Digit derivation.
            let mut state = [BabyBear::ZERO; 24];
            state[..PARAM_LEN].copy_from_slice(&param);
            state[5] = bb(TAG_MESSAGE);
            state[6..14].copy_from_slice(&message);
            state[14..21].copy_from_slice(&randomizer);
            specs.push(param_header(Spec::new(K_DIG, state)).set(UID, bb(uid)).set(TX, tx_id));

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
                spec.prev = prev;
                specs.push(spec);
                sponge = perm.permute(sponge);
            }
            let pkh: [BabyBear; 8] = sponge[..8].try_into().unwrap();
            debug_assert_eq!(pkh, pk.hash());

            // Input commitment.
            let commitment = commit_spec(&mut specs, K_CIN, pkh, input.amount, tx_id, perm);
            specs.last_mut().unwrap().carries = total.add(input.amount, 1);
            public_inputs.push(commitment);
            items.push((commitment, [BabyBear::ZERO; 8], true));
        }

        for output in &tx.outputs {
            let pkh = digest_from_bytes(&output.pubkey_hash);
            let commitment = commit_spec(&mut specs, K_COUT, pkh, output.amount, tx_id, perm);
            let nonce = crate::output::nonce_limbs(&output.nonce);
            let spec = specs.last_mut().unwrap();
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
    specs.push(bal);

    // The same order a `BlockBody` publishes them in.
    public_inputs.sort_by_key(|c| digest_to_bytes(*c));
    public_outputs.sort_by_key(|(c, _)| digest_to_bytes(*c));
    if let Some(shape) = shape
        && (public_inputs.len() > shape.inputs || public_outputs.len() > shape.outputs)
    {
        return Err(WitnessError::TooLarge);
    }
    let capacity = shape.map(|s| (s.inputs, s.outputs));
    let (public_outputs, public_nonces) = public_outputs.into_iter().unzip();
    let air = BlockAir::chunk(num_blocks, public_inputs, public_outputs, public_nonces, net, capacity);
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
    let mut acc = [BabyBear::ZERO; AMOUNT_LIMBS];
    let mut acc_top = BabyBear::ZERO;

    for (b, spec) in specs.iter().enumerate() {
        let (rows, _) = air.chip.generate(spec.state);
        let base = b * ROWS;
        let carry: Vec<BabyBear> = rows[OUT_ROW][..24].to_vec();

        // Registers that persist across blocks unless this block sets them.
        if spec.kind == K_DIG {
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
        header.extend(spec.header.iter().filter(|(col, _)| *col != TX && *col != UID && !(PARAM..PARAM + PARAM_LEN).contains(col)));
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
        // Digit lanes: the compress output, 3 bits at a time.
        let lanes: Vec<u32> = (0..LANES).map(|e| (carry[e] + spec.state[e]).value()).collect();

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
            if spec.kind == K_DIG && r <= DIGITS_PER_LANE {
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
}

