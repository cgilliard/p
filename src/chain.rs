//! Chain-state-dependent block processing: resolving a block's inputs and
//! outputs against the real `StateTree`/`UtxoIndex`, applying the
//! resulting updates, and checking the header's claimed roots match what
//! applying the block actually produced -- everything `block::Block`
//! deliberately doesn't do on its own, since it has no access to (or need
//! for) any chain state. See that module's docs for exactly where the
//! line between the two sits.
//!
//! **No balance or authorization check lives here, now or later.** Once
//! `inputs`/`outputs` are bare opaque commitments (see `block`'s docs),
//! there's nothing left in plaintext to check a sum over -- that's
//! permanently the future ZK proof's job, not a placeholder standing in
//! for it.
//!
//! Timestamps must **strictly increase**: every block's `timestamp` is
//! later than its parent's (`Error::TimestampNotAfterParent`). Checked
//! here, in plaintext, by every full node -- it's cheap, and it's what
//! stops a miner backdating the first block of a retarget window to
//! fake a slow window and drag difficulty down (the "timewarp" attack).
//! A light client relying on the recursive proof instead will need the
//! proof to attest the same rule; that's the proof's job on top of this,
//! not instead of it.
//!
//! What this module *does* check is everything structural: does this
//! block chain onto the current tip, does its `timestamp` claim to be
//! further in the future than this node's own clock allows (the one
//! timestamp rule that can *never* move into any proof, recursive or
//! not -- it's about the relationship between a timestamp and whenever
//! *this check* happens to run, not a fact fixed at proving time), does
//! every input resolve to a real, currently-unspent output, does every
//! output avoid colliding with one that's still live, and do the roots
//! that result from applying it match what the header claims.
//!
//! # Atomicity
//!
//! `StateTree` and `UtxoIndex` hold no in-memory state of their own
//! to desync -- every read and write they do goes through a caller-
//! supplied LMDB transaction (see each module's docs). That's what lets
//! `apply_block` update all of them through one shared `heed::RwTxn` and
//! commit them together: if any check fails partway through, the
//! function returns before ever calling `commit`, the transaction is
//! simply dropped, and LMDB aborts it -- every write attempted so far is
//! discarded, with nothing to roll back by hand.
//!
//! `build_block` leans on the exact same mechanism for a different
//! purpose: it runs the identical resolve-and-apply logic `apply_block`
//! uses, through its own write transaction, purely to compute the roots
//! a prospective block *would* produce -- then deliberately never
//! commits. There's no separate "simulate" code path to keep in sync
//! with the real one; it's the same function, just discarded afterward.
//!
//! # Difficulty retargeting
//!
//! Whatever target a `Chain` opens with (`DifficultyConfig::
//! initial_target`, see `Chain::open`) is only ever the *starting*
//! one, not a fixed one -- `Chain` adjusts it over time to keep blocks
//! landing roughly `DifficultyConfig::target_block_time_ms` apart,
//! which is exactly why `Block::validate`/`pow::mine_block` take the
//! target as an explicit parameter rather than assuming a constant
//! (see `block`'s docs). `Chain` tracks two more small pieces of side
//! state for this, on top of the tip header: the currently-active
//! target (`current_target`), and the timestamp of whichever block
//! started the retarget window currently in progress
//! (`window_start_timestamp`).
//!
//! The rule is Bitcoin's own: every `DifficultyConfig::interval`
//! blocks, compare how long that window actually took (real elapsed
//! time, from `timestamp`s already in the applied headers) against
//! how long it was supposed to take, clamp that ratio to
//! `[1/max_adjustment_factor, max_adjustment_factor]` (so one bad
//! window can't swing the target wildly), and scale the target by it
//! (`pow::scale` -- genuine proportional 256-bit arithmetic, not a
//! bit-shift). All four knobs -- the starting target, the window
//! size, the target block time, and the clamp -- are bundled into one
//! `DifficultyConfig` the caller supplies to `Chain::open`, precisely
//! because the right values for a test (fast, cheap to mine, so the
//! suite stays quick) and for an actual run (slower, closer to a real
//! target pace) are never the same numbers -- see
//! `DifficultyConfig::for_tests`.

#![allow(dead_code)]

use crate::recovery::NONCE_LEN;
use crate::block::{Block, BlockBody, BlockHeader, HEADER_LEN, UnprovenBlock, now_millis};
use crate::state_tree::StateTree;
use crate::pow;
use crate::storage::Storage;
use crate::transaction::Transaction;
use crate::utxo::UtxoIndex;
use heed::Database;
use heed::types::Bytes;

/// The `prev_hash` an empty chain's first block must declare -- there's
/// no real prior header to point to, so this stands in for "no parent."
pub const GENESIS_PARENT_HASH: [u8; 32] = [0u8; 32];

/// How far ahead of this node's own clock a block's `timestamp` is
/// allowed to claim to be, in milliseconds -- same order of magnitude
/// as Bitcoin's 2-hour rule. This can never be part of any proof,
/// recursive or otherwise: it's a statement about the relationship
/// between a timestamp and whenever *this particular check* happens to
/// run, not a fact fixed at proving time (see `docs/BLOCK_TODO.md` #3).
/// Every verifier -- full node or light client -- has to check this
/// locally, against its own clock, no matter how much of the rest of
/// chain validity eventually gets folded into a recursive proof.
const MAX_FUTURE_DRIFT_MS: u64 = 2 * 60 * 60 * 1000;

/// The tip's full header, the one thing `Chain` persists in its own
/// `chain_meta` database beyond what `state`/`utxo` already
/// track. Everything else `Chain` needs to know about the tip --
/// its hash, its height -- is derived from this single stored value
/// rather than kept as separate, independently-updated counters, so
/// there's nothing for two pieces of tip metadata to ever drift out of
/// sync with each other.
const TIP_HEADER_KEY: &[u8] = b"tip_header";

/// Every knob `Chain`'s difficulty retargeting needs, bundled into one
/// struct rather than separate positional parameters to `Chain::open`
/// -- partly so adding another knob later doesn't change that
/// signature again, partly so a caller can't accidentally transpose
/// two `u64`s that mean different things. See the module docs for what
/// the rule actually does with these.
#[derive(Clone, Copy, Debug)]
pub struct DifficultyConfig {
    /// The PoW target a brand new chain starts at, before the first
    /// retarget happens. Only matters for a genuinely new chain -- if
    /// this one's already been applied to before, whatever's actually
    /// stored in `chain_meta` wins, same as every other piece of
    /// retargeting state.
    pub initial_target: [u8; 32],
    /// Blocks between difficulty adjustments.
    pub interval: u64,
    /// The real time a window of `interval` blocks is supposed to
    /// take, in **milliseconds**, if mining is keeping pace with the
    /// target. Milliseconds rather than seconds specifically so a test
    /// can set this small (tens of milliseconds) and use genuinely
    /// real elapsed time -- actually sleeping between mined blocks --
    /// without the test suite paying for it in wall-clock seconds; see
    /// `for_tests`.
    pub target_block_time_ms: u64,
    /// How far the actual/expected elapsed-time ratio is allowed to
    /// swing before being clamped, each retarget -- `4` means at most
    /// 4x harder or 4x easier per window. Bitcoin's own value.
    pub max_adjustment_factor: u64,
}

impl DifficultyConfig {
    /// Fast, cheap-to-mine defaults for tests: `block::INITIAL_MAX_HASH`
    /// (the easy target everything else in this crate's test suite is
    /// already built around), a short window, and a millisecond-scale
    /// target block time -- a full retarget window is nominally just
    /// `10 * 9 = 90` milliseconds, fast enough that a test exercising
    /// genuinely real elapsed time (not hand-set `timestamp`s) stays
    /// fast too.
    pub fn for_tests() -> Self {
        DifficultyConfig {
            initial_target: crate::block::INITIAL_MAX_HASH,
            interval: 10,
            target_block_time_ms: 10,
            max_adjustment_factor: 4,
        }
    }
}

/// The currently-active PoW target, the other piece of state `Chain`
/// persists in `chain_meta` beyond the tip header -- `Chain`'s own
/// `initial_target` until the first retarget happens.
const CURRENT_TARGET_KEY: &[u8] = b"current_target";

/// The timestamp of the first block in the retarget window currently in
/// progress -- what the next retarget's elapsed-time measurement is
/// taken from. Updated every time a block lands on a window boundary
/// (`height % RETARGET_INTERVAL == 0`), including height `0`, which is
/// what seeds this without needing a separate genesis special-case.
const WINDOW_START_TIMESTAMP_KEY: &[u8] = b"window_start_timestamp";

/// `chain_meta` key: the height of the block a fast sync started this
/// chain at (u64 BE), if one did -- nothing below it is stored but the
/// genesis block, so no reorg reaches below it (`reorg_floor`).
const SYNC_BASE_KEY: &[u8] = b"sync_base";

/// Database name: every applied block, in full (`Block::to_bytes`),
/// keyed by its own header hash. The one place this module keeps
/// actual block data around after applying it -- needed so a reorg
/// can look back at what a block it's unwinding actually contained
/// (`body.outputs`' commitments, specifically), and eventually so a
/// fork-choice comparison has real headers to walk back through.
const BLOCKS_DB: &str = "blocks";

/// Database name: `UndoData` for every applied block, keyed by the
/// same header hash as `BLOCKS_DB`. See `UndoData`'s own docs for why
/// this has to be captured *at apply time*, not reconstructed later.
const BLOCK_UNDO_DB: &str = "block_undo";

/// Database name: cumulative chain work (`pow::work_for_target`,
/// summed via `pow::add256`) up to and including each stored block,
/// keyed by the same header hash as `BLOCKS_DB`. Tracked for *every*
/// accepted block, not just the active chain's -- fork-choice needs
/// to compare a side branch's total work against the active chain's
/// before either has been touched, so this can't be computed lazily
/// only when a reorg is already underway.
const BLOCK_WORK_DB: &str = "block_work";

/// Database name: hashes of blocks known to be invalid (value unused),
/// recorded when a reorg replay fails on a block-level fault (see
/// `Error::is_block_fault`). Without this, a side branch whose stored
/// blocks merely *look* heavier would retrigger the same doomed reorg
/// every time another block extending it arrived. Persisted rather
/// than in-memory: the bad blocks themselves stay in `BLOCKS_DB`
/// across restarts, so the verdict on them has to as well.
const INVALID_BLOCKS_DB: &str = "invalid_blocks";

/// Database name: the `RetargetState` in effect right *after* each
/// stored block, keyed by the same header hash as `BLOCKS_DB`. Tracked
/// for every accepted block, active or side branch, for the same reason
/// as `BLOCK_WORK_DB`: a side-branch block has to be checked against
/// the target *its own branch's* history implies, which can differ from
/// the active chain's once the two straddle a retarget-window boundary.
const BLOCK_RETARGET_DB: &str = "block_retarget";

/// Database name: an index of every stored block by height -- key is
/// `height` (big-endian) followed by the header hash, value unused --
/// so pruning can find everything below a height without scanning
/// `BLOCKS_DB`. See `Chain::prune`.
const BLOCK_HEIGHTS_DB: &str = "block_heights";

/// Database name: the active chain by height -- key is `height`
/// (big-endian), value the active block's header hash. Maintained as
/// blocks are applied and unwound, so it always describes exactly the
/// active chain. What lets a peer ask for "your block at height N"
/// (sync), and what `prune` uses to tell active-chain blocks (kept
/// forever) from side-branch ones (dropped once out of reach).
const ACTIVE_HEIGHTS_DB: &str = "active_heights";

/// Every output the active chain has created, spent or not: commitment
/// -> its block's height (u64 BE) ‖ its recovery nonce. Written when a
/// block applies, removed only when that block is unwound -- spending
/// doesn't touch it. What a wallet checks its outputs' nonces against,
/// and what recovery scans (`docs/RECOVERY.md`).
const OUTPUT_INDEX_DB: &str = "output_index";

/// How many blocks the orphan pool holds before evicting the oldest --
/// a bound on how much memory a peer can make this node spend on
/// blocks it can't place yet. Same number Bitcoin Core uses for its
/// orphan *transaction* pool; not calibrated against anything here.
const MAX_ORPHANS: usize = 100;

#[derive(Debug)]
pub enum Error {
    Storage(crate::storage::Error),
    Heed(heed::Error),
    State(crate::state_tree::Error),
    Utxo(crate::utxo::Error),
    /// The on-disk tip entry wasn't a validly encoded hash.
    Corrupt(&'static str),
    /// The block failed `Block::validate()` -- unsound on its own terms,
    /// before chain state even enters the picture.
    InvalidBlock,
    /// `header.prev_hash` doesn't match this chain's current tip (or
    /// `GENESIS_PARENT_HASH`, for an empty chain).
    WrongParent,
    /// `header.height` isn't exactly one more than the current tip's
    /// (or `0`, for an empty chain). Catches a bug or forged claim
    /// independently of `WrongParent` -- see `block::HEADER_LEN`'s docs
    /// on why `height` is trustworthy data in the first place.
    WrongHeight,
    /// `header.timestamp` claims to be further ahead of this node's own
    /// clock than `MAX_FUTURE_DRIFT_MS` allows.
    TimestampTooFarInFuture,
    /// An input commitment doesn't resolve to a currently unspent output.
    UnresolvedInput([u8; 32]),
    /// An output's commitment collides with one that's already live
    /// (created, and not yet spent).
    DuplicateOutput([u8; 32]),
    /// A fast sync's snapshot was refused: why.
    Snapshot(&'static str),
    /// Applying the body produced a state root different from the one the
    /// header claims.
    StateRootMismatch,
    /// Applying the body left a different number of outputs than the
    /// header claims.
    OutputCountMismatch,
    /// One of the transactions handed to `build_block` failed its own
    /// `Transaction::verify()` -- the index is its position in the slice
    /// that was passed in.
    InvalidTransaction(usize),
    /// A transaction handed to `build_block` has more inputs or outputs
    /// than one chunk holds (`prover::CHUNK_SHAPE`) -- a consensus limit.
    TransactionTooLarge,
    /// A side-branch block's own header is unsound -- `Block::validate`
    /// against the target its own branch's history implies failed.
    InvalidSideBranchBlock,
    /// A side-branch block's claimed `prev_hash`/`height` doesn't
    /// match the block it claims to extend.
    InvalidSideBranchLineage,
    /// A competing chain (or a block that could only ever belong to
    /// one) would fork off the active chain further back than
    /// `max_reorg_depth` allows -- see `Chain::open`'s docs.
    ReorgTooDeep,
    /// The block is, or descends from, one already recorded in
    /// `INVALID_BLOCKS_DB`.
    KnownInvalidBlock,
    /// An orphan's proof of work doesn't even meet the active chain's
    /// current target relaxed by `max_adjustment_factor` -- see
    /// `Chain::orphan_target`. Not a verdict on the block (its real
    /// target is unknowable without its parent), just a refusal to
    /// spend pool space on it; it can always be sent again once its
    /// parent is known.
    OrphanPowTooWeak,
    /// `header.timestamp` isn't strictly later than its parent's.
    TimestampNotAfterParent,
    /// A block claiming to be the first one (`prev_hash` is
    /// `GENESIS_PARENT_HASH`) that isn't this chain's genesis block -- or,
    /// at `Chain::open`, stored data whose first block isn't.
    WrongGenesis,
    /// `build_block` was handed more than fits in `block::MAX_BLOCK_BYTES`.
    BlockTooLarge,
}

impl Error {
    /// Whether this error condemns the block itself -- as opposed to a
    /// storage failure, which says nothing about the block, or
    /// `TimestampTooFarInFuture`, which may stop being true just by
    /// waiting. Only these get a block recorded in `INVALID_BLOCKS_DB`.
    fn is_block_fault(&self) -> bool {
        matches!(
            self,
            Error::InvalidBlock
                | Error::WrongParent
                | Error::WrongHeight
                | Error::UnresolvedInput(_)
                | Error::DuplicateOutput(_)
                | Error::StateRootMismatch
                | Error::OutputCountMismatch
                | Error::TimestampNotAfterParent
                | Error::WrongGenesis
        )
    }
}

impl From<crate::storage::Error> for Error {
    fn from(e: crate::storage::Error) -> Self {
        Error::Storage(e)
    }
}

impl From<heed::Error> for Error {
    fn from(e: heed::Error) -> Self {
        Error::Heed(e)
    }
}

impl From<crate::state_tree::Error> for Error {
    fn from(e: crate::state_tree::Error) -> Self {
        Error::State(e)
    }
}


impl From<crate::utxo::Error> for Error {
    fn from(e: crate::utxo::Error) -> Self {
        Error::Utxo(e)
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Storage(e) => write!(f, "storage error: {e}"),
            Error::Heed(e) => write!(f, "LMDB error: {e}"),
            Error::State(e) => write!(f, "state tree error: {e}"),
            Error::Utxo(e) => write!(f, "utxo error: {e}"),
            Error::Corrupt(msg) => write!(f, "corrupt chain metadata: {msg}"),
            Error::InvalidBlock => write!(f, "block failed its own validate()"),
            Error::WrongParent => write!(f, "block does not chain onto the current tip"),
            Error::WrongHeight => write!(f, "block's height is not exactly one more than the current tip's"),
            Error::TimestampTooFarInFuture => write!(f, "header timestamp is too far ahead of this node's clock"),
            Error::UnresolvedInput(c) => write!(f, "input {} does not resolve to a live unspent output", hex(c)),
            Error::DuplicateOutput(c) => write!(f, "output {} collides with a still-live output", hex(c)),
            Error::Snapshot(why) => write!(f, "snapshot refused: {why}"),
            Error::StateRootMismatch => write!(f, "header's state_root does not match the result of applying the body"),
            Error::OutputCountMismatch => write!(f, "header's output_count does not match the result of applying the body"),
            Error::InvalidTransaction(i) => write!(f, "transaction at index {i} failed verify()"),
            Error::TransactionTooLarge => write!(f, "a transaction has more inputs or outputs than one chunk holds"),
            Error::InvalidSideBranchBlock => write!(f, "side-branch block failed validate() against the active target"),
            Error::InvalidSideBranchLineage => write!(f, "side-branch block's prev_hash/height doesn't match its claimed parent"),
            Error::ReorgTooDeep => write!(f, "competing chain's common ancestor is beyond max_reorg_depth"),
            Error::KnownInvalidBlock => write!(f, "block is, or descends from, a block already known to be invalid"),
            Error::OrphanPowTooWeak => write!(f, "orphan's proof of work is too weak to be worth pooling"),
            Error::TimestampNotAfterParent => write!(f, "header timestamp is not later than its parent's"),
            Error::WrongGenesis => write!(f, "block is not this chain's genesis block"),
            Error::BlockTooLarge => write!(f, "transactions don't fit in the maximum block size"),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

/// `resolve_and_apply`'s result: the resulting `(state_root,
/// output_count)`, every spent input's `(commitment, position)` from
/// before it was removed, and (if asked for) each chunk's state
/// transition witness -- see that method's docs.
type ResolveResult = ([u8; 32], u64, Vec<([u8; 32], u64)>, Vec<crate::aggregate::ChunkTransition>);

/// Which of a body's inputs and outputs each chunk holds, as indices
/// into its lists (body order within each chunk).
type ChunkIndices = Vec<(Vec<usize>, Vec<usize>)>;

/// `BLOCK_HEIGHTS_DB`'s key for a block: big-endian height first, so
/// keys sort by height, then the hash to keep same-height blocks apart.
fn height_key(height: u64, hash: [u8; 32]) -> [u8; 40] {
    let mut out = [0u8; 40];
    out[..8].copy_from_slice(&height.to_be_bytes());
    out[8..].copy_from_slice(&hash);
    out
}

fn hex(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Difficulty retargeting's state as of right after some block: the
/// target the *next* block must meet, and the timestamp the retarget
/// window in progress started at. What `chain_meta`'s
/// `CURRENT_TARGET_KEY`/`WINDOW_START_TIMESTAMP_KEY` hold for the
/// active tip, and what `BLOCK_RETARGET_DB` holds for every stored block.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RetargetState {
    target: [u8; 32],
    window_start_timestamp: u64,
}

impl RetargetState {
    fn to_bytes(self) -> [u8; 40] {
        let mut out = [0u8; 40];
        out[..32].copy_from_slice(&self.target);
        out[32..].copy_from_slice(&self.window_start_timestamp.to_be_bytes());
        out
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != 40 {
            return Err(Error::Corrupt("stored retarget state was not 40 bytes"));
        }
        Ok(RetargetState {
            target: bytes[..32].try_into().unwrap(),
            window_start_timestamp: u64::from_be_bytes(bytes[32..].try_into().unwrap()),
        })
    }

    /// The state right after `header` lands on top of `self` -- the
    /// retargeting rule itself, as a pure function of nothing but the
    /// previous state and the new header, so it can be run for any
    /// branch, not just the active one. Two things can happen, and at
    /// most one ever does for a given block (see the module docs): if
    /// `header` opens a new window, its timestamp becomes the new
    /// `window_start_timestamp`; if it closes one, the window's actual
    /// elapsed time, clamped to within `max_adjustment_factor` of what
    /// was expected, becomes the ratio `target` is scaled by (Bitcoin's
    /// own rule -- see the module docs).
    fn after(self, config: &DifficultyConfig, header: &BlockHeader) -> Self {
        let (target, window_start_timestamp) = next_retarget(config, (self.target, self.window_start_timestamp), header.height, header.timestamp);
        RetargetState { target, window_start_timestamp }
    }
}

/// The retarget rule, on its own: the `(target, window start)` in effect
/// after a block at `height` with `timestamp`, given those before it. A
/// window starts at every multiple of `config.interval`; at a window's
/// last block the target scales by its elapsed over expected time,
/// clamped to within `max_adjustment_factor` (`pow::scale`). Shared with
/// the chain-proof circuit (`chain_step`), which proves the same rule.
pub(crate) fn next_retarget(config: &DifficultyConfig, (target, window_start): ([u8; 32], u64), height: u64, timestamp: u64) -> ([u8; 32], u64) {
    let interval = config.interval;
    let window_start = if height.is_multiple_of(interval) { timestamp } else { window_start };
    let mut target = target;
    if (height + 1).is_multiple_of(interval) {
        let elapsed = timestamp.saturating_sub(window_start);
        let expected = config.target_block_time_ms * (interval - 1);
        let factor = config.max_adjustment_factor;
        let clamped_elapsed = elapsed.clamp(expected / factor, expected * factor);
        target = pow::scale(target, clamped_elapsed, expected);
    }
    (target, window_start)
}

/// Everything `Chain::unwind_tip` needs to reverse exactly what
/// `apply_block` did for one block, snapshotted *before* that block's
/// own mutations ran. None of this is recoverable any other way once
/// those mutations have happened: the tip header and retargeting
/// state (`current_target`/`window_start_timestamp`) get overwritten
/// in place, not appended, and a spent input's original position
/// is deleted from `utxo` the moment it's spent -- the one instant
/// `resolve_and_apply` has it in hand is the only chance to record it.
/// This is genuinely the same "undo data" Bitcoin Core keeps per
/// block, for the exact same reason.
struct UndoData {
    /// The tip header in effect immediately before this block was
    /// applied -- `None` if this block was the very first ever
    /// applied (there was no tip at all yet).
    prev_tip_header: Option<BlockHeader>,
    prev_current_target: [u8; 32],
    prev_window_start_timestamp: u64,
    /// `(commitment, position)` for every input this block spent.
    spent_inputs: Vec<([u8; 32], u64)>,
}

impl UndoData {
    fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        match &self.prev_tip_header {
            Some(header) => {
                out.push(1);
                out.extend_from_slice(&header.to_bytes());
            }
            None => out.push(0),
        }
        out.extend_from_slice(&self.prev_current_target);
        out.extend_from_slice(&self.prev_window_start_timestamp.to_be_bytes());
        out.extend_from_slice(&(self.spent_inputs.len() as u32).to_be_bytes());
        for (commitment, position) in &self.spent_inputs {
            out.extend_from_slice(commitment);
            out.extend_from_slice(&position.to_be_bytes());
        }
        out
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self> {
        fn take<'a>(bytes: &'a [u8], offset: &mut usize, len: usize) -> Result<&'a [u8]> {
            let slice = bytes.get(*offset..*offset + len).ok_or(Error::Corrupt("undo data was truncated"))?;
            *offset += len;
            Ok(slice)
        }

        let mut offset = 0;
        let has_prev_tip_header = take(bytes, &mut offset, 1)?[0];
        let prev_tip_header = match has_prev_tip_header {
            0 => None,
            1 => {
                let header_bytes = take(bytes, &mut offset, HEADER_LEN)?;
                Some(BlockHeader::from_bytes(header_bytes).map_err(|_| Error::Corrupt("undo data's tip header was corrupt"))?)
            }
            _ => return Err(Error::Corrupt("undo data's tip-header flag was neither 0 nor 1")),
        };

        let prev_current_target: [u8; 32] = take(bytes, &mut offset, 32)?.try_into().unwrap();
        let prev_window_start_timestamp = u64::from_be_bytes(take(bytes, &mut offset, 8)?.try_into().unwrap());
        let count = u32::from_be_bytes(take(bytes, &mut offset, 4)?.try_into().unwrap());

        let mut spent_inputs = Vec::with_capacity(count as usize);
        for _ in 0..count {
            let commitment: [u8; 32] = take(bytes, &mut offset, 32)?.try_into().unwrap();
            let position = u64::from_be_bytes(take(bytes, &mut offset, 8)?.try_into().unwrap());
            spent_inputs.push((commitment, position));
        }

        if offset != bytes.len() {
            return Err(Error::Corrupt("undo data had trailing bytes"));
        }

        Ok(UndoData {
            prev_tip_header,
            prev_current_target,
            prev_window_start_timestamp,
            spent_inputs,
        })
    }
}

/// Where a candidate chain diverges from the active one -- what
/// `find_fork_point` returns, and everything `accept_block`'s reorg
/// path needs to actually carry one out.
struct ForkPoint {
    /// How many times `unwind_tip` must be called to bring the active
    /// chain back to the common ancestor.
    unwind_count: u64,
    /// The candidate chain's own blocks, strictly after the common
    /// ancestor, in apply order (oldest first) -- what gets replayed
    /// through `apply_block_in_txn` once the active chain has been
    /// unwound that far.
    replay: Vec<Block>,
}

/// What `accept_block` actually did with a block -- distinct outcomes
/// rather than just success/failure, since "accepted, but not applied
/// yet" is a perfectly normal, expected result, not an error.
#[derive(Debug, PartialEq, Eq)]
pub enum AcceptOutcome {
    /// Extended the active chain directly.
    Applied,
    /// Stored as a side branch -- its chain doesn't (yet) have more
    /// work than the active one.
    StoredAsSideBranch,
    /// Stored as a side branch whose chain turned out to have more
    /// work than the active one, so a reorg happened: `unwound` blocks
    /// were rolled back off the active chain, `applied` blocks from
    /// the winning branch were replayed forward, atomically (see
    /// `accept_block`'s docs).
    Reorged { unwound: u64, applied: u64 },
    /// This block's parent isn't known at all -- held in the orphan
    /// pool, pending that parent (or an ancestor of it) arriving. See
    /// `Chain::try_connect_orphans`.
    Orphaned,
    /// Already stored (active chain or side branch), or already
    /// waiting in the orphan pool -- nothing was done.
    AlreadyKnown,
}

/// Read-only access to stored blocks and the active chain, separate from
/// `Chain` -- so another thread (the network's) can serve blocks to peers
/// and see where the tip is, while `Chain` itself stays owned by whoever
/// applies blocks. Cheap to clone. Sees exactly what's committed.
#[derive(Clone)]
pub struct BlockReader {
    storage: Storage,
    meta: Database<Bytes, Bytes>,
    blocks: Database<Bytes, Bytes>,
    active_heights: Database<Bytes, Bytes>,
}

impl BlockReader {
    pub fn open(storage: &Storage) -> Result<Self> {
        Ok(BlockReader {
            storage: storage.clone(),
            meta: storage.database("chain_meta")?,
            blocks: storage.database(BLOCKS_DB)?,
            active_heights: storage.database(ACTIVE_HEIGHTS_DB)?,
        })
    }

    /// A stored block's encoding (`Block::to_bytes`), active chain or
    /// side branch.
    pub fn block_bytes(&self, hash: [u8; 32]) -> Result<Option<Vec<u8>>> {
        let rtxn = self.storage.read_txn()?;
        Ok(self.blocks.get(&rtxn, &hash)?.map(|bytes| bytes.to_vec()))
    }

    /// `len` bytes of a stored block's encoding starting at `start`
    /// (fewer if it ends first), plus the encoding's total size -- one
    /// chunk's worth, without copying out the whole (up to megabytes)
    /// block. `None` if the block isn't stored or `start` is past its end.
    pub fn block_range(&self, hash: [u8; 32], start: usize, len: usize) -> Result<Option<(usize, Vec<u8>)>> {
        let rtxn = self.storage.read_txn()?;
        let Some(bytes) = self.blocks.get(&rtxn, &hash)? else {
            return Ok(None);
        };
        if start >= bytes.len() {
            return Ok(None);
        }
        let end = start.saturating_add(len).min(bytes.len());
        Ok(Some((bytes.len(), bytes[start..end].to_vec())))
    }

    pub fn has_block(&self, hash: [u8; 32]) -> Result<bool> {
        let rtxn = self.storage.read_txn()?;
        Ok(self.blocks.get(&rtxn, &hash)?.is_some())
    }

    /// The active chain's block hash at `height`, if it's that tall.
    pub fn active_hash_at(&self, height: u64) -> Result<Option<[u8; 32]>> {
        let rtxn = self.storage.read_txn()?;
        match self.active_heights.get(&rtxn, &height.to_be_bytes())? {
            Some(bytes) => Ok(Some(
                bytes.try_into().map_err(|_| Error::Corrupt("active height entry was not 32 bytes"))?,
            )),
            None => Ok(None),
        }
    }

    /// The active tip's `(height, hash)`, or `None` for an empty chain.
    pub fn tip(&self) -> Result<Option<(u64, [u8; 32])>> {
        let rtxn = self.storage.read_txn()?;
        match self.meta.get(&rtxn, TIP_HEADER_KEY)? {
            Some(bytes) => {
                let header = BlockHeader::from_bytes(bytes).map_err(|_| Error::Corrupt("tip header was corrupt"))?;
                Ok(Some((header.height, header.hash())))
            }
            None => Ok(None),
        }
    }
}

/// Whether `outcome` means the block is now stored -- on the active
/// chain or a side branch -- so anything waiting on it can connect too.
fn is_connected(outcome: &AcceptOutcome) -> bool {
    matches!(
        outcome,
        AcceptOutcome::Applied | AcceptOutcome::StoredAsSideBranch | AcceptOutcome::Reorged { .. }
    )
}

/// A full node's chain state: the real `StateTree` and `UtxoIndex`,
/// plus the metadata none of those three know about on their own -- which
/// header is the current tip, and at what height.
/// The active chain at one moment, for the wallet (`Chain::view`).
pub struct ChainState<'a> {
    chain: &'a Chain,
    txn: heed::RoTxn<'a>,
}

/// An output the active chain created: where, and its recovery nonce.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OutputRecord {
    pub commitment: [u8; 32],
    pub height: u64,
    pub nonce: [u8; NONCE_LEN],
}

impl OutputRecord {
    fn decode(commitment: [u8; 32], bytes: &[u8]) -> Result<Self> {
        if bytes.len() != 8 + NONCE_LEN {
            return Err(Error::Corrupt("output index entry was the wrong size"));
        }
        Ok(OutputRecord {
            commitment,
            height: u64::from_be_bytes(bytes[..8].try_into().unwrap()),
            nonce: bytes[8..].try_into().unwrap(),
        })
    }
}

impl crate::wallet::ChainView for ChainState<'_> {
    fn tip_height(&self) -> u64 {
        self.chain.height(&self.txn).ok().flatten().unwrap_or(0)
    }

    fn is_unspent(&self, commitment: &[u8; 32]) -> bool {
        self.chain.is_unspent(&self.txn, commitment).unwrap_or(false)
    }

    fn output_record(&self, commitment: &[u8; 32]) -> Option<(u64, [u8; NONCE_LEN])> {
        let record = self.chain.output_record(&self.txn, commitment).ok()??;
        Some((record.height, record.nonce))
    }

    fn for_each_output(&self, f: &mut dyn FnMut([u8; 32], u64, [u8; NONCE_LEN], bool)) -> bool {
        self.chain
            .for_each_output(&self.txn, |r, unspent| f(r.commitment, r.height, r.nonce, unspent))
            .is_ok()
    }

    fn has_full_history(&self) -> bool {
        matches!(self.chain.sync_base(&self.txn), Ok(None))
    }
}

/// Read-only access to what fast-syncing peers ask for -- the state as of
/// a recent block, in pieces (`snapshot`), and the rest of what the chain
/// proof of that block attests -- for the network's thread, like
/// `BlockReader`. Serves any active-chain block from the reorg floor up:
/// the state then is the current tree with every later block undone
/// (their undo data says what they spent), computed on the fly, not
/// stored.
#[derive(Clone)]
pub struct StateReader {
    storage: Storage,
    state: std::sync::Arc<StateTree>,
    meta: Database<Bytes, Bytes>,
    blocks: Database<Bytes, Bytes>,
    block_undo: Database<Bytes, Bytes>,
    block_work: Database<Bytes, Bytes>,
    block_retarget: Database<Bytes, Bytes>,
    active_heights: Database<Bytes, Bytes>,
    output_index: Database<Bytes, Bytes>,
    /// The last view computed: for which block, at which tip.
    cache: std::sync::Arc<std::sync::Mutex<Option<CachedView>>>,
}

/// A state view (`StateReader::as_of`): the block it's as of, the tip it
/// was computed at, and the view.
type CachedView = ([u8; 32], [u8; 32], std::sync::Arc<crate::state_tree::AsOf>);

impl StateReader {
    pub fn open(storage: &Storage) -> Result<Self> {
        Ok(StateReader {
            storage: storage.clone(),
            state: std::sync::Arc::new(StateTree::open(storage)?),
            meta: storage.database("chain_meta")?,
            blocks: storage.database(BLOCKS_DB)?,
            block_undo: storage.database(BLOCK_UNDO_DB)?,
            block_work: storage.database(BLOCK_WORK_DB)?,
            block_retarget: storage.database(BLOCK_RETARGET_DB)?,
            active_heights: storage.database(ACTIVE_HEIGHTS_DB)?,
            output_index: storage.database(OUTPUT_INDEX_DB)?,
            cache: Default::default(),
        })
    }

    fn header(&self, txn: &heed::RoTxn, hash: [u8; 32]) -> Result<Option<BlockHeader>> {
        match self.blocks.get(txn, &hash)? {
            Some(bytes) => Ok(Some(
                BlockHeader::from_bytes(&bytes[..HEADER_LEN.min(bytes.len())]).map_err(|_| Error::Corrupt("a stored block was corrupt"))?,
            )),
            None => Ok(None),
        }
    }

    /// The active tip's header, and `hash`'s if it's on the active chain.
    fn active(&self, txn: &heed::RoTxn, hash: [u8; 32]) -> Result<Option<(BlockHeader, BlockHeader)>> {
        let Some(header) = self.header(txn, hash)? else {
            return Ok(None);
        };
        if self.active_heights.get(txn, &header.height.to_be_bytes())? != Some(&hash[..]) {
            return Ok(None);
        }
        let tip = match self.meta.get(txn, TIP_HEADER_KEY)? {
            Some(bytes) => BlockHeader::from_bytes(bytes).map_err(|_| Error::Corrupt("stored tip header was corrupt"))?,
            None => return Ok(None),
        };
        Ok(Some((tip, header)))
    }

    /// What the chain proof of active-chain block `hash` attests besides
    /// its header, if this node still has it.
    pub fn sync_point(&self, hash: [u8; 32]) -> Result<Option<crate::snapshot::SyncPoint>> {
        let rtxn = self.storage.read_txn()?;
        if self.active(&rtxn, hash)?.is_none() {
            return Ok(None);
        }
        let (Some(work), Some(retarget)) = (self.block_work.get(&rtxn, &hash)?, self.block_retarget.get(&rtxn, &hash)?) else {
            return Ok(None);
        };
        let retarget = RetargetState::from_bytes(retarget)?;
        Ok(Some(crate::snapshot::SyncPoint {
            target: retarget.target,
            window_start: retarget.window_start_timestamp,
            work: work.try_into().map_err(|_| Error::Corrupt("stored chain work was not 32 bytes"))?,
        }))
    }

    /// The state as of active-chain block `hash`, from the current tree:
    /// `None` if it's not on the active chain, or too old to undo to.
    fn as_of(&self, txn: &heed::RoTxn, hash: [u8; 32]) -> Result<Option<std::sync::Arc<crate::state_tree::AsOf>>> {
        let Some((tip, header)) = self.active(txn, hash)? else {
            return Ok(None);
        };
        let tip_hash = tip.hash();
        if let Some((at, cached_tip, as_of)) = &*self.cache.lock().unwrap()
            && *at == hash
            && *cached_tip == tip_hash
        {
            return Ok(Some(as_of.clone()));
        }
        let mut as_of = crate::state_tree::AsOf {
            count: header.output_count,
            ..Default::default()
        };
        for height in header.height + 1..=tip.height {
            let Some(block) = self.active_heights.get(txn, &height.to_be_bytes())? else {
                return Ok(None);
            };
            let Some(undo) = self.block_undo.get(txn, block)? else {
                return Ok(None);
            };
            for (commitment, position) in UndoData::from_bytes(undo)?.spent_inputs {
                if position < as_of.count {
                    let record = self.output_index.get(txn, &commitment)?.ok_or(Error::Corrupt("a spent output's record is missing"))?;
                    let record = OutputRecord::decode(commitment, record)?;
                    as_of.restored.insert(position, (commitment, record.nonce));
                }
            }
        }
        let as_of = std::sync::Arc::new(as_of);
        *self.cache.lock().unwrap() = Some((hash, tip_hash, as_of.clone()));
        Ok(Some(as_of))
    }

    /// Piece `(level, index)` of the state as of active-chain block `hash`
    /// (`snapshot`), if this node can serve it.
    pub fn piece(&self, hash: [u8; 32], level: usize, index: u64) -> Result<Option<Vec<u8>>> {
        use crate::snapshot::{LEAF_LEVEL, child_level};
        if !crate::snapshot::is_piece(level, index) {
            return Ok(None);
        }
        let rtxn = self.storage.read_txn()?;
        let Some(as_of) = self.as_of(&rtxn, hash)? else {
            return Ok(None);
        };
        if level == LEAF_LEVEL {
            let entries = self.state.unspent_as_of(&rtxn, &as_of, index << level, (index + 1) << level)?;
            return Ok(Some(crate::snapshot::encode_leaves(index, &entries)));
        }
        let below = child_level(level);
        let children = (0..1u64 << (level - below))
            .map(|j| self.state.node_as_of(&rtxn, &as_of, below, (index << (level - below)) + j))
            .collect::<std::result::Result<Vec<_>, _>>()?;
        Ok(Some(crate::snapshot::encode_inner(&children)))
    }
}

pub struct Chain {
    storage: Storage,
    /// Every output ever created, by position: commitment while unspent,
    /// then spent (`state_tree`).
    state: StateTree,
    utxo: UtxoIndex,
    meta: Database<Bytes, Bytes>,
    blocks: Database<Bytes, Bytes>,
    block_undo: Database<Bytes, Bytes>,
    block_work: Database<Bytes, Bytes>,
    invalid_blocks: Database<Bytes, Bytes>,
    block_retarget: Database<Bytes, Bytes>,
    block_heights: Database<Bytes, Bytes>,
    active_heights: Database<Bytes, Bytes>,
    output_index: Database<Bytes, Bytes>,
    /// The one block allowed to have no parent, if this chain has a
    /// fixed one -- see `Chain::open`.
    genesis_hash: Option<[u8; 32]>,
    /// When set, every block after the first must carry its parent's chain
    /// proof (`chain_step`), checked against the parent as this chain
    /// records it. Set by nodes (`require_chain_proofs`); off for tests
    /// about other things.
    chain_proofs: Option<crate::chain_step::ChainVerifier>,
    /// Whether blocks' proofs are verified -- always, except in tests that
    /// opt out (`skip_proof_checks`) because they're about something else.
    check_proofs: bool,
    difficulty: DifficultyConfig,
    /// How many blocks a reorg is ever allowed to unwind -- see
    /// `Chain::open`'s docs. Also how far back stored blocks are kept
    /// at all; see `prune`.
    max_reorg_depth: u64,
    /// Blocks whose parent isn't known at all yet, each with its own
    /// header hash, oldest first -- purely in-memory, not persisted.
    /// This is inherently about a transient "still waiting on the
    /// network" state; if this process restarts, there's nothing to
    /// resume, the orphan would just arrive again (or get re-requested)
    /// the same way it did the first time. A plain `Vec` rather than a
    /// map keyed by parent: it never holds more than `max_orphans`
    /// entries, so a linear scan is cheap, and arrival order is exactly
    /// what eviction needs.
    orphans: Vec<([u8; 32], Block)>,
    /// `MAX_ORPHANS`, as a field only so tests can shrink it.
    max_orphans: usize,
}

impl Chain {
    /// Open (creating if absent) a chain's full state within the given
    /// storage context, retargeting according to `difficulty` (see
    /// `DifficultyConfig`'s docs -- in particular, why the right
    /// values for a test and for an actual run are never the same
    /// numbers). `max_reorg_depth` is the deepest a reorg is ever
    /// allowed to unwind, in blocks -- deeper competing chains are
    /// refused outright (`Error::ReorgTooDeep`) rather than attempted
    /// (see `docs/BLOCK_TODO.md` on why: resolving a deeper divergence
    /// correctly needs a resync-from-genesis fallback this crate
    /// doesn't have yet). Like `difficulty`, the right value for a
    /// test (small, so the "too deep" path is actually exercisable
    /// without mining hundreds of blocks) and for an actual run
    /// (1000, say) are never the same number.
    ///
    /// `genesis`, if given, is this chain's fixed first block: applied
    /// right away if the chain is empty, and from then on the only block
    /// ever accepted at height 0 (`Error::WrongGenesis` for any other) --
    /// so every node on a network starts from the same block, and can't
    /// be fed a wholly different chain. Stored data whose first block
    /// isn't `genesis` (left over from a different network, say) fails
    /// to open with `Error::WrongGenesis`. `None` means no fixed first
    /// block -- for tests, which build their own chains from scratch.
    pub fn open(
        storage: &Storage,
        difficulty: DifficultyConfig,
        max_reorg_depth: u64,
        genesis: Option<&Block>,
    ) -> Result<Self> {
        let state = StateTree::open(storage)?;
        let utxo = UtxoIndex::open(storage)?;
        let meta = storage.database("chain_meta")?;
        let blocks = storage.database(BLOCKS_DB)?;
        let block_undo = storage.database(BLOCK_UNDO_DB)?;
        let block_work = storage.database(BLOCK_WORK_DB)?;
        let invalid_blocks = storage.database(INVALID_BLOCKS_DB)?;
        let block_retarget = storage.database(BLOCK_RETARGET_DB)?;
        let block_heights = storage.database(BLOCK_HEIGHTS_DB)?;
        let active_heights = storage.database(ACTIVE_HEIGHTS_DB)?;
        let output_index = storage.database(OUTPUT_INDEX_DB)?;
        let mut chain = Chain {
            storage: storage.clone(),
            state,
            utxo,
            meta,
            blocks,
            block_undo,
            block_work,
            invalid_blocks,
            block_retarget,
            block_heights,
            active_heights,
            output_index,
            genesis_hash: genesis.map(|g| g.header.hash()),
            chain_proofs: None,
            check_proofs: true,
            difficulty,
            max_reorg_depth,
            orphans: Vec::new(),
            max_orphans: MAX_ORPHANS,
        };

        if let Some(genesis) = genesis {
            let rtxn = storage.read_txn()?;
            let first = chain.active_heights.get(&rtxn, &0u64.to_be_bytes())?.map(|h| h.to_vec());
            drop(rtxn);
            match first {
                None => chain.apply_block(genesis)?,
                Some(hash) if hash[..] == genesis.header.hash()[..] => {}
                Some(_) => return Err(Error::WrongGenesis),
            }
        }
        Ok(chain)
    }

    /// Stop verifying blocks' proofs -- for tests about forks, retargeting,
    /// or sync, whose blocks carry placeholder proofs, since real ones take
    /// seconds each to make. Doesn't exist outside tests.
    #[cfg(test)]
    pub fn skip_proof_checks(&mut self) {
        self.check_proofs = false;
    }

    /// `Block::validate`: every structural rule, then the proof -- unless
    /// proofs are being skipped, or this is the chain's fixed genesis,
    /// which is trusted by consensus (it's hardcoded) and couldn't prove
    /// anything anyway: its empty body claims no reward.
    fn block_is_valid(&self, txn: &heed::RoTxn, block: &Block, target: &[u8; 32]) -> Result<bool> {
        if !block.validate_structure(target) {
            return Ok(false);
        }
        let is_genesis = self.genesis_hash == Some(block.header.hash());
        if !self.check_proofs || is_genesis {
            return Ok(true);
        }
        let parent = self.parent_state(txn, block.header.prev_hash)?;
        if !block.body.proof_is_valid(&block.state_change(parent)) {
            return Ok(false);
        }
        // The parent's chain proof: that the parent is the tip of a valid
        // chain, as this chain records it.
        if let Some(verifier) = &self.chain_proofs
            && block.header.prev_hash != GENESIS_PARENT_HASH
        {
            let parent_tip = self.chain_tip(txn, block.header.prev_hash)?;
            return Ok(verifier.verify(&parent_tip, &block.body.chain_proof));
        }
        Ok(true)
    }

    /// The `(state_root, output_count)` after the block `prev_hash` --
    /// the state a block extending it starts from.
    fn parent_state(&self, txn: &heed::RoTxn, prev_hash: [u8; 32]) -> Result<([u8; 32], u64)> {
        if prev_hash == GENESIS_PARENT_HASH {
            return Ok((crate::state_tree::empty_root(), 0));
        }
        let bytes = self.blocks.get(txn, &prev_hash)?.ok_or(Error::Corrupt("a parent block is not stored"))?;
        let header = BlockHeader::from_bytes(&bytes[..HEADER_LEN.min(bytes.len())]).map_err(|_| Error::Corrupt("a stored block was corrupt"))?;
        Ok((header.state_root, header.output_count))
    }

    /// The chunks a received block's proof says to apply its body in; one
    /// chunk of everything if the proof doesn't say (it's then invalid
    /// anyway, unless proofs aren't being checked).
    fn chunks_of(body: &BlockBody) -> ChunkIndices {
        body.proof
            .chunk_assignment(body.inputs.len(), body.outputs.len())
            .unwrap_or_else(|| vec![((0..body.inputs.len()).collect(), (0..body.outputs.len()).collect())])
    }

    /// `Error::WrongGenesis` if `header` claims to be a first block but
    /// isn't this chain's fixed genesis (when it has one).
    fn check_genesis(&self, header: &BlockHeader) -> Result<()> {
        match self.genesis_hash {
            Some(genesis) if header.prev_hash == GENESIS_PARENT_HASH && header.hash() != genesis => {
                Err(Error::WrongGenesis)
            }
            _ => Ok(()),
        }
    }

    /// The tip's full header, or `None` if no block has ever been
    /// applied. Everything else this type reports about the tip
    /// (`tip_hash`, `height`) is derived from this one stored value --
    /// see `TIP_HEADER_KEY`'s docs.
    fn tip_header(&self, txn: &heed::RoTxn) -> Result<Option<BlockHeader>> {
        match self.meta.get(txn, TIP_HEADER_KEY)? {
            Some(bytes) => {
                let header = BlockHeader::from_bytes(bytes).map_err(|_| Error::Corrupt("stored tip header was corrupt"))?;
                Ok(Some(header))
            }
            None => Ok(None),
        }
    }

    /// A previously-accepted block, by hash -- active chain or side
    /// branch, `BLOCKS_DB` doesn't distinguish. `Error::Corrupt` if
    /// it's not there at all, which should only happen for a hash
    /// nothing in this module ever actually stored.
    fn get_stored_block(&self, txn: &heed::RoTxn, hash: [u8; 32]) -> Result<Block> {
        let bytes = self.blocks.get(txn, &hash)?.ok_or(Error::Corrupt("referenced block is not stored"))?;
        Block::from_bytes(bytes).map_err(|_| Error::Corrupt("stored block was corrupt"))
    }

    fn is_known_invalid(&self, txn: &heed::RoTxn, hash: [u8; 32]) -> Result<bool> {
        Ok(self.invalid_blocks.get(txn, &hash)?.is_some())
    }

    /// Record every block in `blocks` as invalid, in its own committed
    /// transaction -- the reorg transaction that discovered the fault
    /// has already been aborted by the time this runs.
    fn mark_invalid(&mut self, blocks: &[Block]) -> Result<()> {
        let storage = self.storage.clone();
        let mut wtxn = storage.write_txn()?;
        for block in blocks {
            self.invalid_blocks.put(&mut wtxn, &block.header.hash(), &[])?;
        }
        wtxn.commit()?;
        Ok(())
    }

    /// Cumulative work up to and including `hash` -- `[0; 32]` for
    /// `GENESIS_PARENT_HASH` (the "chain" before any real block
    /// exists has no work at all), otherwise whatever was snapshotted
    /// for that block when it was accepted (`BLOCK_WORK_DB`).
    /// `Error::Corrupt` for any other hash with no stored work, which
    /// should only happen for one this module never actually accepted.
    fn chain_work(&self, txn: &heed::RoTxn, hash: [u8; 32]) -> Result<[u8; 32]> {
        if hash == GENESIS_PARENT_HASH {
            return Ok([0u8; 32]);
        }
        let bytes = self.block_work.get(txn, &hash)?.ok_or(Error::Corrupt("no stored chain work for this block"))?;
        bytes.try_into().map_err(|_| Error::Corrupt("stored chain work was not 32 bytes"))
    }

    /// What a chain proof of block `hash` attests besides its header: the
    /// `(target, window start)` in effect after it, and the cumulative
    /// work up to it.
    pub(crate) fn proof_state(&self, hash: [u8; 32]) -> Result<([u8; 32], u64, [u8; 32])> {
        let rtxn = self.storage.read_txn()?;
        self.proof_state_in(&rtxn, hash)
    }

    fn proof_state_in(&self, txn: &heed::RoTxn, hash: [u8; 32]) -> Result<([u8; 32], u64, [u8; 32])> {
        let retarget = self.retarget_state_after(txn, hash)?;
        Ok((retarget.target, retarget.window_start_timestamp, self.chain_work(txn, hash)?))
    }

    /// The tip a chain proof of block `hash` attests: its header, and what
    /// this chain records after it.
    fn chain_tip(&self, txn: &heed::RoTxn, hash: [u8; 32]) -> Result<crate::chain_step::Tip> {
        let header = self.get_stored_block(txn, hash)?.header;
        Ok(crate::chain_step::Tip::new(&header, self.proof_state_in(txn, hash)?))
    }

    /// Require every block after the first to carry its parent's chain
    /// proof, checked by `verifier`.
    pub fn require_chain_proofs(&mut self, verifier: crate::chain_step::ChainVerifier) {
        self.chain_proofs = Some(verifier);
    }

    /// Everything needed to prove block `hash`'s chain proof -- which the
    /// next block on it carries -- from this chain's records.
    pub fn chain_proof_inputs(&self, hash: [u8; 32]) -> Result<crate::chain_step::ChainProofInputs> {
        let rtxn = self.storage.read_txn()?;
        let block = self.get_stored_block(&rtxn, hash)?;
        let tip = crate::chain_step::Tip::new(&block.header, self.proof_state_in(&rtxn, hash)?);
        let inputs = if block.header.prev_hash == GENESIS_PARENT_HASH {
            None
        } else {
            let parent_tip = self.chain_tip(&rtxn, block.header.prev_hash)?;
            let state = block.state_change((parent_tip.state_root, parent_tip.output_count));
            Some(crate::chain_step::BlockInputs {
                inputs: block.body.inputs.clone(),
                outputs: block.body.outputs.clone(),
                nonces: block.body.nonces.clone(),
                proof: block.body.proof.clone(),
                state,
                parent_tip,
                parent_chain_proof: block.body.chain_proof.clone(),
            })
        };
        Ok(crate::chain_step::ChainProofInputs {
            header: block.header,
            tip,
            block: inputs,
        })
    }

    /// The `RetargetState` right after `hash` -- the initial state for
    /// `GENESIS_PARENT_HASH`, otherwise whatever was recorded for that
    /// block when it was accepted (`BLOCK_RETARGET_DB`).
    fn retarget_state_after(&self, txn: &heed::RoTxn, hash: [u8; 32]) -> Result<RetargetState> {
        if hash == GENESIS_PARENT_HASH {
            return Ok(RetargetState {
                target: self.difficulty.initial_target,
                window_start_timestamp: 0,
            });
        }
        let bytes = self
            .block_retarget
            .get(txn, &hash)?
            .ok_or(Error::Corrupt("no stored retarget state for this block"))?;
        RetargetState::from_bytes(bytes)
    }

    /// Record `block` in every per-block store -- the block itself, its
    /// cumulative work, the retargeting state after it, and the height
    /// index -- active chain or side branch alike.
    fn store_block_records(
        &self,
        wtxn: &mut heed::RwTxn,
        block: &Block,
        work: [u8; 32],
        retarget: RetargetState,
    ) -> Result<()> {
        let hash = block.header.hash();
        self.blocks.put(wtxn, &hash, &block.to_bytes())?;
        self.block_work.put(wtxn, &hash, &work)?;
        self.block_retarget.put(wtxn, &hash, &retarget.to_bytes())?;
        self.block_heights.put(wtxn, &height_key(block.header.height, hash), &[])?;
        Ok(())
    }

    /// The height at or below which no block can matter any more: a
    /// block at this height or lower could only ever be part of a
    /// branch forking off the active chain further back than
    /// `max_reorg_depth` allows. `None` while the active chain is still
    /// shallower than that (every height, back to genesis, is fair game).
    /// The single number `accept_block`'s early rejection,
    /// `find_fork_point`'s search bound, and `prune`'s cutoff all share.
    fn reorg_floor(&self, txn: &heed::RoTxn) -> Result<Option<u64>> {
        let by_depth = self
            .height(txn)?
            .and_then(|tip_height| tip_height.checked_sub(self.max_reorg_depth));
        Ok(match (by_depth, self.sync_base(txn)?) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (a, b) => a.or(b),
        })
    }

    /// The height a fast sync started this chain at, if one did.
    fn sync_base(&self, txn: &heed::RoTxn) -> Result<Option<u64>> {
        match self.meta.get(txn, SYNC_BASE_KEY)? {
            Some(b) => Ok(Some(u64::from_be_bytes(b.try_into().map_err(|_| Error::Corrupt("sync base was not 8 bytes"))?))),
            None => Ok(None),
        }
    }

    /// Start this chain, holding nothing yet but (possibly) its genesis,
    /// at block `base` -- a fast sync (`snapshot`): `point` is what the
    /// chain proof of `base` (`chain_proof`, from the block after it)
    /// attests along with its header, and `unspent` the state tree's
    /// unspent outputs then (positions in order). Checked: the chain
    /// proof (when this chain requires them), the body against the
    /// header, and the snapshot against the header's state root and
    /// count, with no two unspent outputs alike. Blocks before `base`
    /// aren't stored, so nothing reorgs below it, and outputs spent
    /// before it are unknown (`has_full_history`). Imported outputs are
    /// recorded at `base`'s height: their real heights are older, which
    /// only matters for the coinbase maturity of outputs younger than
    /// that, and syncing far enough back leaves none.
    /// Whether `chain_proof` (from the block after `base`) attests `base`
    /// with `point` -- a fast sync's sync point, checked before its state
    /// is downloaded. Only the body's hash is checked when this chain
    /// doesn't require chain proofs.
    pub fn check_sync_point(&self, base: &Block, point: &crate::snapshot::SyncPoint, chain_proof: &[u8]) -> Result<()> {
        let header = &base.header;
        if header.height == 0 || base.body.body_hash() != header.body_hash {
            return Err(Error::Snapshot("not a valid base block"));
        }
        if let Some(verifier) = &self.chain_proofs {
            let tip = crate::chain_step::Tip::new(header, (point.target, point.window_start, point.work));
            if !verifier.verify(&tip, chain_proof) {
                return Err(Error::Snapshot("the chain proof doesn't attest this block"));
            }
        }
        Ok(())
    }

    pub fn import_snapshot(&mut self, base: &Block, point: &crate::snapshot::SyncPoint, chain_proof: &[u8], unspent: &[crate::state_tree::Entry]) -> Result<()> {
        let storage = self.storage.clone();
        let mut wtxn = storage.write_txn()?;
        if self.height(&wtxn)?.unwrap_or(0) != 0 || self.state.count(&wtxn)? != 0 {
            return Err(Error::Snapshot("this chain isn't empty"));
        }
        self.check_sync_point(base, point, chain_proof)?;
        let header = &base.header;
        let root = self.state.import(&mut wtxn, header.output_count, unspent).map_err(|_| Error::Snapshot("malformed unspent set"))?;
        if root != header.state_root {
            return Err(Error::StateRootMismatch);
        }
        for (position, commitment, nonce) in unspent {
            if self.utxo.get(&wtxn, *commitment)?.is_some() {
                return Err(Error::DuplicateOutput(*commitment));
            }
            self.utxo.insert(&mut wtxn, *commitment, *position)?;
            self.output_index.put(&mut wtxn, commitment, &[&header.height.to_be_bytes()[..], nonce].concat())?;
        }
        self.meta.put(&mut wtxn, TIP_HEADER_KEY, &header.to_bytes())?;
        self.meta.put(&mut wtxn, CURRENT_TARGET_KEY, &point.target)?;
        self.meta.put(&mut wtxn, WINDOW_START_TIMESTAMP_KEY, &point.window_start.to_be_bytes())?;
        self.meta.put(&mut wtxn, SYNC_BASE_KEY, &header.height.to_be_bytes())?;
        let retarget = RetargetState {
            target: point.target,
            window_start_timestamp: point.window_start,
        };
        self.store_block_records(&mut wtxn, base, point.work, retarget)?;
        self.active_heights.put(&mut wtxn, &header.height.to_be_bytes(), &header.hash())?;
        wtxn.commit()?;
        Ok(())
    }

    /// For every block strictly below `reorg_floor`, drop what only a
    /// reorg could ever need -- undo data, work, retarget state, invalid
    /// marker, height index entry -- and, for side-branch blocks, the
    /// block itself. Nothing below that height can ever be unwound to,
    /// replayed, or extended by an acceptable block again. Active-chain
    /// blocks themselves are kept forever: they're what a new node
    /// syncing from genesis has to download from someone, and until
    /// state-snapshot sync exists, that someone is every node. The floor
    /// block keeps everything: a side branch forking right at it still
    /// needs its work and retarget state.
    fn prune(&self, wtxn: &mut heed::RwTxn) -> Result<()> {
        let Some(floor) = self.reorg_floor(wtxn)? else {
            return Ok(());
        };
        let end = floor.to_be_bytes();
        let mut doomed = Vec::new();
        // A `(Bound, Bound)` pair rather than `..&end[..]`: `Bytes`' key
        // type is the unsized `[u8]`, which only the tuple form of
        // `RangeBounds` accepts.
        let below_floor = (std::ops::Bound::Unbounded, std::ops::Bound::Excluded(&end[..]));
        for entry in self.block_heights.range(wtxn, &below_floor)? {
            let (key, _) = entry?;
            doomed.push(key.to_vec());
        }
        for key in doomed {
            let hash: [u8; 32] = key[8..].try_into().map_err(|_| Error::Corrupt("height index key was not 40 bytes"))?;
            let active = self.active_heights.get(wtxn, &key[..8])? == Some(&hash[..]);
            if !active {
                self.blocks.delete(wtxn, &hash)?;
            }
            self.block_undo.delete(wtxn, &hash)?;
            self.block_work.delete(wtxn, &hash)?;
            self.block_retarget.delete(wtxn, &hash)?;
            self.invalid_blocks.delete(wtxn, &hash)?;
            self.block_heights.delete(wtxn, &key)?;
        }
        Ok(())
    }

    /// The least proof of work an orphan must show to be pooled: the
    /// active chain's current target, made easier by
    /// `max_adjustment_factor`. An orphan's real target can't be known
    /// without its parent, so this is a heuristic, not consensus -- it
    /// only has to make junk orphans expensive (each costs a real
    /// fraction of a block's work, rather than nothing) without turning
    /// away legitimate ones. Relaxing by exactly one retarget's maximum
    /// swing admits an orphan from just past a window boundary on a
    /// chain that eased up as far as one retarget allows. Rejecting a
    /// legitimate orphan is cheap anyway: it just gets accepted
    /// normally once its parent arrives and it's sent again.
    fn orphan_target(&self, txn: &heed::RoTxn) -> Result<[u8; 32]> {
        let current = self.current_target(txn)?;
        Ok(pow::scale(current, self.difficulty.max_adjustment_factor, 1))
    }

    /// The current tip's header hash, or `GENESIS_PARENT_HASH` if no
    /// block has ever been applied.
    pub fn tip_hash(&self, txn: &heed::RoTxn) -> Result<[u8; 32]> {
        Ok(self.tip_header(txn)?.map(|h| h.hash()).unwrap_or(GENESIS_PARENT_HASH))
    }

    /// The current tip's height, or `None` if no block has ever been
    /// applied (there is no height to report yet).
    pub fn height(&self, txn: &heed::RoTxn) -> Result<Option<u64>> {
        Ok(self.tip_header(txn)?.map(|h| h.height))
    }

    /// Whether `commitment` is an unspent output of the active chain.
    pub fn is_unspent(&self, txn: &heed::RoTxn, commitment: &[u8; 32]) -> Result<bool> {
        Ok(self.utxo.get(txn, *commitment)?.is_some())
    }

    /// The height and recovery nonce of an output the active chain
    /// created (spent or not), if it did.
    pub fn output_record(&self, txn: &heed::RoTxn, commitment: &[u8; 32]) -> Result<Option<OutputRecord>> {
        match self.output_index.get(txn, commitment)? {
            Some(bytes) => Ok(Some(OutputRecord::decode(*commitment, bytes)?)),
            None => Ok(None),
        }
    }

    /// Call `f` with every output the active chain has created, spent or
    /// not (in commitment order), and whether it's still unspent -- what
    /// wallet recovery scans. One pass, one read transaction.
    pub fn for_each_output(&self, txn: &heed::RoTxn, mut f: impl FnMut(&OutputRecord, bool)) -> Result<()> {
        for item in self.output_index.iter(txn)? {
            let (key, bytes) = item?;
            let commitment: [u8; 32] = key.try_into().map_err(|_| Error::Corrupt("output index key was not 32 bytes"))?;
            let record = OutputRecord::decode(commitment, bytes)?;
            f(&record, self.is_unspent(txn, &commitment)?);
        }
        Ok(())
    }

    /// A read-only view of the active chain as it is now (see
    /// `wallet::ChainView`).
    pub fn view(&self) -> Result<ChainState<'_>> {
        Ok(ChainState {
            chain: self,
            txn: self.storage.read_txn()?,
        })
    }

    /// The `(prev_hash, height)` the next block must declare to extend
    /// this chain's current tip -- `(GENESIS_PARENT_HASH, 0)` for an
    /// empty chain.
    fn next_prev_hash_and_height(&self, txn: &heed::RoTxn) -> Result<([u8; 32], u64)> {
        match self.tip_header(txn)? {
            Some(tip) => Ok((tip.hash(), tip.height + 1)),
            None => Ok((GENESIS_PARENT_HASH, 0)),
        }
    }

    /// The PoW target the next block must meet -- `self.difficulty.
    /// initial_target` until the first retarget happens. See the
    /// module docs on difficulty retargeting.
    pub fn current_target(&self, txn: &heed::RoTxn) -> Result<[u8; 32]> {
        match self.meta.get(txn, CURRENT_TARGET_KEY)? {
            Some(bytes) => bytes
                .try_into()
                .map_err(|_| Error::Corrupt("current target was not 32 bytes")),
            None => Ok(self.difficulty.initial_target),
        }
    }

    fn window_start_timestamp(&self, txn: &heed::RoTxn) -> Result<u64> {
        match self.meta.get(txn, WINDOW_START_TIMESTAMP_KEY)? {
            Some(bytes) => bytes
                .try_into()
                .map(u64::from_be_bytes)
                .map_err(|_| Error::Corrupt("window start timestamp was not 8 bytes")),
            None => Ok(0),
        }
    }

    /// Advance the active chain's retargeting state past
    /// `applied_header` (see `RetargetState::after` for the rule
    /// itself), through `wtxn` -- called once a block has already
    /// passed every other check in `apply_block`, right before it's
    /// committed. Returns the new state, for `BLOCK_RETARGET_DB`.
    fn retarget_if_due(&mut self, wtxn: &mut heed::RwTxn, applied_header: &BlockHeader) -> Result<RetargetState> {
        let prev = RetargetState {
            target: self.current_target(wtxn)?,
            window_start_timestamp: self.window_start_timestamp(wtxn)?,
        };
        let next = prev.after(&self.difficulty, applied_header);
        self.meta.put(wtxn, CURRENT_TARGET_KEY, &next.target)?;
        self.meta
            .put(wtxn, WINDOW_START_TIMESTAMP_KEY, &next.window_start_timestamp.to_be_bytes())?;
        Ok(next)
    }

    /// Resolve and apply `body`'s inputs and outputs against real chain
    /// state, through `wtxn`: every input must resolve to a currently
    /// live (unspent) output, which is then marked spent in the state
    /// tree and removed from `utxo`; every output must not collide with
    /// one still live, and is then appended to the state tree and recorded
    /// in `utxo`. Returns the resulting `(state_root, output_count,
    /// spent_inputs)` --
    /// the third element is each input's `(commitment, position)`
    /// *before* it was removed, which is exactly `UndoData` needs to
    /// undo this later (see that type's docs); `build_block` just
    /// discards it, since it never commits anything in the first
    /// place. Nothing here is specific to a real header -- `apply_block`
    /// checks the roots against one, `build_block` just wants them --
    /// and nothing here commits `wtxn`; that's always the caller's job.
    ///
    /// Applied chunk by chunk (`chunks`): each chunk's inputs spent, then
    /// its outputs appended -- so outputs get positions in chunk order,
    /// as the block's proof applies them. With `record`, also returns each
    /// chunk's state transition witness (positions, nonces, paths, every
    /// `CHUNK_SHAPE` slot), for proving.
    fn resolve_and_apply(&mut self, wtxn: &mut heed::RwTxn, body: &BlockBody, chunks: &ChunkIndices, record: bool) -> Result<ResolveResult> {
        use crate::aggregate::{ChunkTransition, StateChange};
        use crate::poseidon2::digest_from_bytes;
        use crate::prover::CHUNK_SHAPE;
        let mut spent_inputs = Vec::with_capacity(body.inputs.len());
        let mut transitions = Vec::new();
        let mut seen_inputs = 0;
        let mut seen_outputs = 0;
        for (ins, outs) in chunks {
            seen_inputs += ins.len();
            seen_outputs += outs.len();
            if record && (ins.len() > CHUNK_SHAPE.inputs || outs.len() > CHUNK_SHAPE.outputs) {
                return Err(Error::TransactionTooLarge);
            }
            let root_in = self.state.root(wtxn)?;
            let count_in = self.state.count(wtxn)?;
            let mut t_inputs = Vec::new();
            let mut t_outputs = Vec::new();
            for &i in ins {
                let commitment = body.inputs[i];
                let position = self
                    .utxo
                    .get(wtxn, commitment)?
                    .ok_or(Error::UnresolvedInput(commitment))?;
                if record {
                    let nonce = self
                        .output_record(wtxn, &commitment)?
                        .ok_or(Error::Corrupt("an unspent output's record is missing"))?
                        .nonce;
                    t_inputs.push((position, nonce, self.state.path(wtxn, position)?));
                }
                self.state.spend(wtxn, position)?;
                self.utxo.remove(wtxn, commitment)?;
                spent_inputs.push((commitment, position));
            }
            if record {
                let count = self.state.count(wtxn)?;
                for _ in ins.len()..CHUNK_SHAPE.inputs {
                    t_inputs.push((count, [0; crate::recovery::NONCE_LEN], self.state.path(wtxn, count)?));
                }
            }
            for &o in outs {
                let (commitment, nonce) = (body.outputs[o], body.nonces[o]);
                if self.utxo.get(wtxn, commitment)?.is_some() {
                    return Err(Error::DuplicateOutput(commitment));
                }
                if record {
                    let count = self.state.count(wtxn)?;
                    t_outputs.push(self.state.path(wtxn, count)?);
                }
                let position = self.state.push(wtxn, &commitment, &nonce)?;
                self.utxo.insert(wtxn, commitment, position)?;
            }
            if record {
                let count = self.state.count(wtxn)?;
                for _ in outs.len()..CHUNK_SHAPE.outputs {
                    t_outputs.push(self.state.path(wtxn, count)?);
                }
                transitions.push(ChunkTransition {
                    change: StateChange {
                        root_in: digest_from_bytes(&root_in),
                        count_in,
                        root_out: digest_from_bytes(&self.state.root(wtxn)?),
                        count_out: self.state.count(wtxn)?,
                    },
                    inputs: t_inputs,
                    outputs: t_outputs,
                });
            }
        }
        if seen_inputs != body.inputs.len() || seen_outputs != body.outputs.len() {
            return Err(Error::InvalidBlock);
        }
        Ok((self.state.root(wtxn)?, self.state.count(wtxn)?, spent_inputs, transitions))
    }

    /// Apply `block` to the chain: resolve its inputs/outputs against
    /// real state, update `state`/`utxo`, and advance the tip --
    /// all in one LMDB write transaction, committed only once every check
    /// passes. On any error, the transaction is simply never committed
    /// (see the module docs on atomicity): every store is left exactly
    /// as it was before this call.
    ///
    /// Checked, in order: that `header.timestamp` isn't too far in this
    /// node's future; `block.validate()` against this node's own idea
    /// of the current PoW target (proof of work, canonical ordering, no
    /// same-block spend, `body_hash` matches); that `prev_hash`/
    /// `height` chain onto the current tip; that every input resolves
    /// and every output avoids colliding with a live one; and that the
    /// roots applying the body actually produces match what the header
    /// claims. Difficulty retargeting's side state is updated last,
    /// right before committing -- see the module docs.
    pub fn apply_block(&mut self, block: &Block) -> Result<()> {
        // A local, cloned handle (just an `Arc` bump -- see `Storage`'s
        // docs) rather than `self.storage.write_txn()` directly: that
        // would tie `wtxn`'s lifetime to a borrow of `self` itself,
        // which would then conflict with the `&mut self` calls below.
        let storage = self.storage.clone();
        let mut wtxn = storage.write_txn()?;
        self.apply_block_in_txn(&mut wtxn, block)?;
        self.prune(&mut wtxn)?;
        wtxn.commit()?;
        Ok(())
    }

    /// `apply_block`'s actual work, through a caller-supplied `wtxn`
    /// rather than one this method opens and commits itself -- what
    /// lets `accept_block`'s reorg path replay several blocks (plus
    /// whatever `unwind_tip` calls preceded them) inside one shared
    /// transaction, atomically, instead of each block committing on
    /// its own as it would through the public `apply_block`.
    fn apply_block_in_txn(&mut self, wtxn: &mut heed::RwTxn, block: &Block) -> Result<()> {
        if block.header.timestamp > now_millis() + MAX_FUTURE_DRIFT_MS {
            return Err(Error::TimestampTooFarInFuture);
        }

        let target = self.current_target(wtxn)?;
        if !self.block_is_valid(wtxn, block, &target)? {
            return Err(Error::InvalidBlock);
        }

        let (expected_prev_hash, expected_height) = self.next_prev_hash_and_height(wtxn)?;
        if block.header.prev_hash != expected_prev_hash {
            return Err(Error::WrongParent);
        }
        if block.header.height != expected_height {
            return Err(Error::WrongHeight);
        }
        self.check_genesis(&block.header)?;
        if let Some(parent) = self.tip_header(wtxn)?
            && block.header.timestamp <= parent.timestamp
        {
            return Err(Error::TimestampNotAfterParent);
        }

        // Snapshot everything `unwind_tip` will need to restore, before
        // any of it gets overwritten below -- see `UndoData`'s docs on
        // why this is the only chance to capture it.
        let prev_tip_header = self.tip_header(wtxn)?;
        let prev_current_target = target;
        let prev_window_start_timestamp = self.window_start_timestamp(wtxn)?;
        let parent_work = self.chain_work(wtxn, block.header.prev_hash)?;

        let chunks = Self::chunks_of(&block.body);
        let (state_root, output_count, spent_inputs, _) = self.resolve_and_apply(wtxn, &block.body, &chunks, false)?;
        for (commitment, nonce) in block.body.outputs.iter().zip(&block.body.nonces) {
            let record = [&block.header.height.to_be_bytes()[..], nonce].concat();
            self.output_index.put(wtxn, commitment, &record)?;
        }
        if state_root != block.header.state_root {
            return Err(Error::StateRootMismatch);
        }
        if output_count != block.header.output_count {
            return Err(Error::OutputCountMismatch);
        }

        let retarget = self.retarget_if_due(wtxn, &block.header)?;
        self.meta.put(wtxn, TIP_HEADER_KEY, &block.header.to_bytes())?;

        let undo = UndoData {
            prev_tip_header,
            prev_current_target,
            prev_window_start_timestamp,
            spent_inputs,
        };
        self.block_undo.put(wtxn, &block.header.hash(), &undo.to_bytes())?;
        let this_work = pow::add256(parent_work, pow::work_for_target(target));
        self.store_block_records(wtxn, block, this_work, retarget)?;
        self.active_heights
            .put(wtxn, &block.header.height.to_be_bytes(), &block.header.hash())?;

        Ok(())
    }

    /// Undo the current tip, through `wtxn`, restoring the chain to
    /// exactly the state it was in right before that block was ever
    /// applied -- the state-tree/utxo effects reversed using the
    /// block's own stored `UndoData`, and the tip header/retargeting
    /// state restored from the same snapshot. Nothing is committed
    /// here; that's the caller's job, same as everywhere else in this
    /// module. Returns the unwound block.
    ///
    /// Fails with `Error::Corrupt` if there's no tip at all, or if its
    /// stored block/undo data is missing. The latter shouldn't happen
    /// for anything `apply_block` itself persisted -- but once a
    /// retention limit or pruning exists, "we don't have that block
    /// anymore" is exactly the condition that should surface here,
    /// rather than this method guessing at a substitute.
    ///
    /// Only ever moves the tip back one block. The orchestration that
    /// decides *how many* times to call this, and what to do if it
    /// would need to go back further than retained data allows (see
    /// `max_reorg_depth`), is `accept_block`'s concern -- this is
    /// deliberately just the one-block primitive.
    pub(crate) fn unwind_tip(&mut self, wtxn: &mut heed::RwTxn) -> Result<Block> {
        let tip_header = self.tip_header(wtxn)?.ok_or(Error::Corrupt("no tip to unwind"))?;
        let hash = tip_header.hash();

        let block_bytes = self.blocks.get(wtxn, &hash)?.ok_or(Error::Corrupt("tip block is not stored"))?;
        let block = Block::from_bytes(block_bytes).map_err(|_| Error::Corrupt("stored tip block was corrupt"))?;

        let undo_bytes = self.block_undo.get(wtxn, &hash)?.ok_or(Error::Corrupt("tip undo data is not stored"))?;
        let undo = UndoData::from_bytes(undo_bytes)?;

        // Reverse the inputs: every spent output goes back to live, at
        // exactly the position it occupied before.
        for (commitment, position) in &undo.spent_inputs {
            // Its nonce: the output index keeps spent outputs' records
            // (until the block that created them is itself unwound).
            let record = self
                .output_record(wtxn, commitment)?
                .ok_or(Error::Corrupt("a spent output's record is missing"))?;
            self.state.unspend(wtxn, *position, commitment, &record.nonce)?;
            self.utxo.insert(wtxn, *commitment, *position)?;
        }
        // Reverse the outputs: each one this block created disappears
        // from the live set again.
        for commitment in &block.body.outputs {
            self.utxo.remove(wtxn, *commitment)?;
            self.output_index.delete(wtxn, commitment)?;
        }
        // Reverse the appends -- this block appended exactly
        // `body.outputs.len()` outputs, the last ones, and nothing else
        // has been appended since (we're unwinding the tip).
        self.state.truncate(wtxn, block.body.outputs.len() as u64)?;

        self.active_heights.delete(wtxn, &block.header.height.to_be_bytes())?;

        // Restore the tip and retargeting state exactly as snapshotted.
        match &undo.prev_tip_header {
            Some(header) => {
                self.meta.put(wtxn, TIP_HEADER_KEY, &header.to_bytes())?;
            }
            None => {
                self.meta.delete(wtxn, TIP_HEADER_KEY)?;
            }
        }
        self.meta.put(wtxn, CURRENT_TARGET_KEY, &undo.prev_current_target)?;
        self.meta
            .put(wtxn, WINDOW_START_TIMESTAMP_KEY, &undo.prev_window_start_timestamp.to_be_bytes())?;

        Ok(block)
    }

    /// Find where `candidate_tip_hash`'s chain and the active chain
    /// diverge, searching the active side back at most
    /// `self.max_reorg_depth` blocks, and the candidate side back until
    /// it either meets the active side or drops to `reorg_floor` (below
    /// which it can't possibly meet it any more). The candidate side is
    /// bounded by height, not by a step count: a branch can be longer
    /// than `max_reorg_depth` past the fork point without the *unwind*
    /// being any deeper -- two miners neck and neck for a while, say.
    /// `None` if no common ancestor turns up within those bounds -- the
    /// caller should treat that as `Error::ReorgTooDeep`, not keep
    /// searching (see `Chain::open`'s docs on why this crate refuses
    /// rather than attempting a deeper reorg).
    fn find_fork_point(&self, txn: &heed::RoTxn, candidate_tip_hash: [u8; 32]) -> Result<Option<ForkPoint>> {
        let max_depth = self.max_reorg_depth;
        let floor = self.reorg_floor(txn)?;

        // Hash -> how many `unwind_tip` calls reach it from the active tip.
        let mut active_depth: std::collections::HashMap<[u8; 32], u64> = std::collections::HashMap::new();
        let mut hash = self.tip_hash(txn)?;
        let mut depth = 0u64;
        loop {
            active_depth.insert(hash, depth);
            if hash == GENESIS_PARENT_HASH || depth >= max_depth {
                break;
            }
            let block = self.get_stored_block(txn, hash)?;
            if floor.is_some_and(|floor| block.header.height <= floor) {
                break;
            }
            hash = block.header.prev_hash;
            depth += 1;
        }

        // Walk back from the candidate tip, collecting its own blocks,
        // until landing on a hash the active side already knows about.
        let mut replay = Vec::new();
        let mut hash = candidate_tip_hash;
        loop {
            if let Some(&unwind_count) = active_depth.get(&hash) {
                replay.reverse();
                return Ok(Some(ForkPoint { unwind_count, replay }));
            }
            if hash == GENESIS_PARENT_HASH {
                return Ok(None);
            }
            let block = self.get_stored_block(txn, hash)?;
            if floor.is_some_and(|floor| block.header.height <= floor) {
                return Ok(None);
            }
            hash = block.header.prev_hash;
            replay.push(block);
        }
    }

    /// Validate and store `block` as a side-branch candidate, through
    /// `wtxn` -- *not* applied to live `state`/`utxo` state
    /// (it might not even be valid relative to that state -- it could
    /// spend an output only its own branch believes exists, or double
    /// spend one the active chain already spent differently; there's
    /// no separate UTXO snapshot per branch to check that against
    /// yet). That check only actually happens if/when this block is
    /// replayed for real, through `apply_block_in_txn`, inside one
    /// shared, all-or-nothing reorg transaction -- which is exactly
    /// what makes skipping it here safe rather than a hole: a bad
    /// side-branch block just fails *then*, aborting the whole reorg
    /// attempt and leaving the active chain untouched.
    ///
    /// What *is* checked here: the block's own `Block::validate`
    /// (proof of work, canonical ordering, body_hash, proof), against
    /// the target its own branch's history implies -- the parent's
    /// recorded `RetargetState`, not the active chain's, since the two
    /// differ once a fork straddles a retarget-window boundary. Also
    /// checked: that `prev_hash`/`height` actually match the parent
    /// block it claims to extend.
    fn store_side_branch_block(&mut self, wtxn: &mut heed::RwTxn, block: &Block) -> Result<()> {
        let parent_retarget = self.retarget_state_after(wtxn, block.header.prev_hash)?;
        if !self.block_is_valid(wtxn, block, &parent_retarget.target)? {
            return Err(Error::InvalidSideBranchBlock);
        }

        self.check_genesis(&block.header)?;
        let (expected_height, parent_work) = if block.header.prev_hash == GENESIS_PARENT_HASH {
            (0, [0u8; 32])
        } else {
            let parent = self.get_stored_block(wtxn, block.header.prev_hash)?;
            if block.header.timestamp <= parent.header.timestamp {
                return Err(Error::TimestampNotAfterParent);
            }
            let parent_work = self.chain_work(wtxn, block.header.prev_hash)?;
            (parent.header.height + 1, parent_work)
        };
        if block.header.height != expected_height {
            return Err(Error::InvalidSideBranchLineage);
        }

        let this_work = pow::add256(parent_work, pow::work_for_target(parent_retarget.target));
        let retarget = parent_retarget.after(&self.difficulty, &block.header);
        self.store_block_records(wtxn, block, this_work, retarget)
    }

    /// Accept `block`, whatever it turns out to be relative to the
    /// active chain -- the general entry point a real node would call
    /// for every block it receives, one at a time, in whatever order
    /// they arrive. Three things can happen:
    ///
    /// - It extends the active tip directly: applied immediately
    ///   (`apply_block`), same as always.
    /// - It extends some other block this `Chain` already knows about
    ///   (active-chain history or another side branch): validated and
    ///   stored as a side branch (`store_side_branch_block`), in its
    ///   own transaction -- always safe to commit regardless of what
    ///   happens next, since nothing live is touched. Then, in a
    ///   *separate* transaction, fork-choice runs: if this branch's
    ///   total work now exceeds the active chain's, the chain reorgs
    ///   onto it -- `find_fork_point` locates the common ancestor
    ///   (bounded by `max_reorg_depth`; `Error::ReorgTooDeep` if
    ///   that's not enough), then `unwind_tip` and `apply_block_in_txn`
    ///   run in one shared transaction, committed only if every
    ///   replayed block actually validates -- so a bad block deep in
    ///   a heavier-looking branch aborts the whole reorg, leaving the
    ///   active chain exactly as it was.
    /// - Its parent isn't known at all: held in the orphan pool (at
    ///   most `max_orphans` of them, oldest evicted first), provided
    ///   its proof of work meets `orphan_target` -- `Error::
    ///   OrphanPowTooWeak` otherwise.
    ///
    /// Before any of that, a block already stored or already waiting
    /// as an orphan is reported as `AlreadyKnown` and otherwise
    /// ignored; one that is, or extends, a block recorded in
    /// `INVALID_BLOCKS_DB` is refused with `Error::KnownInvalidBlock`;
    /// and one at or below `reorg_floor` is refused with `Error::
    /// ReorgTooDeep` -- nothing that low can ever win, so it isn't
    /// worth storing or pooling. A reorg that fails on a block-level
    /// fault (`Error::is_block_fault`) records the failing block and
    /// everything after it in that branch as invalid, so the same
    /// branch never triggers another attempt.
    ///
    /// Whenever `block` ends up connected (applied, stored, or reorged
    /// onto), any orphans that were waiting on it are retried right
    /// away, transitively -- see `connect_orphans`. The returned
    /// outcome is `block`'s own; theirs aren't reported (an orphan that
    /// fails is just dropped), but anything they did to the active
    /// chain is visible through `tip_hash` like any other change.
    pub fn accept_block(&mut self, block: Block) -> Result<AcceptOutcome> {
        let hash = block.header.hash();
        let outcome = self.accept_one(block)?;
        if is_connected(&outcome) {
            self.connect_orphans(hash);
        }
        Ok(outcome)
    }

    /// `accept_block` for exactly one block, without touching the
    /// orphan pool beyond (possibly) adding `block` to it.
    fn accept_one(&mut self, block: Block) -> Result<AcceptOutcome> {
        let storage = self.storage.clone();
        let hash = block.header.hash();

        let rtxn = storage.read_txn()?;
        if self.is_known_invalid(&rtxn, hash)? || self.is_known_invalid(&rtxn, block.header.prev_hash)? {
            drop(rtxn);
            self.mark_invalid(std::slice::from_ref(&block))?;
            return Err(Error::KnownInvalidBlock);
        }
        if self.orphans.iter().any(|(orphan_hash, _)| *orphan_hash == hash) || self.blocks.get(&rtxn, &hash)?.is_some() {
            return Ok(AcceptOutcome::AlreadyKnown);
        }
        if self.reorg_floor(&rtxn)?.is_some_and(|floor| block.header.height <= floor) {
            return Err(Error::ReorgTooDeep);
        }

        let tip_hash = self.tip_hash(&rtxn)?;
        if block.header.prev_hash == tip_hash {
            drop(rtxn);
            self.apply_block(&block)?;
            return Ok(AcceptOutcome::Applied);
        }

        let parent_known =
            block.header.prev_hash == GENESIS_PARENT_HASH || self.blocks.get(&rtxn, &block.header.prev_hash)?.is_some();
        let orphan_target = self.orphan_target(&rtxn)?;
        drop(rtxn);

        if !parent_known {
            // Only the proof of work, and only against a relaxed
            // target: everything else (and the real target) is checked
            // once the parent is known and this is accepted for real.
            if !block.header.pow_valid(&orphan_target) {
                return Err(Error::OrphanPowTooWeak);
            }
            if self.orphans.len() >= self.max_orphans {
                self.orphans.remove(0);
            }
            self.orphans.push((hash, block));
            return Ok(AcceptOutcome::Orphaned);
        }

        let mut wtxn = storage.write_txn()?;
        self.store_side_branch_block(&mut wtxn, &block)?;
        wtxn.commit()?;

        let mut wtxn = storage.write_txn()?;
        let candidate_work = self.chain_work(&wtxn, hash)?;
        let active_work = self.chain_work(&wtxn, self.tip_hash(&wtxn)?)?;
        if candidate_work <= active_work {
            return Ok(AcceptOutcome::StoredAsSideBranch);
        }

        let fork_point = self.find_fork_point(&wtxn, hash)?.ok_or(Error::ReorgTooDeep)?;

        // A block stored before one of its ancestors was found invalid
        // (a sibling branch off the bad block, say) gets past the
        // parent check above -- catch it here, before unwinding anything.
        let mut first_invalid = None;
        for (i, replay_block) in fork_point.replay.iter().enumerate() {
            if self.is_known_invalid(&wtxn, replay_block.header.hash())? {
                first_invalid = Some(i);
                break;
            }
        }
        if let Some(i) = first_invalid {
            drop(wtxn);
            self.mark_invalid(&fork_point.replay[i..])?;
            return Err(Error::KnownInvalidBlock);
        }

        for _ in 0..fork_point.unwind_count {
            self.unwind_tip(&mut wtxn)?;
        }
        let applied = fork_point.replay.len() as u64;
        for (i, replay_block) in fork_point.replay.iter().enumerate() {
            if let Err(e) = self.apply_block_in_txn(&mut wtxn, replay_block) {
                // Abort the reorg first -- the active chain must come
                // out of this exactly as it went in.
                drop(wtxn);
                if e.is_block_fault() {
                    self.mark_invalid(&fork_point.replay[i..])?;
                }
                return Err(e);
            }
        }
        self.prune(&mut wtxn)?;
        wtxn.commit()?;

        Ok(AcceptOutcome::Reorged {
            unwound: fork_point.unwind_count,
            applied,
        })
    }

    /// Retry every orphan waiting on `newly_known_hash`, now that it's
    /// actually known -- and, transitively, anything that in turn was
    /// waiting on one of *those* once they're connected. Returns each
    /// retried orphan's outcome, in the order they were retried; only
    /// tests look at them (`accept_block` discards them).
    fn connect_orphans(&mut self, newly_known_hash: [u8; 32]) -> Vec<Result<AcceptOutcome>> {
        let mut outcomes = Vec::new();
        let mut queue = vec![newly_known_hash];
        while let Some(parent_hash) = queue.pop() {
            let (waiting, rest): (Vec<_>, Vec<_>) = std::mem::take(&mut self.orphans)
                .into_iter()
                .partition(|(_, orphan)| orphan.header.prev_hash == parent_hash);
            self.orphans = rest;
            for (orphan_hash, orphan) in waiting {
                let outcome = self.accept_one(orphan);
                if outcome.as_ref().is_ok_and(is_connected) {
                    queue.push(orphan_hash);
                }
                outcomes.push(outcome);
            }
        }
        outcomes
    }

    /// Build a prospective block out of `transactions`: fold each into a
    /// fresh `BlockBody` (failing if any doesn't verify on its own
    /// terms), then resolve and speculatively apply that body against
    /// real chain state -- in its own write transaction, deliberately
    /// never committed -- to compute the `state_root`/`output_count` it
    /// would actually produce.
    ///
    /// Returns an `UnprovenBlock`, not a `Block`: there's no proof yet
    /// (that's `prover::prove_block`'s job, needing the same
    /// `transactions`), and no `Block` can exist without one (see
    /// `BlockBody`'s docs) -- which is exactly what keeps
    /// `pow::mine_block`-ing something from happening before proving
    /// does. Mining itself is also not this function's job either way:
    /// it's chain-state-independent work, usually a hot loop, that
    /// doesn't need to re-resolve anything per attempt.
    pub fn build_block(&mut self, transactions: &[Transaction]) -> Result<UnprovenBlock> {
        let body = BlockBody::from_transactions(transactions).map_err(Error::InvalidTransaction)?;
        // Without the proof, which doesn't exist yet -- `Block::validate`
        // checks the finished block, proof included.
        if crate::block::HEADER_LEN + body.encoded_len() > crate::block::MAX_BLOCK_BYTES {
            return Err(Error::BlockTooLarge);
        }

        let storage = self.storage.clone();
        let mut wtxn = storage.write_txn()?;
        let (prev_hash, height) = self.next_prev_hash_and_height(&wtxn)?;
        let min_timestamp = self.tip_header(&wtxn)?.map_or(0, |parent| parent.timestamp + 1);
        let target = self.current_target(&wtxn)?;
        // The chunks to prove it in, and so the order its outputs are
        // appended in: each chunk's transactions' commitments, by their
        // place in the body.
        let plan_chunks = crate::prover::plan_chunks(transactions).ok_or(Error::TransactionTooLarge)?;
        let index = |list: &[[u8; 32]], c: &[u8; 32]| list.binary_search(c).map_err(|_| Error::InvalidBlock);
        let mut chunks: ChunkIndices = Vec::with_capacity(plan_chunks.len());
        for txs in &plan_chunks {
            let (mut ins, mut outs) = (Vec::new(), Vec::new());
            for &t in txs {
                for input in &transactions[t].inputs {
                    ins.push(index(&body.inputs, &crate::output::Output::new(&input.pubkey, input.amount).commitment())?);
                }
                for output in &transactions[t].outputs {
                    outs.push(index(&body.outputs, &output.commitment())?);
                }
            }
            ins.sort_unstable();
            outs.sort_unstable();
            chunks.push((ins, outs));
        }
        let (state_root, output_count, _spent_inputs, transitions) = self.resolve_and_apply(&mut wtxn, &body, &chunks, true)?;
        // Deliberately never committed -- see the module docs. `wtxn`
        // drops here, and LMDB aborts it.

        Ok(UnprovenBlock {
            prev_hash,
            height,
            target,
            min_timestamp,
            state_root,
            output_count,
            inputs: body.inputs,
            outputs: body.outputs,
            nonces: body.nonces,
            plan: crate::prover::BlockPlan {
                chunks: plan_chunks,
                body_chunks: chunks,
                transitions,
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block::{BlockHeader, INITIAL_MAX_HASH, mine_block};
    use crate::output::Output;
    use crate::prover;
    use crate::wots::{self, PublicKey, SecretKey};
    use std::sync::atomic::{AtomicU64, Ordering};

    struct TempDir(std::path::PathBuf);

    impl TempDir {
        fn new() -> Self {
            static COUNTER: AtomicU64 = AtomicU64::new(0);
            let n = COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!("chain-test-{}-{n}", std::process::id()));
            std::fs::create_dir_all(&path).unwrap();
            TempDir(path)
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    /// Deliberately small -- so a test can actually build past it
    /// (exercising `Error::ReorgTooDeep`) without mining hundreds of
    /// blocks to get there. Same reasoning as `DifficultyConfig::
    /// for_tests`'s own numbers.
    const TEST_MAX_REORG_DEPTH: u64 = 5;

    fn open() -> (TempDir, Storage, Chain) {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut chain = Chain::open(&storage, DifficultyConfig::for_tests(), TEST_MAX_REORG_DEPTH, None).unwrap();
        chain.skip_proof_checks();
        (dir, storage, chain)
    }

    fn keypair(byte: u8) -> (SecretKey, PublicKey) {
        wots::keygen(&[byte; 32])
    }

    fn commitment_of(pubkey: &PublicKey, amount: u64) -> [u8; 32] {
        Output::new(pubkey, amount).commitment()
    }

    /// A one-output, zero-input transaction -- the shape a miner's
    /// reward claim takes (see `block`'s module docs: there's no
    /// separate "coinbase" concept, it's just an ordinary transaction
    /// with no inputs).
    fn reward_transaction(pubkey: &PublicKey, amount: u64) -> Transaction {
        let mut tx = Transaction::new();
        tx.add_output(Output::new(pubkey, amount)).unwrap();
        tx
    }

    /// A one-input, one-output transaction spending `(from_sk, from_pk,
    /// amount)` entirely to `to_pk`, fully signed.
    fn spend_transaction(
        from_sk: &SecretKey,
        from_pk: &PublicKey,
        amount: u64,
        to_pk: &PublicKey,
    ) -> Transaction {
        let mut tx = Transaction::new();
        tx.add_input(from_pk, amount).unwrap();
        tx.add_output(Output::new(to_pk, amount)).unwrap();
        assert!(tx.sign_input(from_pk, from_sk));
        tx
    }

    /// Run the real `build_block` -> `prover::prove_block` ->
    /// `UnprovenBlock::finish` -> `mine_block` pipeline end to end,
    /// panicking if any stage fails -- for tests that just want a real,
    /// minable `Block` out of `transactions` without re-deriving all four
    /// steps inline every time.
    fn built_proved_and_mined(chain: &mut Chain, transactions: &[Transaction]) -> Block {
        let unproven = chain.build_block(transactions).unwrap();
        let target = unproven.target;
        let proof = prover::Proof::placeholder();
        let mut block = unproven.finish(proof);
        assert!(mine_block(&mut block, &target, 100_000), "should find a nonce quickly");
        block
    }

    /// A fully independent chain of `length` blocks, from its own
    /// genesis -- a fresh, throwaway `Chain`/`Storage` entirely
    /// separate from whatever's under test, used to build a
    /// competing branch to feed into it via `accept_block`.
    /// `key_offset` just needs to differ from whatever keys the
    /// caller's own chain used, so the two don't coincidentally reuse
    /// the exact same (pubkey, amount) commitment.
    fn build_chain(length: u64, key_offset: u8) -> Vec<Block> {
        let (_dir, _storage, mut chain) = open();
        let mut blocks = Vec::new();
        for i in 0..length {
            let (_sk, pk) = keypair(key_offset.wrapping_add(i as u8));
            let block = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);
            chain.apply_block(&block).unwrap();
            blocks.push(block);
        }
        blocks
    }

    fn unwind_committed(storage: &Storage, chain: &mut Chain) -> Block {
        let mut wtxn = storage.write_txn().unwrap();
        let block = chain.unwind_tip(&mut wtxn).unwrap();
        wtxn.commit().unwrap();
        block
    }

    /// Download the state as of active-chain block `hash` from `reader`,
    /// piece by piece, as a fast-syncing node does.
    fn download_state(reader: &StateReader, hash: [u8; 32], header: &BlockHeader) -> Vec<crate::state_tree::Entry> {
        let mut plan = crate::snapshot::Plan::new(header.state_root, header.output_count);
        while let Some(piece) = plan.next() {
            let bytes = reader.piece(hash, piece.level, piece.index).unwrap().unwrap();
            assert!(plan.accept(&piece, &bytes));
        }
        plan.finish()
    }

    /// Fast sync, natively (`docs/CHAIN_RECURSION.md`, 5d): chain A, with
    /// spends scattered through its history, serves its state as of block
    /// H (a few blocks back) from its current tree and undo data; chain B
    /// downloads it piece by piece, starts at H, then applies H+1 .. tip
    /// as any node does -- and ends in exactly A's state. B then serves
    /// the same state itself, and refuses anything below H.
    #[test]
    fn fast_sync_from_a_state_snapshot() {
        let (_da, storage_a, mut a) = open();
        let mut blocks = Vec::new();
        let mut live: Vec<(SecretKey, PublicKey)> = Vec::new();
        for i in 0..12u8 {
            let mut txs = Vec::new();
            for j in 0..3u8 {
                let (sk, pk) = wots::keygen(&std::array::from_fn(|n| [1, i, j].get(n).copied().unwrap_or(0)));
                txs.push(reward_transaction(&pk, 50));
                live.push((sk, pk));
            }
            // Spend two older outputs: one ancient, one recent.
            if i >= 3 {
                for k in [0, live.len() - 5] {
                    let (sk, pk) = live.remove(k);
                    let (_, to) = wots::keygen(&std::array::from_fn(|n| [2, i, k as u8].get(n).copied().unwrap_or(0)));
                    txs.push(spend_transaction(&sk, &pk, 50, &to));
                }
            }
            let block = built_proved_and_mined(&mut a, &txs);
            a.apply_block(&block).unwrap();
            blocks.push(block);
        }
        let h = 8usize;
        let base = &blocks[h];
        let reader_a = StateReader::open(&storage_a).unwrap();
        let point = reader_a.sync_point(base.header.hash()).unwrap().unwrap();
        let unspent = download_state(&reader_a, base.header.hash(), &base.header);
        assert!(!unspent.is_empty());

        // A snapshot missing an output is refused.
        let (_dc, _sc, mut c) = open();
        assert!(matches!(c.import_snapshot(base, &point, &[], &unspent[1..]), Err(Error::StateRootMismatch)));

        let (_db, storage_b, mut b) = open();
        b.import_snapshot(base, &point, &[], &unspent).unwrap();
        assert!(!crate::wallet::ChainView::has_full_history(&b.view().unwrap()));
        for block in &blocks[h + 1..] {
            assert_eq!(b.accept_block(block.clone()).unwrap(), AcceptOutcome::Applied);
        }
        let (ra, rb) = (storage_a.read_txn().unwrap(), storage_b.read_txn().unwrap());
        assert_eq!(b.tip_hash(&rb).unwrap(), a.tip_hash(&ra).unwrap());
        assert_eq!(b.state.root(&rb).unwrap(), a.state.root(&ra).unwrap());
        assert_eq!(b.current_target(&rb).unwrap(), a.current_target(&ra).unwrap());
        assert_eq!(b.chain_work(&rb, b.tip_hash(&rb).unwrap()).unwrap(), a.chain_work(&ra, a.tip_hash(&ra).unwrap()).unwrap());
        assert_eq!(b.state.unspent_in(&rb, 0, 1 << 40).unwrap(), a.state.unspent_in(&ra, 0, 1 << 40).unwrap());
        for (_, pk) in &live {
            let c = commitment_of(pk, 50);
            assert_eq!(b.utxo.get(&rb, c).unwrap(), a.utxo.get(&ra, c).unwrap());
        }
        drop((ra, rb));

        // B serves the state as of H+1 just as A does.
        let reader_b = StateReader::open(&storage_b).unwrap();
        let next = &blocks[h + 1];
        assert_eq!(download_state(&reader_b, next.header.hash(), &next.header), download_state(&reader_a, next.header.hash(), &next.header));
        assert_eq!(reader_b.sync_point(next.header.hash()).unwrap(), reader_a.sync_point(next.header.hash()).unwrap());
        // Nothing below the sync point: not served, not accepted.
        assert_eq!(reader_b.piece(blocks[h - 1].header.hash(), 32, 0).unwrap(), None);
        assert!(matches!(b.accept_block(blocks[h - 1].clone()), Err(Error::ReorgTooDeep)));
        // A fresh chain only.
        assert!(matches!(b.import_snapshot(base, &point, &[], &unspent), Err(Error::Snapshot(_))));
    }

    /// The key correctness property, same spirit as `state_tree`'s undo
    /// round-trip tests: unwinding the tip must restore *exactly* the
    /// state that existed right before that block was ever applied --
    /// not just a plausible-looking state.
    #[test]
    fn unwind_tip_restores_state_to_right_before_that_block() {
        let (_dir, storage, mut chain) = open();
        let (_sk_a, pk_a) = keypair(1);
        let block1 = built_proved_and_mined(&mut chain, &[reward_transaction(&pk_a, 50)]);
        chain.apply_block(&block1).unwrap();

        let rtxn = storage.read_txn().unwrap();
        let tip_after_block1 = chain.tip_hash(&rtxn).unwrap();
        let height_after_block1 = chain.height(&rtxn).unwrap();
        let root_after_block1 = chain.state.root(&rtxn).unwrap();
        let count_after_block1 = chain.state.count(&rtxn).unwrap();
        let target_after_block1 = chain.current_target(&rtxn).unwrap();
        drop(rtxn);

        let (_sk_b, pk_b) = keypair(2);
        let block2 = built_proved_and_mined(&mut chain, &[reward_transaction(&pk_b, 50)]);
        chain.apply_block(&block2).unwrap();

        let unwound = unwind_committed(&storage, &mut chain);
        assert_eq!(unwound.header.hash(), block2.header.hash());

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), tip_after_block1);
        assert_eq!(chain.height(&rtxn).unwrap(), height_after_block1);
        assert_eq!(chain.state.root(&rtxn).unwrap(), root_after_block1);
        assert_eq!(chain.state.count(&rtxn).unwrap(), count_after_block1);
        assert_eq!(chain.current_target(&rtxn).unwrap(), target_after_block1);
        // block2's own output must be gone again.
        assert_eq!(chain.utxo.get(&rtxn, commitment_of(&pk_b, 50)).unwrap(), None);
        // block1's output must still be exactly where it was.
        assert!(chain.utxo.get(&rtxn, commitment_of(&pk_a, 50)).unwrap().is_some());
    }

    #[test]
    fn unwind_tip_all_the_way_to_genesis_restores_empty_state() {
        let (_dir, storage, mut chain) = open();
        let (_sk, pk) = keypair(1);
        let block = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);
        chain.apply_block(&block).unwrap();

        unwind_committed(&storage, &mut chain);

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), GENESIS_PARENT_HASH);
        assert_eq!(chain.height(&rtxn).unwrap(), None);
        assert_eq!(chain.state.count(&rtxn).unwrap(), 0);
        assert_eq!(chain.current_target(&rtxn).unwrap(), DifficultyConfig::for_tests().initial_target);
        assert_eq!(chain.utxo.get(&rtxn, commitment_of(&pk, 50)).unwrap(), None);
    }

    /// The property that actually matters for a reorg: unwinding a
    /// spend must make the spent output live again, at the exact same
    /// position, not just remove the record that it was ever spent.
    #[test]
    fn unwind_tip_reverses_a_spend() {
        let (_dir, storage, mut chain) = open();
        let (sk_a, pk_a) = keypair(1);
        let block1 = built_proved_and_mined(&mut chain, &[reward_transaction(&pk_a, 50)]);
        chain.apply_block(&block1).unwrap();

        let rtxn = storage.read_txn().unwrap();
        let position_a = chain.utxo.get(&rtxn, commitment_of(&pk_a, 50)).unwrap().unwrap();
        drop(rtxn);

        let (_sk_b, pk_b) = keypair(2);
        let spend = spend_transaction(&sk_a, &pk_a, 50, &pk_b);
        let block2 = built_proved_and_mined(&mut chain, &[spend]);
        chain.apply_block(&block2).unwrap();

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.utxo.get(&rtxn, commitment_of(&pk_a, 50)).unwrap(), None);
        assert!((chain.state.leaf_at(&rtxn, position_a).unwrap() == crate::state_tree::SPENT));
        drop(rtxn);

        unwind_committed(&storage, &mut chain);

        let rtxn = storage.read_txn().unwrap();
        // pk_a's output is live again, at the exact same position.
        assert_eq!(
            chain.utxo.get(&rtxn, commitment_of(&pk_a, 50)).unwrap(),
            Some(position_a)
        );
        assert!(!(chain.state.leaf_at(&rtxn, position_a).unwrap() == crate::state_tree::SPENT));
        // pk_b's output (created by the now-undone block) is gone.
        assert_eq!(chain.utxo.get(&rtxn, commitment_of(&pk_b, 50)).unwrap(), None);
    }

    /// The output index records every output with its height and nonce;
    /// spending leaves the record (recovery needs spent outputs too);
    /// unwinding the block that created an output removes it.
    #[test]
    fn the_output_index_follows_the_active_chain() {
        let (_dir, storage, mut chain) = open();
        let (sk_a, pk_a) = keypair(1);
        let mut reward = Transaction::new();
        reward.add_output(Output::new(&pk_a, 50).with_nonce([7; NONCE_LEN])).unwrap();
        let block0 = built_proved_and_mined(&mut chain, &[reward]);
        assert_eq!(block0.body.nonces, vec![[7; NONCE_LEN]]);
        chain.apply_block(&block0).unwrap();

        let (_sk_b, pk_b) = keypair(2);
        let mut spend = Transaction::new();
        spend.add_input(&pk_a, 50).unwrap();
        spend.add_output(Output::new(&pk_b, 50).with_nonce([9; NONCE_LEN])).unwrap();
        assert!(spend.sign_input(&pk_a, &sk_a));
        let block1 = built_proved_and_mined(&mut chain, &[spend]);
        chain.apply_block(&block1).unwrap();

        let (a, b) = (commitment_of(&pk_a, 50), commitment_of(&pk_b, 50));
        let rtxn = storage.read_txn().unwrap();
        let record = |c| chain.output_record(&rtxn, &c).unwrap();
        assert_eq!(record(a), Some(OutputRecord { commitment: a, height: 0, nonce: [7; NONCE_LEN] }), "spent, still recorded");
        assert_eq!(record(b), Some(OutputRecord { commitment: b, height: 1, nonce: [9; NONCE_LEN] }));
        let mut seen = Vec::new();
        chain.for_each_output(&rtxn, |r, unspent| seen.push((r.commitment, unspent))).unwrap();
        seen.sort();
        let mut expected = vec![(a, false), (b, true)];
        expected.sort();
        assert_eq!(seen, expected);
        drop(rtxn);

        unwind_committed(&storage, &mut chain);
        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.output_record(&rtxn, &b).unwrap(), None, "its block was unwound");
        assert!(chain.output_record(&rtxn, &a).unwrap().is_some());
    }

    /// Unwinding a block that completed a retarget window must restore
    /// `current_target` to what it was *before* that retarget, not
    /// just leave it at whatever it became.
    #[test]
    fn unwind_tip_restores_retargeting_state_across_a_window_boundary() {
        let (_dir, storage, mut chain) = open();
        let interval = DifficultyConfig::for_tests().interval;
        let initial_target = DifficultyConfig::for_tests().initial_target;

        let mut last_block = None;
        for i in 0..interval {
            let (_sk, pk) = keypair((i + 1) as u8);
            let block = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);
            chain.apply_block(&block).unwrap();
            last_block = Some(block);
        }
        let last_block = last_block.unwrap();

        let rtxn = storage.read_txn().unwrap();
        let target_after_window = chain.current_target(&rtxn).unwrap();
        drop(rtxn);
        // The window completing is what this test is actually
        // exercising -- if this doesn't hold, the rest is moot.
        assert_ne!(target_after_window, initial_target);

        let unwound = unwind_committed(&storage, &mut chain);
        assert_eq!(unwound.header.hash(), last_block.header.hash());

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.current_target(&rtxn).unwrap(), initial_target);
        assert_eq!(chain.height(&rtxn).unwrap(), Some(interval - 2));
    }

    #[test]
    fn chain_work_of_the_genesis_parent_is_zero() {
        let (_dir, storage, chain) = open();
        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.chain_work(&rtxn, GENESIS_PARENT_HASH).unwrap(), [0u8; 32]);
    }

    #[test]
    fn chain_work_accumulates_across_blocks() {
        let (_dir, storage, mut chain) = open();
        let initial_target = DifficultyConfig::for_tests().initial_target;
        let per_block_work = pow::work_for_target(initial_target);

        let (_sk, pk) = keypair(1);
        let block1 = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);
        chain.apply_block(&block1).unwrap();

        let rtxn = storage.read_txn().unwrap();
        let work1 = chain.chain_work(&rtxn, block1.header.hash()).unwrap();
        assert_eq!(work1, per_block_work);
        drop(rtxn);

        // No retarget has happened yet (well within one window), so
        // the second block is mined against the same target too.
        let (_sk2, pk2) = keypair(2);
        let block2 = built_proved_and_mined(&mut chain, &[reward_transaction(&pk2, 50)]);
        chain.apply_block(&block2).unwrap();

        let rtxn = storage.read_txn().unwrap();
        let work2 = chain.chain_work(&rtxn, block2.header.hash()).unwrap();
        assert_eq!(work2, pow::add256(work1, per_block_work));
    }

    #[test]
    fn empty_chain_has_the_genesis_parent_as_its_tip() {
        let (_dir, storage, chain) = open();
        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), GENESIS_PARENT_HASH);
    }

    #[test]
    fn empty_chain_has_no_height() {
        let (_dir, storage, chain) = open();
        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.height(&rtxn).unwrap(), None);
    }

    #[test]
    fn height_advances_by_one_with_every_applied_block() {
        let (_dir, storage, mut chain) = open();
        let (_sk, pk) = keypair(1);

        let block1 = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);
        chain.apply_block(&block1).unwrap();
        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.height(&rtxn).unwrap(), Some(0));
        drop(rtxn);

        let (_sk2, pk2) = keypair(2);
        let block2 = built_proved_and_mined(&mut chain, &[reward_transaction(&pk2, 50)]);
        chain.apply_block(&block2).unwrap();
        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.height(&rtxn).unwrap(), Some(1));
    }

    /// Mine and apply `DifficultyConfig::for_tests().interval` blocks,
    /// each `ms_apart` after the last, starting from an arbitrary
    /// (but fixed, and comfortably in the past) timestamp -- enough to
    /// complete exactly one retarget window, so the test can check what
    /// `current_target` became afterward.
    fn apply_one_window(chain: &mut Chain, ms_apart: u64) {
        let mut timestamp = 1_000_000u64;
        for i in 0..DifficultyConfig::for_tests().interval {
            let (_sk, pk) = keypair((i + 1) as u8);
            let unproven = chain.build_block(&[reward_transaction(&pk, 50)]).unwrap();
            let target = unproven.target;
            let proof = prover::Proof::placeholder();
            let mut block = unproven.finish(proof);
            block.header.timestamp = timestamp;
            assert!(mine_block(&mut block, &target, 100_000), "should find a nonce quickly");
            chain.apply_block(&block).unwrap();
            timestamp += ms_apart;
        }
    }

    /// With `DifficultyConfig::for_tests()` (`interval: 10`,
    /// `target_block_time_ms: 10`, `max_adjustment_factor: 4`), one
    /// window spans 9 gaps and is expected to take `10 * 9 = 90`
    /// milliseconds, clamped to `[90/4, 90*4] = [22, 360]` before scaling.
    #[test]
    fn retargets_harder_after_a_window_that_ran_faster_than_target() {
        let (_dir, storage, mut chain) = open();
        // Nine gaps of 1 ms each (elapsed = 9) is unmistakably
        // faster than the 90ms expectation, and clamped up to the
        // floor of 22 before scaling -- not scaled by the raw 9/90.
        apply_one_window(&mut chain, 1);

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.current_target(&rtxn).unwrap(), pow::scale(INITIAL_MAX_HASH, 22, 90));
    }

    #[test]
    fn retargets_easier_after_a_window_that_ran_slower_than_target() {
        let (_dir, storage, mut chain) = open();
        // Nine gaps of 100ms each (elapsed = 900) is unmistakably
        // slower, and clamped down to the ceiling of 360 before
        // scaling -- not scaled by the raw 900/90 (which would be 10x,
        // past the 4x limit).
        apply_one_window(&mut chain, 100);

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.current_target(&rtxn).unwrap(), pow::scale(INITIAL_MAX_HASH, 360, 90));
    }

    /// A window whose elapsed time falls *within* the clamp -- so the
    /// scaling is driven by the real ratio, not just pegged to one of
    /// the clamp's bounds. Nine gaps of 5ms (elapsed = 45) is
    /// exactly half of the 90ms expectation.
    #[test]
    fn retargets_proportionally_when_within_the_clamp() {
        let (_dir, storage, mut chain) = open();
        apply_one_window(&mut chain, 5);

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.current_target(&rtxn).unwrap(), pow::scale(INITIAL_MAX_HASH, 45, 90));
    }

    /// Unlike `apply_one_window`, which fakes `timestamp` by hand, this
    /// never touches it at all -- `UnprovenBlock::finish` stamps every
    /// block with the real clock (`block::now_millis`), so this
    /// exercises retargeting against genuinely real elapsed time, not
    /// a simulated stand-in for it. Only practical to do quickly
    /// because `DifficultyConfig::for_tests()`'s window is
    /// milliseconds, not seconds (see that method's docs): ten trivial
    /// blocks, mined back to back with no injected delay, run in this
    /// test in well under a second of wall-clock test time.
    ///
    /// The assertion deliberately doesn't predict a *direction*. The
    /// first version of this test assumed ten trivial blocks would
    /// obviously finish faster than the 90ms window and asserted the
    /// target would harden -- and promptly failed, because
    /// `apply_block` commits one real LMDB write transaction per
    /// block, and `fsync`-on-commit durability makes that genuinely
    /// slow and unpredictable in a sandboxed environment (slower, in
    /// fact, than the 90ms budget here). That's a real example of
    /// exactly why wall-clock-timing assertions are riskier than the
    /// rest of this test suite: the *fact* that real elapsed time
    /// drives retargeting is what's actually safe to assert, not which
    /// way a given machine's disk happens to push it.
    #[test]
    fn retargeting_reacts_to_genuinely_real_elapsed_time() {
        let (_dir, storage, mut chain) = open();

        let rtxn = storage.read_txn().unwrap();
        let initial_target = chain.current_target(&rtxn).unwrap();
        drop(rtxn);

        for i in 0..DifficultyConfig::for_tests().interval {
            let (_sk, pk) = keypair((i + 1) as u8);
            let unproven = chain.build_block(&[reward_transaction(&pk, 50)]).unwrap();
            let target = unproven.target;
            let proof = prover::Proof::placeholder();
            let mut block = unproven.finish(proof); // timestamp: the real clock, untouched
            assert!(mine_block(&mut block, &target, 100_000), "should find a nonce quickly");
            chain.apply_block(&block).unwrap();
        }

        let rtxn = storage.read_txn().unwrap();
        let new_target = chain.current_target(&rtxn).unwrap();
        assert_ne!(
            new_target, initial_target,
            "expected a real, ~90ms window to retarget away from the initial target in *some* direction"
        );
    }

    #[test]
    fn target_is_unchanged_mid_window() {
        let (_dir, storage, mut chain) = open();
        let (_sk, pk) = keypair(1);
        // One block in (out of RETARGET_INTERVAL) -- nowhere near a
        // window boundary, so the target must still be the initial one.
        let block = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);
        chain.apply_block(&block).unwrap();

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.current_target(&rtxn).unwrap(), INITIAL_MAX_HASH);
    }

    #[test]
    fn build_block_produces_an_unproven_block_chaining_onto_the_tip() {
        let (_dir, _storage, mut chain) = open();
        let (_sk, pk) = keypair(1);
        let tx = reward_transaction(&pk, 50);

        let unproven = chain.build_block(&[tx]).unwrap();
        assert_eq!(unproven.prev_hash, GENESIS_PARENT_HASH);
        assert_eq!(unproven.outputs, vec![commitment_of(&pk, 50)]);
    }

    #[test]
    fn finish_assembles_a_block_whose_body_hash_matches_but_is_not_yet_mined() {
        let (_dir, _storage, mut chain) = open();
        let (_sk, pk) = keypair(1);
        let tx = reward_transaction(&pk, 50);

        let unproven = chain.build_block(&[tx]).unwrap();
        let proof = prover::Proof::placeholder();
        let block = unproven.finish(proof);

        assert_eq!(block.header.body_hash, block.body.body_hash());
        // Not mined -- finish's job stops at assembling the fields, not
        // finding a satisfying nonce.
        assert!(!block.header.pow_valid(&INITIAL_MAX_HASH));
    }

    #[test]
    fn build_block_rejects_a_transaction_that_does_not_verify() {
        let (_dir, _storage, mut chain) = open();
        let (_sk, pk) = keypair(1);
        // An input with no signature at all: fails `Transaction::verify()`.
        let mut bad = Transaction::new();
        bad.add_input(&pk, 10).unwrap();

        let err = chain.build_block(&[bad]).unwrap_err();
        assert!(matches!(err, Error::InvalidTransaction(0)));
    }

    #[test]
    fn build_then_apply_roundtrips_and_advances_the_tip() {
        let (_dir, storage, mut chain) = open();
        let (_sk, pk) = keypair(1);
        let tx = reward_transaction(&pk, 50);

        let block = built_proved_and_mined(&mut chain, &[tx]);
        assert!(block.validate_structure(&INITIAL_MAX_HASH));

        chain.apply_block(&block).unwrap();

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), block.header.hash());

        let commitment = commitment_of(&pk, 50);
        let position = chain.utxo.get(&rtxn, commitment).unwrap();
        assert!(position.is_some());
        assert_ne!(chain.state.leaf_at(&rtxn, position.unwrap()).unwrap(), crate::state_tree::SPENT);
        assert_eq!(chain.state.root(&rtxn).unwrap(), block.header.state_root);
        assert_eq!(chain.state.count(&rtxn).unwrap(), block.header.output_count);
    }

    #[test]
    fn a_second_block_chains_onto_the_first_and_can_spend_its_output() {
        let (_dir, storage, mut chain) = open();
        let (sk_a, pk_a) = keypair(1);
        let (_sk_b, pk_b) = keypair(2);

        let block1 = built_proved_and_mined(&mut chain, &[reward_transaction(&pk_a, 50)]);
        chain.apply_block(&block1).unwrap();

        let spend = spend_transaction(&sk_a, &pk_a, 50, &pk_b);
        let block2 = built_proved_and_mined(&mut chain, &[spend]);
        assert_eq!(block2.header.prev_hash, block1.header.hash());

        chain.apply_block(&block2).unwrap();

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), block2.header.hash());
        // A's output is spent now: gone from the live utxo set.
        assert_eq!(chain.utxo.get(&rtxn, commitment_of(&pk_a, 50)).unwrap(), None);
        // B's output is live.
        assert!(chain.utxo.get(&rtxn, commitment_of(&pk_b, 50)).unwrap().is_some());
    }

    #[test]
    fn apply_block_rejects_a_block_that_fails_its_own_validate() {
        let (_dir, _storage, mut chain) = open();
        let (_sk, pk) = keypair(1);
        let unproven = chain.build_block(&[reward_transaction(&pk, 50)]).unwrap();
        let proof = prover::Proof::placeholder();
        // Leave the nonce unmined -- pow_valid() will be false, so
        // validate() fails before chain state is even consulted.
        let block = unproven.finish(proof);

        let err = chain.apply_block(&block).unwrap_err();
        assert!(matches!(err, Error::InvalidBlock));
    }

    #[test]
    fn apply_block_rejects_a_wrong_parent_hash() {
        let (_dir, _storage, mut chain) = open();
        let (_sk, pk) = keypair(1);
        let mut unproven = chain.build_block(&[reward_transaction(&pk, 50)]).unwrap();
        unproven.prev_hash = [0xffu8; 32];
        let target = unproven.target;
        let proof = prover::Proof::placeholder();
        let mut block = unproven.finish(proof);
        assert!(mine_block(&mut block, &target, 100_000));

        let err = chain.apply_block(&block).unwrap_err();
        assert!(matches!(err, Error::WrongParent));
    }

    /// `prev_hash` can be made to match the real tip while `height`
    /// still doesn't -- these are independent checks, and this confirms
    /// `height` is actually enforced, not just carried along for show.
    #[test]
    fn apply_block_rejects_a_wrong_height() {
        let (_dir, _storage, mut chain) = open();
        let (_sk, pk) = keypair(1);
        let mut unproven = chain.build_block(&[reward_transaction(&pk, 50)]).unwrap();
        unproven.height = 1; // the real first block must be height 0
        let target = unproven.target;
        let proof = prover::Proof::placeholder();
        let mut block = unproven.finish(proof);
        assert!(mine_block(&mut block, &target, 100_000));

        let err = chain.apply_block(&block).unwrap_err();
        assert!(matches!(err, Error::WrongHeight));
    }

    #[test]
    fn apply_block_rejects_a_timestamp_too_far_in_the_future() {
        let (_dir, _storage, mut chain) = open();
        let (_sk, pk) = keypair(1);
        let unproven = chain.build_block(&[reward_transaction(&pk, 50)]).unwrap();
        let target = unproven.target;
        let proof = prover::Proof::placeholder();
        let mut block = unproven.finish(proof);
        // Comfortably past MAX_FUTURE_DRIFT_MS -- re-mined since
        // changing `timestamp` changes the PoW preimage.
        block.header.timestamp = now_millis() + MAX_FUTURE_DRIFT_MS + 3600;
        assert!(mine_block(&mut block, &target, 100_000));

        let err = chain.apply_block(&block).unwrap_err();
        assert!(matches!(err, Error::TimestampTooFarInFuture));
    }

    #[test]
    fn apply_block_accepts_a_timestamp_within_the_future_tolerance() {
        let (_dir, _storage, mut chain) = open();
        let (_sk, pk) = keypair(1);
        let unproven = chain.build_block(&[reward_transaction(&pk, 50)]).unwrap();
        let target = unproven.target;
        let proof = prover::Proof::placeholder();
        let mut block = unproven.finish(proof);
        // Just inside the tolerance -- must not be rejected on that
        // basis alone.
        block.header.timestamp = now_millis() + MAX_FUTURE_DRIFT_MS - 1;
        assert!(mine_block(&mut block, &target, 100_000));

        chain.apply_block(&block).unwrap();
    }

    /// `build_block` runs the exact same resolution `apply_block` does
    /// (see the module docs), so an unresolvable input is actually
    /// caught right there, before a block even exists to apply.
    #[test]
    fn build_block_rejects_an_input_that_never_existed() {
        let (_dir, _storage, mut chain) = open();
        let (sk_a, pk_a) = keypair(1);
        let (_sk_b, pk_b) = keypair(2);
        // Nothing has ever created this output, so spending it can't
        // resolve.
        let spend = spend_transaction(&sk_a, &pk_a, 50, &pk_b);

        let err = chain.build_block(&[spend]).unwrap_err();
        assert!(matches!(err, Error::UnresolvedInput(c) if c == commitment_of(&pk_a, 50)));
    }

    /// Constructed by hand rather than via `build_block`, so this checks
    /// `apply_block`'s own resolution independently -- not just that
    /// `build_block` happens to catch the same thing first.
    #[test]
    fn apply_block_rejects_an_input_that_never_existed() {
        let (_dir, _storage, mut chain) = open();
        let (sk_a, pk_a) = keypair(1);
        let (_sk_b, pk_b) = keypair(2);

        let mut body = BlockBody::new();
        assert!(body.add_transaction(&spend_transaction(&sk_a, &pk_a, 50, &pk_b)));
        let header = BlockHeader {
            prev_hash: GENESIS_PARENT_HASH,
            state_root: [0u8; 32],
            output_count: 0,
            body_hash: body.body_hash(),
            height: 0,
            timestamp: 0,
            nonce: [0u8; 32],
        };
        let mut block = Block { header, body };
        assert!(mine_block(&mut block, &INITIAL_MAX_HASH, 100_000));

        let err = chain.apply_block(&block).unwrap_err();
        assert!(matches!(err, Error::UnresolvedInput(c) if c == commitment_of(&pk_a, 50)));
    }

    #[test]
    fn apply_block_rejects_an_output_colliding_with_a_still_live_one() {
        let (_dir, _storage, mut chain) = open();
        let (_sk, pk) = keypair(1);

        let block1 = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);
        chain.apply_block(&block1).unwrap();

        // The exact same (pubkey, amount) again -- same commitment,
        // still live from block1, so this must be rejected rather than
        // silently creating a second, indistinguishable entry.
        let err = chain.build_block(&[reward_transaction(&pk, 50)]).unwrap_err();
        assert!(matches!(err, Error::DuplicateOutput(c) if c == commitment_of(&pk, 50)));
    }

    #[test]
    fn reusing_a_commitment_is_fine_once_the_original_is_spent() {
        let (_dir, storage, mut chain) = open();
        let (sk_a, pk_a) = keypair(1);
        let (_sk_b, pk_b) = keypair(2);

        let block1 = built_proved_and_mined(&mut chain, &[reward_transaction(&pk_a, 50)]);
        chain.apply_block(&block1).unwrap();

        let spend = spend_transaction(&sk_a, &pk_a, 50, &pk_b);
        let block2 = built_proved_and_mined(&mut chain, &[spend]);
        chain.apply_block(&block2).unwrap();

        // pk_a/50 is spent now -- recreating the exact same commitment
        // must be allowed, since there's nothing live to collide with.
        let block3 = built_proved_and_mined(&mut chain, &[reward_transaction(&pk_a, 50)]);
        chain.apply_block(&block3).unwrap();

        let rtxn = storage.read_txn().unwrap();
        assert!(chain.utxo.get(&rtxn, commitment_of(&pk_a, 50)).unwrap().is_some());
    }

    /// The whole point of the transactional restructuring: a failed
    /// `apply_block` must leave every store exactly as it was, with
    /// nothing partially written.
    #[test]
    fn a_failed_apply_block_leaves_every_store_untouched() {
        let (_dir, storage, mut chain) = open();
        let (_sk, pk) = keypair(1);

        let mut unproven = chain.build_block(&[reward_transaction(&pk, 50)]).unwrap();
        // Corrupt the claimed root after the fact so resolve_and_apply's
        // real result won't match it -- this fails only after inputs/
        // outputs have already been resolved and written against wtxn,
        // exactly the partial-progress scenario atomicity has to cover.
        unproven.state_root = [0xabu8; 32];
        let target = unproven.target;
        let proof = prover::Proof::placeholder();
        let mut block = unproven.finish(proof);
        assert!(mine_block(&mut block, &target, 100_000));

        let err = chain.apply_block(&block).unwrap_err();
        assert!(matches!(err, Error::StateRootMismatch));

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), GENESIS_PARENT_HASH);
        assert_eq!(chain.utxo.get(&rtxn, commitment_of(&pk, 50)).unwrap(), None);
        assert_eq!(chain.state.count(&rtxn).unwrap(), 0);
    }

    #[test]
    fn accept_block_applies_a_block_that_extends_the_tip() {
        let (_dir, storage, mut chain) = open();
        let (_sk, pk) = keypair(1);
        let block = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);

        assert_eq!(chain.accept_block(block.clone()).unwrap(), AcceptOutcome::Applied);

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), block.header.hash());
    }

    #[test]
    fn accept_block_stores_a_side_branch_without_switching_on_equal_work() {
        let (_dir, storage, mut chain) = open();
        let (_sk_a, pk_a) = keypair(1);
        let active = built_proved_and_mined(&mut chain, &[reward_transaction(&pk_a, 50)]);
        chain.apply_block(&active).unwrap();

        // A single competing block, also extending genesis -- same
        // height, same (default, since neither chain has retargeted)
        // target, so equal work. Built against its own independent
        // chain, never applied there.
        let competing = build_chain(1, 99);
        let competing = competing.into_iter().next().unwrap();

        assert_eq!(chain.accept_block(competing).unwrap(), AcceptOutcome::StoredAsSideBranch);

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), active.header.hash());
    }

    #[test]
    fn accept_block_reorgs_onto_a_heavier_competing_chain() {
        let (_dir, storage, mut chain) = open();
        let (_sk_a, pk_a) = keypair(1);
        let active1 = built_proved_and_mined(&mut chain, &[reward_transaction(&pk_a, 50)]);
        chain.apply_block(&active1).unwrap();
        let (_sk_b, pk_b) = keypair(2);
        let active2 = built_proved_and_mined(&mut chain, &[reward_transaction(&pk_b, 50)]);
        chain.apply_block(&active2).unwrap();

        // A fully independent competing chain, also from genesis, one
        // block longer -- strictly more work (same target throughout;
        // neither chain is anywhere near a retarget window).
        let competing = build_chain(3, 100);

        let mut last_outcome = None;
        for block in competing.iter().cloned() {
            last_outcome = Some(chain.accept_block(block).unwrap());
        }
        assert_eq!(last_outcome, Some(AcceptOutcome::Reorged { unwound: 2, applied: 3 }));

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), competing.last().unwrap().header.hash());
        // The active chain's own outputs are genuinely gone, not just
        // shadowed by the winning branch's.
        assert_eq!(chain.utxo.get(&rtxn, commitment_of(&pk_a, 50)).unwrap(), None);
        assert_eq!(chain.utxo.get(&rtxn, commitment_of(&pk_b, 50)).unwrap(), None);
    }

    /// A competing branch that was stored back when it was still
    /// within reach, but whose fork point the active chain has since
    /// moved more than `TEST_MAX_REORG_DEPTH` past: even once that
    /// branch becomes strictly heavier, it must be refused rather than
    /// attempted.
    #[test]
    fn accept_block_rejects_a_reorg_deeper_than_max_reorg_depth() {
        let (_dir, storage, mut chain) = open();
        let competing = build_chain(TEST_MAX_REORG_DEPTH + 3, 100);

        let mut active_tip = None;
        for i in 0..(TEST_MAX_REORG_DEPTH + 2) {
            let (_sk, pk) = keypair((i + 1) as u8);
            let block = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);
            chain.apply_block(&block).unwrap();
            active_tip = Some(block.header.hash());
            // The competing branch's first two blocks arrive early,
            // while genesis is still within reach.
            if i < 2 {
                let outcome = chain.accept_block(competing[i as usize].clone()).unwrap();
                assert_eq!(outcome, AcceptOutcome::StoredAsSideBranch);
            }
        }

        let mut last_outcome = None;
        for block in competing.into_iter().skip(2) {
            last_outcome = Some(chain.accept_block(block));
        }
        assert!(matches!(last_outcome, Some(Err(Error::ReorgTooDeep))));

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), active_tip.unwrap());
    }

    /// A block that could only ever fork off the active chain further
    /// back than `TEST_MAX_REORG_DEPTH` is refused on arrival -- not
    /// stored, and not pooled as an orphan either.
    #[test]
    fn accept_block_refuses_a_block_at_or_below_the_reorg_floor() {
        let (_dir, storage, mut chain) = open();
        for i in 0..(TEST_MAX_REORG_DEPTH + 2) {
            let (_sk, pk) = keypair((i + 1) as u8);
            let block = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);
            chain.apply_block(&block).unwrap();
        }

        // Active tip is at height 6, so the floor is 1: heights 0 and 1
        // are out of reach.
        let competing = build_chain(2, 100);
        for block in competing.iter().cloned() {
            assert!(matches!(chain.accept_block(block), Err(Error::ReorgTooDeep)));
        }

        let rtxn = storage.read_txn().unwrap();
        assert!(chain.blocks.get(&rtxn, &competing[0].header.hash()).unwrap().is_none());
        assert!(chain.orphans.is_empty());
    }

    /// Two miners neck and neck: the competing branch keeps pace with
    /// the active chain for `TEST_MAX_REORG_DEPTH` blocks, then pulls
    /// ahead by one. The unwind is exactly `TEST_MAX_REORG_DEPTH`
    /// (allowed) even though the branch being replayed is one longer --
    /// the replay side mustn't be held to the unwind limit.
    #[test]
    fn accept_block_reorgs_onto_a_branch_longer_than_max_reorg_depth() {
        let (_dir, storage, mut chain) = open();
        let (_builder_dir, _builder_storage, mut builder) = open();

        let (_sk, pk) = keypair(1);
        let shared = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);
        chain.apply_block(&shared).unwrap();
        builder.apply_block(&shared).unwrap();

        let mut competing = Vec::new();
        for i in 0..=TEST_MAX_REORG_DEPTH {
            let (_sk, pk) = keypair(100 + i as u8);
            let block = built_proved_and_mined(&mut builder, &[reward_transaction(&pk, 50)]);
            builder.apply_block(&block).unwrap();
            competing.push(block);
        }

        for i in 0..TEST_MAX_REORG_DEPTH {
            let (_sk, pk) = keypair(2 + i as u8);
            let block = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);
            chain.apply_block(&block).unwrap();
            let outcome = chain.accept_block(competing[i as usize].clone()).unwrap();
            assert_eq!(outcome, AcceptOutcome::StoredAsSideBranch);
        }

        let last = competing.last().unwrap().clone();
        assert_eq!(
            chain.accept_block(last.clone()).unwrap(),
            AcceptOutcome::Reorged {
                unwound: TEST_MAX_REORG_DEPTH,
                applied: TEST_MAX_REORG_DEPTH + 1
            }
        );

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), last.header.hash());
    }

    #[test]
    fn accept_block_orphans_a_block_with_an_unknown_parent() {
        let (_dir, _storage, mut chain) = open();
        let other = build_chain(2, 1);
        let child = other.into_iter().nth(1).unwrap();

        assert_eq!(chain.accept_block(child).unwrap(), AcceptOutcome::Orphaned);
    }

    #[test]
    fn accepting_a_missing_parent_connects_the_orphans_waiting_on_it() {
        let (_dir, storage, mut chain) = open();
        let mut other = build_chain(3, 1).into_iter();
        let parent = other.next().unwrap();
        let child = other.next().unwrap();
        let grandchild = other.next().unwrap();

        // Out of order: the grandchild first, then the child.
        assert_eq!(chain.accept_block(grandchild.clone()).unwrap(), AcceptOutcome::Orphaned);
        assert_eq!(chain.accept_block(child).unwrap(), AcceptOutcome::Orphaned);
        assert_eq!(chain.accept_block(parent).unwrap(), AcceptOutcome::Applied);

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), grandchild.header.hash());
        assert!(chain.orphans.is_empty());
    }

    #[test]
    fn connect_orphans_reports_each_retried_orphans_outcome() {
        let (_dir, _storage, mut chain) = open();
        let mut other = build_chain(2, 1).into_iter();
        let parent = other.next().unwrap();
        let child = other.next().unwrap();

        assert_eq!(chain.accept_block(child).unwrap(), AcceptOutcome::Orphaned);
        // Bypass `accept_block`'s automatic retry, to see it directly.
        assert_eq!(chain.accept_one(parent.clone()).unwrap(), AcceptOutcome::Applied);

        let outcomes = chain.connect_orphans(parent.header.hash());
        assert_eq!(outcomes.len(), 1);
        assert!(matches!(outcomes[0], Ok(AcceptOutcome::Applied)));
    }

    /// Past `max_orphans`, the *oldest* orphan is the one evicted.
    #[test]
    fn the_orphan_pool_evicts_its_oldest_entry_when_full() {
        let (_dir, storage, mut chain) = open();
        chain.max_orphans = 2;
        let blocks = build_chain(4, 1);

        for block in &blocks[1..] {
            assert_eq!(chain.accept_block(block.clone()).unwrap(), AcceptOutcome::Orphaned);
        }
        // blocks[1] -- the oldest -- was evicted to make room for blocks[3].
        assert_eq!(chain.orphans.len(), 2);

        assert_eq!(chain.accept_block(blocks[0].clone()).unwrap(), AcceptOutcome::Applied);
        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), blocks[0].header.hash());
        drop(rtxn);

        // Once blocks[1] arrives again, the rest connect behind it.
        assert_eq!(chain.accept_block(blocks[1].clone()).unwrap(), AcceptOutcome::Applied);
        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), blocks[3].header.hash());
        assert!(chain.orphans.is_empty());
    }

    #[test]
    fn accept_block_reports_an_already_applied_block_as_already_known() {
        let (_dir, storage, mut chain) = open();
        let (_sk, pk) = keypair(1);
        let block = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);
        assert_eq!(chain.accept_block(block.clone()).unwrap(), AcceptOutcome::Applied);

        assert_eq!(chain.accept_block(block.clone()).unwrap(), AcceptOutcome::AlreadyKnown);

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), block.header.hash());
    }

    #[test]
    fn accept_block_reports_an_already_stored_side_branch_block_as_already_known() {
        let (_dir, _storage, mut chain) = open();
        let (_sk, pk) = keypair(1);
        let active = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);
        chain.apply_block(&active).unwrap();

        let competing = build_chain(1, 99).into_iter().next().unwrap();
        assert_eq!(chain.accept_block(competing.clone()).unwrap(), AcceptOutcome::StoredAsSideBranch);
        assert_eq!(chain.accept_block(competing).unwrap(), AcceptOutcome::AlreadyKnown);
    }

    #[test]
    fn accept_block_does_not_pool_the_same_orphan_twice() {
        let (_dir, _storage, mut chain) = open();
        let mut other = build_chain(2, 1).into_iter();
        let parent = other.next().unwrap();
        let child = other.next().unwrap();

        assert_eq!(chain.accept_block(child.clone()).unwrap(), AcceptOutcome::Orphaned);
        assert_eq!(chain.accept_block(child).unwrap(), AcceptOutcome::AlreadyKnown);

        chain.accept_block(parent).unwrap();
        assert!(chain.orphans.is_empty());
    }

    /// The winning branch shares a real prefix with the active chain
    /// (not just genesis) and spends that prefix's output *differently*
    /// -- the reorg has to un-spend it from the active side and
    /// re-spend it the branch's way, ending with exactly the state a
    /// node that only ever saw the winning branch would have.
    #[test]
    fn accept_block_reorgs_a_mid_chain_fork_that_spends_differently() {
        let (_dir, storage, mut chain) = open();
        let (_builder_dir, builder_storage, mut builder) = open();

        let (sk_a, pk_a) = keypair(1);
        let shared = built_proved_and_mined(&mut chain, &[reward_transaction(&pk_a, 50)]);
        chain.apply_block(&shared).unwrap();
        builder.apply_block(&shared).unwrap();

        let rtxn = storage.read_txn().unwrap();
        let position_a = chain.utxo.get(&rtxn, commitment_of(&pk_a, 50)).unwrap().unwrap();
        drop(rtxn);

        // Active: A -> B.
        let (_sk_b, pk_b) = keypair(2);
        let active2 = built_proved_and_mined(&mut chain, &[spend_transaction(&sk_a, &pk_a, 50, &pk_b)]);
        chain.apply_block(&active2).unwrap();

        // Competing: A -> C, then a fresh reward to D.
        let (_sk_c, pk_c) = keypair(3);
        let competing2 = built_proved_and_mined(&mut builder, &[spend_transaction(&sk_a, &pk_a, 50, &pk_c)]);
        builder.apply_block(&competing2).unwrap();
        let (_sk_d, pk_d) = keypair(4);
        let competing3 = built_proved_and_mined(&mut builder, &[reward_transaction(&pk_d, 50)]);
        builder.apply_block(&competing3).unwrap();

        assert_eq!(chain.accept_block(competing2).unwrap(), AcceptOutcome::StoredAsSideBranch);
        assert_eq!(
            chain.accept_block(competing3.clone()).unwrap(),
            AcceptOutcome::Reorged { unwound: 1, applied: 2 }
        );

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), competing3.header.hash());
        assert_eq!(chain.utxo.get(&rtxn, commitment_of(&pk_a, 50)).unwrap(), None);
        assert!((chain.state.leaf_at(&rtxn, position_a).unwrap() == crate::state_tree::SPENT));
        assert_eq!(chain.utxo.get(&rtxn, commitment_of(&pk_b, 50)).unwrap(), None);
        assert!(chain.utxo.get(&rtxn, commitment_of(&pk_c, 50)).unwrap().is_some());
        assert!(chain.utxo.get(&rtxn, commitment_of(&pk_d, 50)).unwrap().is_some());

        let builder_rtxn = builder_storage.read_txn().unwrap();
        assert_eq!(chain.state.root(&rtxn).unwrap(), builder.state.root(&builder_rtxn).unwrap());
        assert_eq!(chain.state.count(&rtxn).unwrap(), builder.state.count(&builder_rtxn).unwrap());
    }

    /// A heavier branch whose last block is bad (passes its own
    /// `validate`, but claims the wrong `state_root`): the reorg gets as
    /// far as replaying the branch's good blocks before hitting it, and
    /// must then leave the active chain exactly as it was -- and record
    /// the bad block, so a block built on top of it is refused outright
    /// rather than triggering the same doomed reorg again.
    #[test]
    fn a_reorg_onto_a_branch_with_a_bad_block_aborts_and_is_not_retried() {
        let (_dir, storage, mut chain) = open();
        let (_sk_a, pk_a) = keypair(1);
        let active1 = built_proved_and_mined(&mut chain, &[reward_transaction(&pk_a, 50)]);
        chain.apply_block(&active1).unwrap();
        let (_sk_b, pk_b) = keypair(2);
        let active2 = built_proved_and_mined(&mut chain, &[reward_transaction(&pk_b, 50)]);
        chain.apply_block(&active2).unwrap();

        let rtxn = storage.read_txn().unwrap();
        let root_before = chain.state.root(&rtxn).unwrap();
        let count_before = chain.state.count(&rtxn).unwrap();
        drop(rtxn);

        let (_builder_dir, _builder_storage, mut builder) = open();
        let mut good = Vec::new();
        for i in 0..2u8 {
            let (_sk, pk) = keypair(100 + i);
            let block = built_proved_and_mined(&mut builder, &[reward_transaction(&pk, 50)]);
            builder.apply_block(&block).unwrap();
            good.push(block);
        }

        let (_sk_bad, pk_bad) = keypair(102);
        let bad_txs = [reward_transaction(&pk_bad, 50)];
        let mut unproven = builder.build_block(&bad_txs).unwrap();
        unproven.state_root = [0xabu8; 32];
        let target = unproven.target;
        let proof = prover::Proof::placeholder();
        let mut bad = unproven.finish(proof);
        assert!(mine_block(&mut bad, &target, 100_000));

        // Built on top of `bad`, which `builder` itself never applied --
        // only its lineage matters; it should never get as far as
        // having its roots checked.
        let (_sk_after, pk_after) = keypair(103);
        let after_txs = [reward_transaction(&pk_after, 50)];
        let mut unproven = builder.build_block(&after_txs).unwrap();
        unproven.prev_hash = bad.header.hash();
        unproven.height = bad.header.height + 1;
        let proof = prover::Proof::placeholder();
        let mut after = unproven.finish(proof);
        assert!(mine_block(&mut after, &target, 100_000));

        for block in good {
            assert_eq!(chain.accept_block(block).unwrap(), AcceptOutcome::StoredAsSideBranch);
        }
        let err = chain.accept_block(bad.clone()).unwrap_err();
        assert!(matches!(err, Error::StateRootMismatch));

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), active2.header.hash());
        assert_eq!(chain.state.root(&rtxn).unwrap(), root_before);
        assert_eq!(chain.state.count(&rtxn).unwrap(), count_before);
        assert!(chain.utxo.get(&rtxn, commitment_of(&pk_a, 50)).unwrap().is_some());
        assert!(chain.utxo.get(&rtxn, commitment_of(&pk_b, 50)).unwrap().is_some());
        assert!(chain.is_known_invalid(&rtxn, bad.header.hash()).unwrap());
        drop(rtxn);

        assert!(matches!(chain.accept_block(after), Err(Error::KnownInvalidBlock)));
        assert!(matches!(chain.accept_block(bad), Err(Error::KnownInvalidBlock)));

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), active2.header.hash());
    }

    /// The real `build_block` -> prove -> finish -> mine pipeline, like
    /// `built_proved_and_mined`, but with a hand-set `timestamp` -- for
    /// tests that need to steer retargeting.
    fn built_proved_and_mined_at(chain: &mut Chain, transactions: &[Transaction], timestamp: u64) -> Block {
        let unproven = chain.build_block(transactions).unwrap();
        let target = unproven.target;
        let proof = prover::Proof::placeholder();
        let mut block = unproven.finish(proof);
        block.header.timestamp = timestamp;
        assert!(mine_block(&mut block, &target, 100_000), "should find a nonce quickly");
        block
    }

    /// A fork straddling a retarget-window boundary: the two branches
    /// close the window at different speeds, so after it they're on
    /// different targets. The competing branch's first post-window
    /// block meets *its own* (easier) target but deliberately not the
    /// active chain's -- it has to be accepted against the former.
    #[test]
    fn a_side_branch_block_is_checked_against_its_own_branchs_target() {
        let (_dir, storage, mut chain) = open();
        let (_builder_dir, builder_storage, mut builder) = open();
        let interval = DifficultyConfig::for_tests().interval;
        let start = 1_000_000u64;

        // Heights 0..=5, shared.
        for i in 0..6u64 {
            let (_sk, pk) = keypair(1 + i as u8);
            let block = built_proved_and_mined_at(&mut chain, &[reward_transaction(&pk, 50)], start + 10 * i);
            chain.apply_block(&block).unwrap();
            builder.apply_block(&block).unwrap();
        }

        // Heights 6..=9 on each side: active fast (harder after the
        // window), competing slow (easier).
        for i in 6..interval {
            let (_sk, pk) = keypair(1 + i as u8);
            let block = built_proved_and_mined_at(&mut chain, &[reward_transaction(&pk, 50)], start + 50 + (i - 5));
            chain.apply_block(&block).unwrap();
        }
        let mut competing = Vec::new();
        for i in 6..interval {
            let (_sk, pk) = keypair(100 + i as u8);
            let block = built_proved_and_mined_at(&mut builder, &[reward_transaction(&pk, 50)], start + 50 + 100 * (i - 5));
            builder.apply_block(&block).unwrap();
            competing.push(block);
        }

        let rtxn = storage.read_txn().unwrap();
        let active_target = chain.current_target(&rtxn).unwrap();
        drop(rtxn);
        let builder_rtxn = builder_storage.read_txn().unwrap();
        let competing_target = builder.current_target(&builder_rtxn).unwrap();
        drop(builder_rtxn);
        assert!(competing_target > active_target, "competing branch should have retargeted easier");

        // Height 10 on the competing side, re-mined until it meets only
        // the easier target.
        let (_sk, pk) = keypair(200);
        let mut timestamp = start + 1_000;
        let post_window = loop {
            let block = built_proved_and_mined_at(&mut builder, &[reward_transaction(&pk, 50)], timestamp);
            if !block.header.pow_valid(&active_target) {
                break block;
            }
            timestamp += 1;
        };
        builder.apply_block(&post_window).unwrap();
        competing.push(post_window.clone());

        for block in &competing[..competing.len() - 1] {
            assert_eq!(chain.accept_block(block.clone()).unwrap(), AcceptOutcome::StoredAsSideBranch);
        }
        assert_eq!(
            chain.accept_block(post_window.clone()).unwrap(),
            AcceptOutcome::Reorged { unwound: 4, applied: 5 }
        );

        let rtxn = storage.read_txn().unwrap();
        let builder_rtxn = builder_storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), post_window.header.hash());
        assert_eq!(chain.current_target(&rtxn).unwrap(), builder.current_target(&builder_rtxn).unwrap());
        assert_eq!(chain.state.root(&rtxn).unwrap(), builder.state.root(&builder_rtxn).unwrap());
    }

    /// Below `reorg_floor`, side-branch blocks are dropped entirely and
    /// active-chain blocks keep only the block itself (for serving
    /// sync); at or above it, everything is kept, and is exactly enough
    /// to unwind the full `TEST_MAX_REORG_DEPTH`.
    #[test]
    fn blocks_below_the_reorg_floor_are_pruned() {
        let (_dir, storage, mut chain) = open();
        let mut active = Vec::new();
        let (_sk, pk) = keypair(1);
        let first = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);
        chain.apply_block(&first).unwrap();
        active.push(first);

        let side = build_chain(1, 99).into_iter().next().unwrap();
        assert_eq!(chain.accept_block(side.clone()).unwrap(), AcceptOutcome::StoredAsSideBranch);

        for i in 1..8u8 {
            let (_sk, pk) = keypair(1 + i);
            let block = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);
            chain.apply_block(&block).unwrap();
            active.push(block);
        }

        // Tip at height 7, floor at 2: heights 0 and 1 are out of reach.
        let rtxn = storage.read_txn().unwrap();
        assert!(chain.blocks.get(&rtxn, &side.header.hash()).unwrap().is_none());
        for block in active[..2].iter().chain(std::iter::once(&side)) {
            let hash = block.header.hash();
            assert!(chain.block_undo.get(&rtxn, &hash).unwrap().is_none());
            assert!(chain.block_work.get(&rtxn, &hash).unwrap().is_none());
            assert!(chain.block_retarget.get(&rtxn, &hash).unwrap().is_none());
            let key = height_key(block.header.height, hash);
            assert!(chain.block_heights.get(&rtxn, &key).unwrap().is_none());
        }
        // Every active-chain block is still there to be served.
        for block in &active {
            assert!(chain.blocks.get(&rtxn, &block.header.hash()).unwrap().is_some());
        }
        drop(rtxn);

        for _ in 0..TEST_MAX_REORG_DEPTH {
            unwind_committed(&storage, &mut chain);
        }
        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), active[2].header.hash());
    }

    /// `BlockReader` sees the active chain by height, follows unwinds,
    /// and can fetch any stored block -- including a side branch's.
    #[test]
    fn block_reader_tracks_the_active_chain() {
        let (_dir, storage, mut chain) = open();
        let reader = BlockReader::open(&storage).unwrap();
        assert_eq!(reader.tip().unwrap(), None);

        let mut active = Vec::new();
        for i in 0..3u8 {
            let (_sk, pk) = keypair(1 + i);
            let block = built_proved_and_mined(&mut chain, &[reward_transaction(&pk, 50)]);
            chain.apply_block(&block).unwrap();
            active.push(block);
        }
        let side = build_chain(1, 99).into_iter().next().unwrap();
        chain.accept_block(side.clone()).unwrap();

        assert_eq!(reader.tip().unwrap(), Some((2, active[2].header.hash())));
        for (height, block) in active.iter().enumerate() {
            assert_eq!(reader.active_hash_at(height as u64).unwrap(), Some(block.header.hash()));
            assert_eq!(reader.block_bytes(block.header.hash()).unwrap(), Some(block.to_bytes()));
        }
        assert!(reader.has_block(side.header.hash()).unwrap());
        assert_eq!(reader.active_hash_at(3).unwrap(), None);

        unwind_committed(&storage, &mut chain);
        assert_eq!(reader.tip().unwrap(), Some((1, active[1].header.hash())));
        assert_eq!(reader.active_hash_at(2).unwrap(), None);
    }

    /// The retargeting rule, as a pure function, must agree with what
    /// the active chain actually stores block by block.
    #[test]
    fn stored_retarget_state_matches_the_active_chains_own() {
        let (_dir, storage, mut chain) = open();
        apply_one_window(&mut chain, 1);

        let rtxn = storage.read_txn().unwrap();
        let tip = chain.tip_hash(&rtxn).unwrap();
        let stored = chain.retarget_state_after(&rtxn, tip).unwrap();
        assert_eq!(stored.target, chain.current_target(&rtxn).unwrap());
        assert_eq!(stored.window_start_timestamp, chain.window_start_timestamp(&rtxn).unwrap());
    }

    /// Overwrite `block`'s nonce with successive values until `accept`
    /// says yes -- for crafting a header whose proof of work lands in a
    /// specific band of targets.
    fn renonce_until(block: &mut Block, accept: impl Fn(&BlockHeader) -> bool) {
        for n in 0u64..1_000_000 {
            block.header.nonce = [0u8; 32];
            block.header.nonce[24..].copy_from_slice(&n.to_be_bytes());
            if accept(&block.header) {
                return;
            }
        }
        panic!("no nonce found in range");
    }

    #[test]
    fn an_orphan_with_too_little_work_is_refused_and_not_pooled() {
        let (_dir, storage, mut chain) = open();
        let rtxn = storage.read_txn().unwrap();
        let orphan_target = chain.orphan_target(&rtxn).unwrap();
        drop(rtxn);

        let mut orphan = build_chain(2, 1).into_iter().nth(1).unwrap();
        renonce_until(&mut orphan, |header| !header.pow_valid(&orphan_target));

        assert!(matches!(chain.accept_block(orphan), Err(Error::OrphanPowTooWeak)));
        assert!(chain.orphans.is_empty());
    }

    /// An orphan that misses the current target but meets the relaxed
    /// one is still pooled -- the tolerance for a legitimately easier
    /// chain just past a retarget.
    #[test]
    fn an_orphan_meeting_only_the_relaxed_target_is_still_pooled() {
        let (_dir, storage, mut chain) = open();
        let rtxn = storage.read_txn().unwrap();
        let current_target = chain.current_target(&rtxn).unwrap();
        let orphan_target = chain.orphan_target(&rtxn).unwrap();
        drop(rtxn);
        assert!(orphan_target > current_target);

        let mut orphan = build_chain(2, 1).into_iter().nth(1).unwrap();
        renonce_until(&mut orphan, |header| {
            header.pow_valid(&orphan_target) && !header.pow_valid(&current_target)
        });

        assert_eq!(chain.accept_block(orphan).unwrap(), AcceptOutcome::Orphaned);
    }

    /// Each block's timestamp must be strictly later than its parent's:
    /// equal or earlier is rejected, one millisecond later is fine.
    #[test]
    fn a_timestamp_must_be_strictly_later_than_the_parents() {
        let (_dir, storage, mut chain) = open();
        let (_sk, pk) = keypair(1);
        let first = built_proved_and_mined_at(&mut chain, &[reward_transaction(&pk, 50)], 1_000_000);
        chain.apply_block(&first).unwrap();

        let (_sk2, pk2) = keypair(2);
        for timestamp in [1_000_000, 999_999] {
            let block = built_proved_and_mined_at(&mut chain, &[reward_transaction(&pk2, 50)], timestamp);
            assert!(matches!(chain.apply_block(&block), Err(Error::TimestampNotAfterParent)), "at {timestamp}");
        }
        let block = built_proved_and_mined_at(&mut chain, &[reward_transaction(&pk2, 50)], 1_000_001);
        chain.apply_block(&block).unwrap();

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), block.header.hash());
    }

    /// The same rule holds for a block arriving on a side branch.
    #[test]
    fn a_side_branch_block_must_also_be_later_than_its_parent() {
        let (_dir, _storage, mut chain) = open();
        let (_builder_dir, _builder_storage, mut builder) = open();
        let (_sk, pk) = keypair(1);
        let shared = built_proved_and_mined_at(&mut chain, &[reward_transaction(&pk, 50)], 1_000_000);
        chain.apply_block(&shared).unwrap();
        builder.apply_block(&shared).unwrap();
        let (_sk2, pk2) = keypair(2);
        let active = built_proved_and_mined_at(&mut chain, &[reward_transaction(&pk2, 50)], 1_000_010);
        chain.apply_block(&active).unwrap();

        // A competing child of `shared`, stamped before it. `builder`
        // never applies it, only builds it.
        let (_sk3, pk3) = keypair(3);
        let backdated = built_proved_and_mined_at(&mut builder, &[reward_transaction(&pk3, 50)], 999_000);
        assert!(matches!(chain.accept_block(backdated), Err(Error::TimestampNotAfterParent)));
    }

    /// `build_block` tells the miner the earliest timestamp it may use,
    /// and `finish` never stamps anything earlier -- even when the parent
    /// claims a time ahead of this node's clock.
    #[test]
    fn build_block_carries_the_minimum_timestamp_forward() {
        let (_dir, _storage, mut chain) = open();
        let (_sk, pk) = keypair(1);
        let ahead = now_millis() + 60_000; // within MAX_FUTURE_DRIFT_MS
        let first = built_proved_and_mined_at(&mut chain, &[reward_transaction(&pk, 50)], ahead);
        chain.apply_block(&first).unwrap();

        let (_sk2, pk2) = keypair(2);
        let transactions = [reward_transaction(&pk2, 50)];
        let unproven = chain.build_block(&transactions).unwrap();
        assert_eq!(unproven.min_timestamp, ahead + 1);
        let target = unproven.target;
        let proof = prover::Proof::placeholder();
        let mut block = unproven.finish(proof);
        assert_eq!(block.header.timestamp, ahead + 1);
        assert!(mine_block(&mut block, &target, 100_000));
        chain.apply_block(&block).unwrap();
    }

    /// With a fixed genesis, no other block is ever accepted at height 0
    /// -- not even as a side branch.
    #[test]
    fn a_chain_with_a_fixed_genesis_refuses_any_other_first_block() {
        let (_builder_dir, _builder_storage, mut builder) = open();
        let (_sk, pk) = keypair(1);
        let genesis = built_proved_and_mined(&mut builder, &[reward_transaction(&pk, 50)]);
        let (_other_dir, _other_storage, mut other_builder) = open();
        let (_sk2, pk2) = keypair(2);
        let impostor = built_proved_and_mined(&mut other_builder, &[reward_transaction(&pk2, 50)]);

        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut chain = Chain::open(&storage, DifficultyConfig::for_tests(), TEST_MAX_REORG_DEPTH, Some(&genesis)).unwrap();
        chain.skip_proof_checks();
        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), genesis.header.hash());
        drop(rtxn);

        assert!(matches!(chain.accept_block(impostor), Err(Error::WrongGenesis)));
        assert_eq!(chain.accept_block(genesis).unwrap(), AcceptOutcome::AlreadyKnown);
    }

    /// With proof checks on (as outside tests they always are), a block
    /// carrying a real proof of its transactions is accepted, and the same
    /// block with a placeholder proof in its place is refused.
    /// Proves a real block (a chunk proof and its wrap): minutes; run
    /// with `cargo test --release -- --ignored a_chain_checking_proofs`.
    #[test]
    #[ignore]
    fn a_chain_checking_proofs_accepts_only_a_really_proven_block() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut chain = Chain::open(&storage, DifficultyConfig::for_tests(), TEST_MAX_REORG_DEPTH, None).unwrap();
        let (_sk, pk) = keypair(1);
        let transactions = [reward_transaction(&pk, prover::REWARD)];

        let unproven = chain.build_block(&transactions).unwrap();
        let target = unproven.target;
        let min_timestamp = unproven.min_timestamp;
        let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &unproven.nonces, &transactions, &unproven.plan, [3; 32]).unwrap();
        let mut real = unproven.finish(proof);
        real.header.timestamp = real.header.timestamp.max(min_timestamp);
        assert!(mine_block(&mut real, &target, 100_000));

        let mut fake = real.clone();
        fake.body.proof = prover::Proof::placeholder();
        fake.header.body_hash = fake.body.body_hash();
        assert!(mine_block(&mut fake, &target, 100_000));
        assert!(matches!(chain.apply_block(&fake), Err(Error::InvalidBlock)));

        chain.apply_block(&real).unwrap();
    }
}
