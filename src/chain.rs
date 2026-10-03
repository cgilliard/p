//! Chain-state-dependent block processing: resolving a block's inputs and
//! outputs against the real `Pmmr`/`Bitmap`/`UtxoIndex`, applying the
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
//! for it. The same is true of timestamp *monotonicity* (each block's
//! `timestamp` not preceding the one before it): it's a per-block rule
//! that only gives a whole-chain guarantee once composed recursively,
//! same shape as the balance equation -- see `docs/BLOCK_TODO.md` #3,
//! and `prover`'s docs once that lands there.
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
//! `Pmmr`, `Bitmap`, and `UtxoIndex` hold no in-memory state of their own
//! to desync -- every read and write they do goes through a caller-
//! supplied LMDB transaction (see each module's docs). That's what lets
//! `apply_block` update all three through one shared `heed::RwTxn` and
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
//! landing roughly `DifficultyConfig::target_block_time_secs` apart,
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

use crate::bitmap::Bitmap;
use crate::block::{Block, BlockBody, BlockHeader, UnprovenBlock, now_unix};
use crate::pmmr::Pmmr;
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
/// allowed to claim to be -- same order of magnitude as Bitcoin's
/// 2-hour rule. This can never be part of any proof, recursive or
/// otherwise: it's a statement about the relationship between a
/// timestamp and whenever *this particular check* happens to run, not
/// a fact fixed at proving time (see `docs/BLOCK_TODO.md` #3). Every
/// verifier -- full node or light client -- has to check this locally,
/// against its own clock, no matter how much of the rest of chain
/// validity eventually gets folded into a recursive proof.
const MAX_FUTURE_DRIFT_SECS: u64 = 2 * 60 * 60;

/// The tip's full header, the one thing `Chain` persists in its own
/// `chain_meta` database beyond what `pmmr`/`bitmap`/`utxo` already
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
    /// take, in seconds, if mining is keeping pace with the target.
    pub target_block_time_secs: u64,
    /// How far the actual/expected elapsed-time ratio is allowed to
    /// swing before being clamped, each retarget -- `4` means at most
    /// 4x harder or 4x easier per window. Bitcoin's own value.
    pub max_adjustment_factor: u64,
}

impl DifficultyConfig {
    /// Fast, cheap-to-mine defaults for tests: `block::INITIAL_MAX_HASH`
    /// (the easy target everything else in this crate's test suite is
    /// already built around) and a short window, so a test can
    /// actually complete a full retarget window without mining
    /// hundreds of blocks to get there.
    pub fn for_tests() -> Self {
        DifficultyConfig {
            initial_target: crate::block::INITIAL_MAX_HASH,
            interval: 10,
            target_block_time_secs: 10,
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

#[derive(Debug)]
pub enum Error {
    Storage(crate::storage::Error),
    Heed(heed::Error),
    Pmmr(crate::pmmr::Error),
    Bitmap(crate::bitmap::Error),
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
    /// clock than `MAX_FUTURE_DRIFT_SECS` allows.
    TimestampTooFarInFuture,
    /// An input commitment doesn't resolve to a currently unspent output.
    UnresolvedInput([u8; 32]),
    /// An output's commitment collides with one that's already live
    /// (created, and not yet spent).
    DuplicateOutput([u8; 32]),
    /// Applying the body produced a PMMR root different from the one the
    /// header claims.
    PmmrRootMismatch,
    /// Applying the body produced a bitmap root different from the one
    /// the header claims.
    BitmapRootMismatch,
    /// One of the transactions handed to `build_block` failed its own
    /// `Transaction::verify()` -- the index is its position in the slice
    /// that was passed in.
    InvalidTransaction(usize),
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

impl From<crate::pmmr::Error> for Error {
    fn from(e: crate::pmmr::Error) -> Self {
        Error::Pmmr(e)
    }
}

impl From<crate::bitmap::Error> for Error {
    fn from(e: crate::bitmap::Error) -> Self {
        Error::Bitmap(e)
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
            Error::Pmmr(e) => write!(f, "pmmr error: {e}"),
            Error::Bitmap(e) => write!(f, "bitmap error: {e}"),
            Error::Utxo(e) => write!(f, "utxo error: {e}"),
            Error::Corrupt(msg) => write!(f, "corrupt chain metadata: {msg}"),
            Error::InvalidBlock => write!(f, "block failed its own validate()"),
            Error::WrongParent => write!(f, "block does not chain onto the current tip"),
            Error::WrongHeight => write!(f, "block's height is not exactly one more than the current tip's"),
            Error::TimestampTooFarInFuture => write!(f, "header timestamp is too far ahead of this node's clock"),
            Error::UnresolvedInput(c) => write!(f, "input {} does not resolve to a live unspent output", hex(c)),
            Error::DuplicateOutput(c) => write!(f, "output {} collides with a still-live output", hex(c)),
            Error::PmmrRootMismatch => write!(f, "header's pmmr_root does not match the result of applying the body"),
            Error::BitmapRootMismatch => write!(f, "header's bitmap_root does not match the result of applying the body"),
            Error::InvalidTransaction(i) => write!(f, "transaction at index {i} failed verify()"),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

fn hex(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// A full node's chain state: the real `Pmmr`, `Bitmap`, and `UtxoIndex`,
/// plus the metadata none of those three know about on their own -- which
/// header is the current tip, and at what height.
pub struct Chain {
    storage: Storage,
    pmmr: Pmmr,
    bitmap: Bitmap,
    utxo: UtxoIndex,
    meta: Database<Bytes, Bytes>,
    difficulty: DifficultyConfig,
}

impl Chain {
    /// Open (creating if absent) a chain's full state within the given
    /// storage context, retargeting according to `difficulty` (see
    /// `DifficultyConfig`'s docs -- in particular, why the right
    /// values for a test and for an actual run are never the same
    /// numbers).
    pub fn open(storage: &Storage, difficulty: DifficultyConfig) -> Result<Self> {
        let pmmr = Pmmr::open(storage)?;
        let bitmap = Bitmap::open(storage)?;
        let utxo = UtxoIndex::open(storage)?;
        let meta = storage.database("chain_meta")?;
        Ok(Chain {
            storage: storage.clone(),
            pmmr,
            bitmap,
            utxo,
            meta,
            difficulty,
        })
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

    /// Update retargeting's side state for the window `applied_header`
    /// just landed in, through `wtxn` -- called once a block has
    /// already passed every other check in `apply_block`, right before
    /// it's committed. Two things can happen, and at most one ever does
    /// for a given block (see the module docs): if `applied_header`
    /// opens a new window, its timestamp becomes the new
    /// `window_start_timestamp`; if it closes one, the window's actual
    /// elapsed time, clamped to within `max_adjustment_factor` of what
    /// was expected, becomes the ratio `current_target` is scaled by
    /// (Bitcoin's own rule -- see the module docs).
    fn retarget_if_due(&mut self, wtxn: &mut heed::RwTxn, applied_header: &BlockHeader) -> Result<()> {
        let height = applied_header.height;
        let interval = self.difficulty.interval;

        if height.is_multiple_of(interval) {
            self.meta
                .put(wtxn, WINDOW_START_TIMESTAMP_KEY, &applied_header.timestamp.to_be_bytes())?;
        }

        if (height + 1).is_multiple_of(interval) {
            let window_start = self.window_start_timestamp(wtxn)?;
            let elapsed = applied_header.timestamp.saturating_sub(window_start);
            let expected = self.difficulty.target_block_time_secs * (interval - 1);
            let factor = self.difficulty.max_adjustment_factor;
            let clamped_elapsed = elapsed.clamp(expected / factor, expected * factor);

            let old_target = self.current_target(wtxn)?;
            let new_target = pow::scale(old_target, clamped_elapsed, expected);
            self.meta.put(wtxn, CURRENT_TARGET_KEY, &new_target)?;
        }

        Ok(())
    }

    /// Resolve and apply `body`'s inputs and outputs against real chain
    /// state, through `wtxn`: every input must resolve to a currently
    /// live (unspent) output, which is then marked spent in `bitmap` and
    /// removed from `utxo`; every output must not collide with one still
    /// live, and is then appended to `pmmr` and recorded in `utxo`.
    /// Returns the resulting `(pmmr_root, bitmap_root)`. Nothing here is
    /// specific to a real header -- `apply_block` checks the result
    /// against one, `build_block` just wants the roots -- and nothing
    /// here commits `wtxn`; that's always the caller's job.
    fn resolve_and_apply(
        &mut self,
        wtxn: &mut heed::RwTxn,
        body: &BlockBody,
    ) -> Result<([u8; 32], [u8; 32])> {
        for commitment in &body.inputs {
            let position = self
                .utxo
                .get(wtxn, *commitment)?
                .ok_or(Error::UnresolvedInput(*commitment))?;
            self.bitmap.set(wtxn, position, true)?;
            self.utxo.remove(wtxn, *commitment)?;
        }

        for commitment in &body.outputs {
            if self.utxo.get(wtxn, *commitment)?.is_some() {
                return Err(Error::DuplicateOutput(*commitment));
            }
            let position = self.pmmr.push(wtxn, *commitment)?;
            self.utxo.insert(wtxn, *commitment, position)?;
        }

        let pmmr_root = self.pmmr.root(wtxn)?;
        let bitmap_root = self.bitmap.root(wtxn)?;
        Ok((pmmr_root, bitmap_root))
    }

    /// Apply `block` to the chain: resolve its inputs/outputs against
    /// real state, update `pmmr`/`bitmap`/`utxo`, and advance the tip --
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
        if block.header.timestamp > now_unix() + MAX_FUTURE_DRIFT_SECS {
            return Err(Error::TimestampTooFarInFuture);
        }

        // A local, cloned handle (just an `Arc` bump -- see `Storage`'s
        // docs) rather than `self.storage.write_txn()` directly: that
        // would tie `wtxn`'s lifetime to a borrow of `self` itself,
        // which would then conflict with the `&mut self` calls below.
        let storage = self.storage.clone();
        let mut wtxn = storage.write_txn()?;

        let target = self.current_target(&wtxn)?;
        if !block.validate(&target) {
            return Err(Error::InvalidBlock);
        }

        let (expected_prev_hash, expected_height) = self.next_prev_hash_and_height(&wtxn)?;
        if block.header.prev_hash != expected_prev_hash {
            return Err(Error::WrongParent);
        }
        if block.header.height != expected_height {
            return Err(Error::WrongHeight);
        }

        let (pmmr_root, bitmap_root) = self.resolve_and_apply(&mut wtxn, &block.body)?;
        if pmmr_root != block.header.pmmr_root {
            return Err(Error::PmmrRootMismatch);
        }
        if bitmap_root != block.header.bitmap_root {
            return Err(Error::BitmapRootMismatch);
        }

        self.retarget_if_due(&mut wtxn, &block.header)?;
        self.meta.put(&mut wtxn, TIP_HEADER_KEY, &block.header.to_bytes())?;
        wtxn.commit()?;
        Ok(())
    }

    /// Build a prospective block out of `transactions`: fold each into a
    /// fresh `BlockBody` (failing if any doesn't verify on its own
    /// terms), then resolve and speculatively apply that body against
    /// real chain state -- in its own write transaction, deliberately
    /// never committed -- to compute the `pmmr_root`/`bitmap_root` it
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

        let storage = self.storage.clone();
        let mut wtxn = storage.write_txn()?;
        let (prev_hash, height) = self.next_prev_hash_and_height(&wtxn)?;
        let target = self.current_target(&wtxn)?;
        let (pmmr_root, bitmap_root) = self.resolve_and_apply(&mut wtxn, &body)?;
        // Deliberately never committed -- see the module docs. `wtxn`
        // drops here, and LMDB aborts it.

        Ok(UnprovenBlock {
            prev_hash,
            height,
            target,
            pmmr_root,
            bitmap_root,
            inputs: body.inputs,
            outputs: body.outputs,
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

    fn open() -> (TempDir, Storage, Chain) {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let chain = Chain::open(&storage, DifficultyConfig::for_tests()).unwrap();
        (dir, storage, chain)
    }

    fn keypair(byte: u8) -> (SecretKey, PublicKey) {
        wots::keygen(&[byte; 32])
    }

    fn commitment_of(pubkey: &PublicKey, amount: u64) -> [u8; 32] {
        crate::poseidon2::hash_bytes_32(&Output::new(pubkey, amount).to_bytes())
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
        let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, transactions).unwrap();
        let mut block = unproven.finish(proof);
        assert!(mine_block(&mut block, &target, 100_000), "should find a nonce quickly");
        block
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
    /// each `seconds_apart` after the last, starting from an arbitrary
    /// (but fixed, and comfortably in the past) timestamp -- enough to
    /// complete exactly one retarget window, so the test can check what
    /// `current_target` became afterward.
    fn apply_one_window(chain: &mut Chain, seconds_apart: u64) {
        let mut timestamp = 1_000_000u64;
        for i in 0..DifficultyConfig::for_tests().interval {
            let (_sk, pk) = keypair((i + 1) as u8);
            let unproven = chain.build_block(&[reward_transaction(&pk, 50)]).unwrap();
            let target = unproven.target;
            let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &[]).unwrap();
            let mut block = unproven.finish(proof);
            block.header.timestamp = timestamp;
            assert!(mine_block(&mut block, &target, 100_000), "should find a nonce quickly");
            chain.apply_block(&block).unwrap();
            timestamp += seconds_apart;
        }
    }

    /// With `DifficultyConfig::for_tests()` (`interval: 10`,
    /// `target_block_time_secs: 10`, `max_adjustment_factor: 4`), one
    /// window spans 9 gaps and is expected to take `10 * 9 = 90`
    /// seconds, clamped to `[90/4, 90*4] = [22, 360]` before scaling.
    #[test]
    fn retargets_harder_after_a_window_that_ran_faster_than_target() {
        let (_dir, storage, mut chain) = open();
        // Nine gaps of 1 second each (elapsed = 9) is unmistakably
        // faster than the 90-second expectation, and clamped up to the
        // floor of 22 before scaling -- not scaled by the raw 9/90.
        apply_one_window(&mut chain, 1);

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.current_target(&rtxn).unwrap(), pow::scale(INITIAL_MAX_HASH, 22, 90));
    }

    #[test]
    fn retargets_easier_after_a_window_that_ran_slower_than_target() {
        let (_dir, storage, mut chain) = open();
        // Nine gaps of 100 seconds each (elapsed = 900) is unmistakably
        // slower, and clamped down to the ceiling of 360 before
        // scaling -- not scaled by the raw 900/90 (which would be 10x,
        // past the 4x limit).
        apply_one_window(&mut chain, 100);

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.current_target(&rtxn).unwrap(), pow::scale(INITIAL_MAX_HASH, 360, 90));
    }

    /// A window whose elapsed time falls *within* the clamp -- so the
    /// scaling is driven by the real ratio, not just pegged to one of
    /// the clamp's bounds. Nine gaps of 5 seconds (elapsed = 45) is
    /// exactly half of the 90-second expectation.
    #[test]
    fn retargets_proportionally_when_within_the_clamp() {
        let (_dir, storage, mut chain) = open();
        apply_one_window(&mut chain, 5);

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.current_target(&rtxn).unwrap(), pow::scale(INITIAL_MAX_HASH, 45, 90));
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
        let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &[]).unwrap();
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
        assert!(block.validate(&INITIAL_MAX_HASH));

        chain.apply_block(&block).unwrap();

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), block.header.hash());

        let commitment = commitment_of(&pk, 50);
        let position = chain.utxo.get(&rtxn, commitment).unwrap();
        assert!(position.is_some());
        assert!(!chain.bitmap.get(&rtxn, position.unwrap()).unwrap());
        assert_eq!(chain.pmmr.root(&rtxn).unwrap(), block.header.pmmr_root);
        assert_eq!(chain.bitmap.root(&rtxn).unwrap(), block.header.bitmap_root);
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
        let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &[]).unwrap();
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
        let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &[]).unwrap();
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
        let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &[]).unwrap();
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
        let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &[]).unwrap();
        let mut block = unproven.finish(proof);
        // Comfortably past MAX_FUTURE_DRIFT_SECS -- re-mined since
        // changing `timestamp` changes the PoW preimage.
        block.header.timestamp = now_unix() + MAX_FUTURE_DRIFT_SECS + 3600;
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
        let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &[]).unwrap();
        let mut block = unproven.finish(proof);
        // Just inside the tolerance -- must not be rejected on that
        // basis alone.
        block.header.timestamp = now_unix() + MAX_FUTURE_DRIFT_SECS - 1;
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
            pmmr_root: [0u8; 32],
            bitmap_root: [0u8; 32],
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
        unproven.pmmr_root = [0xabu8; 32];
        let target = unproven.target;
        let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &[]).unwrap();
        let mut block = unproven.finish(proof);
        assert!(mine_block(&mut block, &target, 100_000));

        let err = chain.apply_block(&block).unwrap_err();
        assert!(matches!(err, Error::PmmrRootMismatch));

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), GENESIS_PARENT_HASH);
        assert_eq!(chain.utxo.get(&rtxn, commitment_of(&pk, 50)).unwrap(), None);
        assert_eq!(chain.pmmr.leaf_count(&rtxn).unwrap(), 0);
    }
}
