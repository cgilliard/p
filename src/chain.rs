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
//! for it. What this module *does* check is everything structural: does
//! this block chain onto the current tip, does every input resolve to a
//! real, currently-unspent output, does every output avoid colliding with
//! one that's still live, and do the roots that result from applying it
//! match what the header claims.
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

#![allow(dead_code)]

use crate::bitmap::Bitmap;
use crate::block::{Block, BlockBody, UnprovenBlock};
use crate::pmmr::Pmmr;
use crate::storage::Storage;
use crate::transaction::Transaction;
use crate::utxo::UtxoIndex;
use heed::Database;
use heed::types::Bytes;

/// The `prev_hash` an empty chain's first block must declare -- there's
/// no real prior header to point to, so this stands in for "no parent."
pub const GENESIS_PARENT_HASH: [u8; 32] = [0u8; 32];

const TIP_HASH_KEY: &[u8] = b"tip_hash";
const NEXT_HEIGHT_KEY: &[u8] = b"next_height";

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
}

impl Chain {
    /// Open (creating if absent) a chain's full state within the given
    /// storage context.
    pub fn open(storage: &Storage) -> Result<Self> {
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
        })
    }

    /// The current tip's header hash, or `GENESIS_PARENT_HASH` if no
    /// block has ever been applied.
    pub fn tip_hash(&self, txn: &heed::RoTxn) -> Result<[u8; 32]> {
        match self.meta.get(txn, TIP_HASH_KEY)? {
            Some(bytes) => bytes
                .try_into()
                .map_err(|_| Error::Corrupt("tip hash was not 32 bytes")),
            None => Ok(GENESIS_PARENT_HASH),
        }
    }

    /// The height of the next block this chain will accept: `0` for an
    /// empty chain (the first block ever applied lands at height `0`),
    /// incrementing by one with every successful `apply_block`. Kept as
    /// a side field here rather than on `BlockHeader` -- see
    /// `block::HEADER_LEN`'s docs: it's fully recoverable from `Chain`'s
    /// own count of applied blocks (or, more expensively, by walking
    /// `prev_hash` all the way back), so spending header space on it
    /// would be pure redundancy.
    fn next_height(&self, txn: &heed::RoTxn) -> Result<u64> {
        match self.meta.get(txn, NEXT_HEIGHT_KEY)? {
            Some(bytes) => bytes
                .try_into()
                .map(u64::from_be_bytes)
                .map_err(|_| Error::Corrupt("next height was not 8 bytes")),
            None => Ok(0),
        }
    }

    /// The current tip's height, or `None` if no block has ever been
    /// applied (there is no height to report yet).
    pub fn height(&self, txn: &heed::RoTxn) -> Result<Option<u64>> {
        let next = self.next_height(txn)?;
        Ok(if next == 0 { None } else { Some(next - 1) })
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
    /// Checked, in order: `block.validate()` (proof of work, canonical
    /// ordering, no same-block spend, `body_hash` matches); that
    /// `prev_hash` chains onto the current tip; that every input
    /// resolves and every output avoids colliding with a live one; and
    /// that the roots applying the body actually produces match what the
    /// header claims.
    pub fn apply_block(&mut self, block: &Block) -> Result<()> {
        if !block.validate() {
            return Err(Error::InvalidBlock);
        }

        // A local, cloned handle (just an `Arc` bump -- see `Storage`'s
        // docs) rather than `self.storage.write_txn()` directly: that
        // would tie `wtxn`'s lifetime to a borrow of `self` itself,
        // which would then conflict with the `&mut self` calls below.
        let storage = self.storage.clone();
        let mut wtxn = storage.write_txn()?;

        if block.header.prev_hash != self.tip_hash(&wtxn)? {
            return Err(Error::WrongParent);
        }

        let (pmmr_root, bitmap_root) = self.resolve_and_apply(&mut wtxn, &block.body)?;
        if pmmr_root != block.header.pmmr_root {
            return Err(Error::PmmrRootMismatch);
        }
        if bitmap_root != block.header.bitmap_root {
            return Err(Error::BitmapRootMismatch);
        }

        let next_height = self.next_height(&wtxn)? + 1;
        self.meta.put(&mut wtxn, TIP_HASH_KEY, &block.header.hash())?;
        self.meta.put(&mut wtxn, NEXT_HEIGHT_KEY, &next_height.to_be_bytes())?;
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
        let prev_hash = self.tip_hash(&wtxn)?;
        let (pmmr_root, bitmap_root) = self.resolve_and_apply(&mut wtxn, &body)?;
        // Deliberately never committed -- see the module docs. `wtxn`
        // drops here, and LMDB aborts it.

        Ok(UnprovenBlock {
            prev_hash,
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
    use crate::block::{BlockHeader, mine_block};
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
        let chain = Chain::open(&storage).unwrap();
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
        let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, transactions).unwrap();
        let mut block = unproven.finish(proof);
        assert!(mine_block(&mut block, 100_000), "should find a nonce quickly");
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
        assert!(!block.header.pow_valid());
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
        assert!(block.validate());

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
        let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &[]).unwrap();
        let mut block = unproven.finish(proof);
        assert!(mine_block(&mut block, 100_000));

        let err = chain.apply_block(&block).unwrap_err();
        assert!(matches!(err, Error::WrongParent));
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
            timestamp: 0,
            nonce: [0u8; 32],
        };
        let mut block = Block { header, body };
        assert!(mine_block(&mut block, 100_000));

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
        let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &[]).unwrap();
        let mut block = unproven.finish(proof);
        assert!(mine_block(&mut block, 100_000));

        let err = chain.apply_block(&block).unwrap_err();
        assert!(matches!(err, Error::PmmrRootMismatch));

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), GENESIS_PARENT_HASH);
        assert_eq!(chain.utxo.get(&rtxn, commitment_of(&pk, 50)).unwrap(), None);
        assert_eq!(chain.pmmr.leaf_count(&rtxn).unwrap(), 0);
    }
}
