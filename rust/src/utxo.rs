//! A UTXO index: a reverse lookup from an output's commitment hash to its
//! position in the state tree (`state_tree`). Stored in the same record per
//! output as the output index (`OUTPUTS_DB`) -- one entry per output, not
//! two. This is the piece `chain`
//! validation needs to turn a spend into "where in the state tree is the
//! real output it's spending" -- without it, there's no way to check a spend against real
//! chain state at all.
//!
//! Keyed by the *full commitment* `H(H(pubkey) || amount)` -- the same
//! hash the state tree holds as the leaf, and the same hash both a spend
//! (`block::BlockBody.inputs`) and the output that created it
//! (`block::BlockBody.outputs`) publish. Deliberately **not** keyed by
//! `pubkey_hash` alone: this index, like the state tree and the published block
//! body, never sees a plaintext `pubkey` or `amount` -- only the opaque
//! commitment -- which is what hides both. The value is just `position`;
//! there's no `amount` to store here anymore, since nothing on this side
//! of a proof ever learns it.
//!
//! This is a genuine *unspent* output set, not just a static reverse
//! index: an entry is inserted when an output is created and removed the
//! moment it's spent (`remove`), so a lookup naturally returns `None` for
//! anything already spent or never created -- the same shape as a real
//! UTXO set, and a second line of defense against double-spending a
//! position within a block, on top of the state tree's own spent leaves.
//!
//! Because the key folds in `amount`, two outputs that happen to share a
//! public key no longer collide the way they would under a
//! `pubkey_hash`-only key, *unless* they also share the exact same
//! amount (in which case they're indistinguishable anyway). `insert` is
//! still a plain, unconditional write with no safety check of its own --
//! that judgment call (is a new output allowed to reuse a key that's
//! still live) belongs to `chain` validation, which can call `get` first.
//!
//! Backed by LMDB via the same shared `storage::Storage` context the state
//! tree uses, so they stay in one environment.

#![allow(dead_code)]

use crate::storage::Storage;
use heed::Database;
use heed::types::Bytes;

pub type Hash = [u8; 32];

#[derive(Debug)]
pub enum Error {
    Storage(crate::storage::Error),
    Heed(heed::Error),
    /// The on-disk entry wasn't a validly encoded position -- e.g. opening
    /// a directory that isn't actually a UTXO index this code created.
    Corrupt(&'static str),
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

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Storage(e) => write!(f, "storage error: {e}"),
            Error::Heed(e) => write!(f, "LMDB error: {e}"),
            Error::Corrupt(msg) => write!(f, "corrupt UTXO index entry: {msg}"),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

/// The database: one record per output the active chain created (see
/// `chain`'s output index, which reads the same records): its block's
/// height (u64 BE) ‖ recovery nonce ‖ position (u64 BE) ‖ unspent (0/1).
pub const OUTPUTS_DB: &str = "outputs";
const POSITION: std::ops::Range<usize> = 24..32;
const UNSPENT: usize = 32;
pub const RECORD_LEN: usize = 33;

pub struct UtxoIndex {
    storage: Storage,
    entries: Database<Bytes, Bytes>,
}

impl UtxoIndex {
    pub fn open(storage: &Storage) -> Result<Self> {
        let entries = storage.database(OUTPUTS_DB)?;
        Ok(UtxoIndex {
            storage: storage.clone(),
            entries,
        })
    }

    fn record(&self, txn: &heed::RoTxn, commitment: &Hash) -> Result<Option<[u8; RECORD_LEN]>> {
        match self.entries.get(txn, commitment)? {
            Some(bytes) => Ok(Some(bytes.try_into().map_err(|_| Error::Corrupt("output record was the wrong size"))?)),
            None => Ok(None),
        }
    }

    /// `commitment` is unspent, at `position` (its record's height and
    /// nonce are kept, or zero until `set_origin`). Nothing is committed
    /// here -- that's the caller's transaction.
    pub fn insert(&mut self, wtxn: &mut heed::RwTxn, commitment: Hash, position: u64) -> Result<()> {
        let mut record = self.record(wtxn, &commitment)?.unwrap_or([0; RECORD_LEN]);
        record[POSITION].copy_from_slice(&position.to_be_bytes());
        record[UNSPENT] = 1;
        self.entries.put(wtxn, &commitment, &record)?;
        Ok(())
    }

    /// A new unspent output's whole record at once (a snapshot import).
    pub fn create(&mut self, wtxn: &mut heed::RwTxn, commitment: Hash, position: u64, height: u64, nonce: &[u8; 16]) -> Result<()> {
        let mut record = [0; RECORD_LEN];
        record[..8].copy_from_slice(&height.to_be_bytes());
        record[8..24].copy_from_slice(nonce);
        record[POSITION].copy_from_slice(&position.to_be_bytes());
        record[UNSPENT] = 1;
        self.entries.put(wtxn, &commitment, &record)?;
        Ok(())
    }

    /// Record the block height and recovery nonce `commitment` was created
    /// with.
    pub fn set_origin(&mut self, wtxn: &mut heed::RwTxn, commitment: Hash, height: u64, nonce: &[u8; 16]) -> Result<()> {
        let mut record = self.record(wtxn, &commitment)?.unwrap_or([0; RECORD_LEN]);
        record[..8].copy_from_slice(&height.to_be_bytes());
        record[8..24].copy_from_slice(nonce);
        self.entries.put(wtxn, &commitment, &record)?;
        Ok(())
    }

    /// The position of `commitment` if it's an unspent output. Reads
    /// through `txn` -- a plain `RoTxn`, or the same `RwTxn` an in-progress
    /// `insert`/`remove` is using.
    pub fn get(&self, txn: &heed::RoTxn, commitment: Hash) -> Result<Option<u64>> {
        Ok(self
            .record(txn, &commitment)?
            .filter(|r| r[UNSPENT] == 1)
            .map(|r| u64::from_be_bytes(r[POSITION].try_into().unwrap())))
    }

    /// `commitment` is spent: no longer found by `get` (its record stays,
    /// for recovery, until `forget`). Harmless if it isn't there.
    pub fn remove(&mut self, wtxn: &mut heed::RwTxn, commitment: Hash) -> Result<()> {
        if let Some(mut record) = self.record(wtxn, &commitment)? {
            record[UNSPENT] = 0;
            self.entries.put(wtxn, &commitment, &record)?;
        }
        Ok(())
    }

    /// Drop `commitment`'s record entirely (its creating block unwound).
    pub fn forget(&mut self, wtxn: &mut heed::RwTxn, commitment: Hash) -> Result<()> {
        self.entries.delete(wtxn, &commitment)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poseidon2::hash_bytes_32;
    use std::sync::atomic::{AtomicU64, Ordering};

    struct TempDir(std::path::PathBuf);

    impl TempDir {
        fn new() -> Self {
            static COUNTER: AtomicU64 = AtomicU64::new(0);
            let n = COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!("utxo-test-{}-{n}", std::process::id()));
            std::fs::create_dir_all(&path).unwrap();
            TempDir(path)
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn temp_storage() -> (Storage, TempDir) {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        (storage, dir)
    }

    fn hash_of(byte: u8) -> Hash {
        hash_bytes_32(&[byte; 32])
    }

    fn insert_committed(storage: &Storage, index: &mut UtxoIndex, commitment: Hash, position: u64) {
        let mut wtxn = storage.write_txn().unwrap();
        index.insert(&mut wtxn, commitment, position).unwrap();
        wtxn.commit().unwrap();
    }

    fn remove_committed(storage: &Storage, index: &mut UtxoIndex, commitment: Hash) {
        let mut wtxn = storage.write_txn().unwrap();
        index.remove(&mut wtxn, commitment).unwrap();
        wtxn.commit().unwrap();
    }

    fn get(storage: &Storage, index: &UtxoIndex, commitment: Hash) -> Option<u64> {
        let rtxn = storage.read_txn().unwrap();
        index.get(&rtxn, commitment).unwrap()
    }

    #[test]
    fn unknown_hash_returns_none() {
        let (storage, _dir) = temp_storage();
        let index = UtxoIndex::open(&storage).unwrap();
        assert_eq!(get(&storage, &index, hash_of(1)), None);
    }

    #[test]
    fn inserted_entry_is_found() {
        let (storage, _dir) = temp_storage();
        let mut index = UtxoIndex::open(&storage).unwrap();
        insert_committed(&storage, &mut index, hash_of(1), 42);
        assert_eq!(get(&storage, &index, hash_of(1)), Some(42));
    }

    #[test]
    fn removed_entry_is_no_longer_found() {
        let (storage, _dir) = temp_storage();
        let mut index = UtxoIndex::open(&storage).unwrap();
        insert_committed(&storage, &mut index, hash_of(1), 42);
        remove_committed(&storage, &mut index, hash_of(1));
        assert_eq!(get(&storage, &index, hash_of(1)), None);
    }

    #[test]
    fn removing_an_absent_entry_is_a_harmless_no_op() {
        let (storage, _dir) = temp_storage();
        let mut index = UtxoIndex::open(&storage).unwrap();
        remove_committed(&storage, &mut index, hash_of(1));
        assert_eq!(get(&storage, &index, hash_of(1)), None);
    }

    #[test]
    fn distinct_hashes_are_tracked_independently() {
        let (storage, _dir) = temp_storage();
        let mut index = UtxoIndex::open(&storage).unwrap();
        insert_committed(&storage, &mut index, hash_of(1), 10);
        insert_committed(&storage, &mut index, hash_of(2), 20);

        remove_committed(&storage, &mut index, hash_of(1));

        assert_eq!(get(&storage, &index, hash_of(1)), None);
        assert_eq!(get(&storage, &index, hash_of(2)), Some(20));
    }

    #[test]
    fn inserting_again_overwrites_the_position() {
        let (storage, _dir) = temp_storage();
        let mut index = UtxoIndex::open(&storage).unwrap();
        insert_committed(&storage, &mut index, hash_of(1), 10);
        insert_committed(&storage, &mut index, hash_of(1), 20);
        assert_eq!(get(&storage, &index, hash_of(1)), Some(20));
    }

    #[test]
    fn reopening_the_same_storage_sees_prior_entries() {
        let (storage, _dir) = temp_storage();
        {
            let mut index = UtxoIndex::open(&storage).unwrap();
            insert_committed(&storage, &mut index, hash_of(1), 42);
        }
        let index = UtxoIndex::open(&storage).unwrap();
        assert_eq!(get(&storage, &index, hash_of(1)), Some(42));
    }

    #[test]
    fn insert_and_remove_compose_within_one_shared_transaction() {
        let (storage, _dir) = temp_storage();
        let mut index = UtxoIndex::open(&storage).unwrap();
        let mut wtxn = storage.write_txn().unwrap();
        index.insert(&mut wtxn, hash_of(1), 10).unwrap();
        index.insert(&mut wtxn, hash_of(2), 20).unwrap();
        index.remove(&mut wtxn, hash_of(1)).unwrap();
        assert_eq!(index.get(&wtxn, hash_of(1)).unwrap(), None);
        assert_eq!(index.get(&wtxn, hash_of(2)).unwrap(), Some(20));
        wtxn.commit().unwrap();

        assert_eq!(get(&storage, &index, hash_of(1)), None);
        assert_eq!(get(&storage, &index, hash_of(2)), Some(20));
    }

    /// The property reorg undo relies on for reversing a *spend*:
    /// removing an entry and then re-inserting the exact same
    /// `(commitment, position)` pair must match a store that never
    /// removed it at all -- with an unrelated entry left alone the
    /// whole time, to confirm the undo doesn't disturb anything else.
    #[test]
    fn removing_then_reinserting_matches_never_having_removed_it() {
        let (storage_a, _dir_a) = temp_storage();
        let mut a = UtxoIndex::open(&storage_a).unwrap();
        insert_committed(&storage_a, &mut a, hash_of(1), 10);
        insert_committed(&storage_a, &mut a, hash_of(2), 20);
        remove_committed(&storage_a, &mut a, hash_of(1)); // simulate a spend
        insert_committed(&storage_a, &mut a, hash_of(1), 10); // undo it

        let (storage_b, _dir_b) = temp_storage();
        let mut b = UtxoIndex::open(&storage_b).unwrap();
        insert_committed(&storage_b, &mut b, hash_of(1), 10);
        insert_committed(&storage_b, &mut b, hash_of(2), 20);
        // hash_of(1) is never removed at all in `b`.

        assert_eq!(get(&storage_a, &a, hash_of(1)), get(&storage_b, &b, hash_of(1)));
        assert_eq!(get(&storage_a, &a, hash_of(2)), get(&storage_b, &b, hash_of(2)));
    }

    /// The other direction: reversing an output's *creation*. Inserting
    /// then removing the same entry must match a store that never
    /// inserted it at all.
    #[test]
    fn inserting_then_removing_matches_never_having_inserted_it() {
        let (storage_a, _dir_a) = temp_storage();
        let mut a = UtxoIndex::open(&storage_a).unwrap();
        insert_committed(&storage_a, &mut a, hash_of(2), 20);
        insert_committed(&storage_a, &mut a, hash_of(1), 10); // simulate a new output
        remove_committed(&storage_a, &mut a, hash_of(1)); // undo its creation

        let (storage_b, _dir_b) = temp_storage();
        let mut b = UtxoIndex::open(&storage_b).unwrap();
        insert_committed(&storage_b, &mut b, hash_of(2), 20);
        // hash_of(1) is never inserted at all in `b`.

        assert_eq!(get(&storage_a, &a, hash_of(1)), get(&storage_b, &b, hash_of(1)));
        assert_eq!(get(&storage_a, &a, hash_of(2)), get(&storage_b, &b, hash_of(2)));
    }
}
