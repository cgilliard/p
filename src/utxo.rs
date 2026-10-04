//! A UTXO index: a reverse lookup from an output's commitment hash to its
//! position in the `pmmr`. This is the piece `chain` validation needs to
//! turn a spend into "where in the `pmmr` is the real output it's
//! spending" -- without it, there's no way to check a spend against real
//! chain state at all.
//!
//! Keyed by the *full commitment* `H(H(pubkey) || amount)` -- the same
//! hash `pmmr` stores as the leaf, and the same hash both a spend
//! (`block::BlockBody.inputs`) and the output that created it
//! (`block::BlockBody.outputs`) publish. Deliberately **not** keyed by
//! `pubkey_hash` alone: this index, like `pmmr` and the published block
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
//! position within a block, on top of whatever the `bitmap` catches.
//!
//! Because the key folds in `amount`, two outputs that happen to share a
//! public key no longer collide the way they would under a
//! `pubkey_hash`-only key, *unless* they also share the exact same
//! amount (in which case they're indistinguishable anyway). `insert` is
//! still a plain, unconditional write with no safety check of its own --
//! that judgment call (is a new output allowed to reuse a key that's
//! still live) belongs to `chain` validation, which can call `get` first.
//!
//! Backed by LMDB via the same shared `storage::Storage` context `pmmr`
//! and `bitmap` already use, so all three stay in one environment.

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

fn encode_pos(pos: u64) -> [u8; 8] {
    pos.to_be_bytes()
}

fn decode_pos(bytes: &[u8]) -> Result<u64> {
    bytes
        .try_into()
        .map(u64::from_be_bytes)
        .map_err(|_| Error::Corrupt("position value was not 8 bytes"))
}

pub struct UtxoIndex {
    storage: Storage,
    entries: Database<Bytes, Bytes>,
}

impl UtxoIndex {
    /// Open this index's table within the given storage context, creating
    /// it if it doesn't already exist.
    pub fn open(storage: &Storage) -> Result<Self> {
        let entries = storage.database("utxo_index")?;
        Ok(UtxoIndex {
            storage: storage.clone(),
            entries,
        })
    }

    /// Record that the output hashing to `commitment` lives at `position`,
    /// through `wtxn`. A plain, unconditional write -- overwrites whatever
    /// was there before for that key, with no check of whether that's
    /// safe. See the module docs: that check belongs to the caller.
    /// Nothing is committed here -- that's the caller's job, once every
    /// other store it's updating in the same transaction has also
    /// succeeded.
    pub fn insert(&mut self, wtxn: &mut heed::RwTxn, commitment: Hash, position: u64) -> Result<()> {
        self.entries
            .put(wtxn, &commitment, &encode_pos(position))?;
        Ok(())
    }

    /// The position of the unspent output hashing to `commitment`, or
    /// `None` if there's no such entry -- either it never existed, or it
    /// was already spent (see `remove`). Reads through `txn` -- a plain
    /// `RoTxn`, or the same `RwTxn` an in-progress `insert`/`remove` is
    /// using.
    pub fn get(&self, txn: &heed::RoTxn, commitment: Hash) -> Result<Option<u64>> {
        match self.entries.get(txn, &commitment)? {
            Some(bytes) => Ok(Some(decode_pos(bytes)?)),
            None => Ok(None),
        }
    }

    /// Remove the entry for `commitment`, e.g. once it's been spent.
    /// Harmless no-op if there wasn't one. Nothing is committed here --
    /// see `insert`.
    pub fn remove(&mut self, wtxn: &mut heed::RwTxn, commitment: Hash) -> Result<()> {
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
