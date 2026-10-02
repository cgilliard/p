//! A UTXO index: a reverse lookup from an output's hash to its position
//! in the `pmmr`. This is the piece `block` validation needs to turn a
//! spent input's claimed (pubkey, amount) into "where in the PMMR is the
//! real output it's spending" -- without it, there's no way to check an
//! input against the actual committed leaf, or to know which bit to flip
//! in the `bitmap`.
//!
//! Keyed by the *output's own hash* -- the same `Poseidon2(output.to_bytes())`
//! hash `pmmr` already uses as a leaf hash -- rather than by a pubkey hash
//! specifically. An `Output` today is just (pubkey hash, amount), but
//! that's expected to grow (scripts, HTLCs, ...), and this index should
//! keep working unchanged no matter what ends up inside an `Output`: its
//! only job is "given this output's hash, what position is it at."
//!
//! This is a genuine *unspent* output set, not just a static reverse
//! index: an entry is inserted when an output is created and removed the
//! moment it's spent (`remove`), so a lookup naturally returns `None` for
//! anything already spent or never created -- the same shape as a real
//! UTXO set, and a second line of defense against double-spending a
//! position within a block, on top of whatever the `bitmap` catches.
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
    /// The on-disk entry wasn't a valid encoded position -- e.g. opening a
    /// directory that isn't actually a UTXO index this code created.
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

    /// Record that the output hashing to `output_hash` lives at `position`.
    /// Called when a new output is appended to the `pmmr`. Overwrites
    /// whatever was there before for that hash -- a collision between two
    /// genuinely different outputs is astronomically unlikely, and
    /// re-inserting the same (hash, position) pair is harmless.
    pub fn insert(&mut self, output_hash: Hash, position: u64) -> Result<()> {
        let mut wtxn = self.storage.write_txn()?;
        self.entries
            .put(&mut wtxn, &output_hash, &encode_pos(position))?;
        wtxn.commit()?;
        Ok(())
    }

    /// The position of the unspent output hashing to `output_hash`, or
    /// `None` if there's no such entry -- either it never existed, or it
    /// was already spent (see `remove`).
    pub fn get(&self, output_hash: Hash) -> Result<Option<u64>> {
        let rtxn = self.storage.read_txn()?;
        match self.entries.get(&rtxn, &output_hash)? {
            Some(bytes) => Ok(Some(decode_pos(bytes)?)),
            None => Ok(None),
        }
    }

    /// Remove the entry for `output_hash`, e.g. once it's been spent.
    /// Harmless no-op if there wasn't one.
    pub fn remove(&mut self, output_hash: Hash) -> Result<()> {
        let mut wtxn = self.storage.write_txn()?;
        self.entries.delete(&mut wtxn, &output_hash)?;
        wtxn.commit()?;
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
        hash_bytes_32(&[byte; 40])
    }

    #[test]
    fn unknown_hash_returns_none() {
        let (storage, _dir) = temp_storage();
        let index = UtxoIndex::open(&storage).unwrap();
        assert_eq!(index.get(hash_of(1)).unwrap(), None);
    }

    #[test]
    fn inserted_entry_is_found() {
        let (storage, _dir) = temp_storage();
        let mut index = UtxoIndex::open(&storage).unwrap();
        index.insert(hash_of(1), 42).unwrap();
        assert_eq!(index.get(hash_of(1)).unwrap(), Some(42));
    }

    #[test]
    fn removed_entry_is_no_longer_found() {
        let (storage, _dir) = temp_storage();
        let mut index = UtxoIndex::open(&storage).unwrap();
        index.insert(hash_of(1), 42).unwrap();
        index.remove(hash_of(1)).unwrap();
        assert_eq!(index.get(hash_of(1)).unwrap(), None);
    }

    #[test]
    fn removing_an_absent_entry_is_a_harmless_no_op() {
        let (storage, _dir) = temp_storage();
        let mut index = UtxoIndex::open(&storage).unwrap();
        index.remove(hash_of(1)).unwrap();
        assert_eq!(index.get(hash_of(1)).unwrap(), None);
    }

    #[test]
    fn distinct_hashes_are_tracked_independently() {
        let (storage, _dir) = temp_storage();
        let mut index = UtxoIndex::open(&storage).unwrap();
        index.insert(hash_of(1), 10).unwrap();
        index.insert(hash_of(2), 20).unwrap();

        index.remove(hash_of(1)).unwrap();

        assert_eq!(index.get(hash_of(1)).unwrap(), None);
        assert_eq!(index.get(hash_of(2)).unwrap(), Some(20));
    }

    #[test]
    fn inserting_again_overwrites_the_position() {
        let (storage, _dir) = temp_storage();
        let mut index = UtxoIndex::open(&storage).unwrap();
        index.insert(hash_of(1), 10).unwrap();
        index.insert(hash_of(1), 20).unwrap();
        assert_eq!(index.get(hash_of(1)).unwrap(), Some(20));
    }

    #[test]
    fn reopening_the_same_storage_sees_prior_entries() {
        let (storage, _dir) = temp_storage();
        {
            let mut index = UtxoIndex::open(&storage).unwrap();
            index.insert(hash_of(1), 42).unwrap();
        }
        let index = UtxoIndex::open(&storage).unwrap();
        assert_eq!(index.get(hash_of(1)).unwrap(), Some(42));
    }
}
