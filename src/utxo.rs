//! A UTXO index: a reverse lookup from a public key's hash to the
//! position and amount of the unspent output it currently owns. This is
//! the piece `chain` validation needs to turn a spent input's bare
//! public key into "where in the `pmmr` is the real output it's
//! spending, and how much is it actually worth" -- without it, there's
//! no way to check an input against real chain state at all, since
//! `transaction::Input` no longer carries anything but the key itself.
//!
//! Keyed by `pubkey_hash` -- the same 32-byte `Poseidon2(pubkey bytes)`
//! value already stored as `Output::pubkey_hash` -- rather than by a hash
//! of the whole output (which would also fold in the amount). Using the
//! owner-identifying part alone, not anything value-specific, means this
//! index keeps working unchanged no matter what else an `Output` grows to
//! include later (scripts, HTLCs, ...): its only job is "given this
//! owner, what position do they currently own, and for how much."
//!
//! This is a genuine *unspent* output set, not just a static reverse
//! index: an entry is inserted when an output is created and removed the
//! moment it's spent (`remove`), so a lookup naturally returns `None` for
//! anything already spent or never created -- the same shape as a real
//! UTXO set, and a second line of defense against double-spending a
//! position within a block, on top of whatever the `bitmap` catches.
//!
//! Keying by owner alone means reusing the same public key for a second,
//! *different* output is dangerous: a second `insert` under a
//! still-live key would silently overwrite the first entry, orphaning
//! whatever it pointed to (the `pmmr` leaf still exists, but nothing
//! could find it again). This module doesn't prevent that itself --
//! `insert` is a plain, unconditional write, no different from any other
//! key-value store -- that check belongs to whoever decides a new output
//! is allowed to be created at all, i.e. `chain` validation, which can
//! (and does) call `get` first and refuse to proceed if an entry is
//! already live.
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
    /// The on-disk entry wasn't a validly encoded (position, amount) pair
    /// -- e.g. opening a directory that isn't actually a UTXO index this
    /// code created.
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

/// `position` (8 bytes) followed by `amount` (8 bytes), both big-endian.
fn encode_entry(position: u64, amount: u64) -> [u8; 16] {
    let mut out = [0u8; 16];
    out[..8].copy_from_slice(&position.to_be_bytes());
    out[8..].copy_from_slice(&amount.to_be_bytes());
    out
}

fn decode_entry(bytes: &[u8]) -> Result<(u64, u64)> {
    if bytes.len() != 16 {
        return Err(Error::Corrupt("entry was not 16 bytes"));
    }
    let position = u64::from_be_bytes(bytes[..8].try_into().unwrap());
    let amount = u64::from_be_bytes(bytes[8..].try_into().unwrap());
    Ok((position, amount))
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

    /// Record that the owner hashing to `pubkey_hash` currently owns an
    /// unspent output of `amount`, at `position` in the `pmmr`. A plain,
    /// unconditional write -- overwrites whatever was there before for
    /// that key, with no check of whether that's safe. See the module
    /// docs: that check (is this key already live) belongs to the caller.
    pub fn insert(&mut self, pubkey_hash: Hash, position: u64, amount: u64) -> Result<()> {
        let mut wtxn = self.storage.write_txn()?;
        self.entries
            .put(&mut wtxn, &pubkey_hash, &encode_entry(position, amount))?;
        wtxn.commit()?;
        Ok(())
    }

    /// The `(position, amount)` of the unspent output owned by
    /// `pubkey_hash`, or `None` if there's no such entry -- either this
    /// key never owned anything, or it was already spent (see `remove`).
    pub fn get(&self, pubkey_hash: Hash) -> Result<Option<(u64, u64)>> {
        let rtxn = self.storage.read_txn()?;
        match self.entries.get(&rtxn, &pubkey_hash)? {
            Some(bytes) => Ok(Some(decode_entry(bytes)?)),
            None => Ok(None),
        }
    }

    /// Remove the entry for `pubkey_hash`, e.g. once it's been spent.
    /// Harmless no-op if there wasn't one.
    pub fn remove(&mut self, pubkey_hash: Hash) -> Result<()> {
        let mut wtxn = self.storage.write_txn()?;
        self.entries.delete(&mut wtxn, &pubkey_hash)?;
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
        hash_bytes_32(&[byte; 32])
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
        index.insert(hash_of(1), 42, 100).unwrap();
        assert_eq!(index.get(hash_of(1)).unwrap(), Some((42, 100)));
    }

    #[test]
    fn removed_entry_is_no_longer_found() {
        let (storage, _dir) = temp_storage();
        let mut index = UtxoIndex::open(&storage).unwrap();
        index.insert(hash_of(1), 42, 100).unwrap();
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
        index.insert(hash_of(1), 10, 100).unwrap();
        index.insert(hash_of(2), 20, 200).unwrap();

        index.remove(hash_of(1)).unwrap();

        assert_eq!(index.get(hash_of(1)).unwrap(), None);
        assert_eq!(index.get(hash_of(2)).unwrap(), Some((20, 200)));
    }

    #[test]
    fn inserting_again_overwrites_the_entry() {
        let (storage, _dir) = temp_storage();
        let mut index = UtxoIndex::open(&storage).unwrap();
        index.insert(hash_of(1), 10, 100).unwrap();
        index.insert(hash_of(1), 20, 200).unwrap();
        assert_eq!(index.get(hash_of(1)).unwrap(), Some((20, 200)));
    }

    #[test]
    fn reopening_the_same_storage_sees_prior_entries() {
        let (storage, _dir) = temp_storage();
        {
            let mut index = UtxoIndex::open(&storage).unwrap();
            index.insert(hash_of(1), 42, 100).unwrap();
        }
        let index = UtxoIndex::open(&storage).unwrap();
        assert_eq!(index.get(hash_of(1)).unwrap(), Some((42, 100)));
    }
}
