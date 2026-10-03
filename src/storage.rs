//! A shared LMDB storage context: one `heed::Env`, opened once, that every
//! on-disk component in this crate gets its own named database from.
//!
//! Before this module existed, `Pmmr::open` opened its own LMDB environment
//! directly -- fine when it was the only thing persisted, but the planned
//! spent-output bitmap (for pruning) needs to live in the *same*
//! environment as the PMMR's tables, not a second one, so a separate tool
//! (or the node itself) only ever has one thing to open. This module is
//! that shared handle; `Pmmr` (and later the bitmap) take one by reference
//! rather than managing their own.

// `main.rs` doesn't call into this module directly yet (it just prints
// "Hello world!"), so allow dead code here rather than suppressing warnings
// piecemeal -- this module exists to be exercised by its own tests and by
// `pmmr.rs` for now.
#![allow(dead_code)]

use heed::types::Bytes;
use heed::{Database, Env, EnvOpenOptions};
use std::path::Path;

/// Default LMDB map size: 1 GiB of reserved address space (not disk usage --
/// LMDB only consumes what's actually written). Plenty for development;
/// bump this (or reopen with a larger value) before storing more than that.
pub const DEFAULT_MAP_SIZE: usize = 1 << 30;

/// Upper bound on how many named databases this environment can ever hold;
/// LMDB requires declaring this upfront. Currently used: `nodes` and `meta`
/// (by `Pmmr`), `bitmap_pages` and `bitmap_nodes` (by `Bitmap`),
/// `utxo_index` (by `UtxoIndex`), and `chain_meta` (by `Chain`) -- 6 of 8,
/// leaving some headroom before this needs revisiting.
const MAX_DBS: u32 = 8;

#[derive(Debug)]
pub enum Error {
    Io(std::io::Error),
    Heed(heed::Error),
}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Error::Io(e)
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
            Error::Io(e) => write!(f, "I/O error: {e}"),
            Error::Heed(e) => write!(f, "LMDB error: {e}"),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

/// A handle to one LMDB environment, shared by every component that
/// persists data. Cheap to clone -- `heed::Env` is itself an `Arc` under the
/// hood, so cloning a `Storage` just bumps a reference count, not opening a
/// second environment.
#[derive(Clone)]
pub struct Storage {
    env: Env,
}

impl Storage {
    /// Open (creating if absent) a storage context at `path`, with the
    /// default 1 GiB LMDB map size.
    pub fn open(path: &Path) -> Result<Self> {
        Self::open_with_map_size(path, DEFAULT_MAP_SIZE)
    }

    pub fn open_with_map_size(path: &Path, map_size: usize) -> Result<Self> {
        std::fs::create_dir_all(path)?;
        let env = unsafe {
            EnvOpenOptions::new()
                .map_size(map_size)
                .max_dbs(MAX_DBS)
                .open(path)?
        };
        Ok(Storage { env })
    }

    /// Open (creating if absent) a named database of raw bytes within this
    /// environment. Safe to call repeatedly with the same name -- later
    /// calls just reopen the same database.
    pub fn database(&self, name: &str) -> Result<Database<Bytes, Bytes>> {
        let mut wtxn = self.env.write_txn()?;
        let db = self.env.create_database(&mut wtxn, Some(name))?;
        wtxn.commit()?;
        Ok(db)
    }

    pub fn read_txn(&self) -> Result<heed::RoTxn<'_>> {
        Ok(self.env.read_txn()?)
    }

    pub fn write_txn(&self) -> Result<heed::RwTxn<'_>> {
        Ok(self.env.write_txn()?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    fn temp_dir() -> std::path::PathBuf {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        std::env::temp_dir().join(format!("storage-test-{}-{n}", std::process::id()))
    }

    #[test]
    fn database_reopen_returns_same_data() {
        let dir = temp_dir();
        let storage = Storage::open(&dir).unwrap();
        let db = storage.database("example").unwrap();

        let mut wtxn = storage.write_txn().unwrap();
        db.put(&mut wtxn, b"key".as_slice(), b"value".as_slice())
            .unwrap();
        wtxn.commit().unwrap();

        // Reopening the same named database (a fresh handle, same
        // environment) must see the same data.
        let db_again = storage.database("example").unwrap();
        let rtxn = storage.read_txn().unwrap();
        assert_eq!(
            db_again.get(&rtxn, b"key".as_slice()).unwrap(),
            Some(b"value".as_slice())
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn clone_shares_the_same_environment() {
        let dir = temp_dir();
        let storage = Storage::open(&dir).unwrap();
        let cloned = storage.clone();
        let db = storage.database("shared").unwrap();

        let mut wtxn = cloned.write_txn().unwrap();
        db.put(&mut wtxn, b"k".as_slice(), b"v".as_slice()).unwrap();
        wtxn.commit().unwrap();

        let rtxn = storage.read_txn().unwrap();
        assert_eq!(
            db.get(&rtxn, b"k".as_slice()).unwrap(),
            Some(b"v".as_slice())
        );

        let _ = std::fs::remove_dir_all(&dir);
    }
}
