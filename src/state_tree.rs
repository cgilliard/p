//! The chain's state: one fixed-depth binary Merkle tree over output
//! positions (`docs/CHAIN_RECURSION.md`), replacing the PMMR (which
//! outputs exist) and the bitmap (which are spent).
//!
//! Every output ever created has a position -- `0, 1, 2, ...` in the
//! order blocks create them -- and a leaf there:
//!
//! - `EMPTY` before anything is appended at it,
//! - `leaf(commitment, nonce)` while it's unspent -- the output's
//!   commitment and its recovery nonce, so the root authenticates both
//!   (a fast-synced node's snapshot nonces can be checked, like its
//!   commitments),
//! - `SPENT` once it's spent.
//!
//! The chain commits to `(root, count)`: the root of the `DEPTH`-level
//! tree, and how many outputs it holds (`BlockHeader::state_root`,
//! `output_count`). A spend proves the output's leaf is at its position
//! (its path recomputes the root) and sets it to `SPENT`; an append proves
//! position `count` is `EMPTY` and sets it.
//!
//! **The whole tree follows from `count` and the unspent outputs**: every
//! position below `count` not holding one is `SPENT`, every one above is
//! `EMPTY`, and an all-`SPENT` (or all-`EMPTY`) subtree has a fixed hash
//! per height. So a state snapshot is just the unspent outputs with their
//! positions, splittable into subtrees each checkable on its own against
//! an authenticated subtree root (`docs/CHAIN_RECURSION.md`, fast sync).
//!
//! Built for proving: a node is **one Poseidon2 permutation** of
//! `left ‖ right` with the level in the capacity (`node`) -- field
//! elements throughout, no byte packing -- and every operation has the
//! same shape (a full-depth path) whatever the data, which is what a
//! circuit needs. Measured in `state_circuit`: ~2,100 circuit rows per
//! spend or append, against ~179,000 per spend for the PMMR + bitmap
//! this replaces.
//!
//! # Storage
//!
//! Sparse, in LMDB: a node is stored only if it differs from the hash of
//! an all-`EMPTY` subtree of its height (`empty`), so storage grows with
//! the outputs actually created (about two nodes per leaf), not with the
//! 2^32 positions. Like the other stores, every method works through the
//! caller's transaction and keeps no state of its own.

#![allow(dead_code)]

use heed::Database;
use heed::types::Bytes;

use crate::circuit::Octet;
use crate::poseidon2::{BabyBear, digest_from_bytes, digest_to_bytes, perm24};
use crate::storage::Storage;

/// Levels: room for 2^32 outputs.
pub const DEPTH: usize = 32;
/// Node hashes' domains: `DOMAIN_STATE_NODE + level`. (0x300: the
/// second layout, leaves committing to nonces -- distinct from the first,
/// so a chain stored under it has a different genesis and won't open.)
const DOMAIN_STATE_NODE: u32 = 0x300;
/// An unspent output's leaf hash.
const DOMAIN_STATE_LEAF: u32 = 0x2ff;
pub const EMPTY: Octet = [BabyBear::ZERO; 8];
/// A spent output's leaf. A commitment is a hash output, so it's never
/// this (or `EMPTY`) except with negligible probability.
pub const SPENT: Octet = {
    let mut o = [BabyBear::ZERO; 8];
    o[0] = BabyBear::ONE;
    o
};

const NODES_DB: &str = "state_tree";
const META_DB: &str = "state_meta";
const COUNT_KEY: &[u8] = b"count";

/// A node's capacity octet: its domain and the rate length.
pub fn capacity(level: usize) -> Octet {
    let mut c = [BabyBear::ZERO; 8];
    c[0] = BabyBear::new(DOMAIN_STATE_NODE + level as u32);
    c[1] = BabyBear::new(16);
    c
}

fn compress(domain: u32, left: &Octet, right: &Octet) -> Octet {
    let mut state = [BabyBear::ZERO; 24];
    state[..8].copy_from_slice(left);
    state[8..16].copy_from_slice(right);
    state[16] = BabyBear::new(domain);
    state[17] = BabyBear::new(16);
    perm24().permute(state)[..8].try_into().unwrap()
}

/// The node above `left` and `right` at `level` (0: just above leaves).
pub fn node(level: usize, left: &Octet, right: &Octet) -> Octet {
    compress(DOMAIN_STATE_NODE + level as u32, left, right)
}

/// The capacity octet of an unspent output's leaf hash.
pub fn leaf_capacity() -> Octet {
    let mut c = [BabyBear::ZERO; 8];
    c[0] = BabyBear::new(DOMAIN_STATE_LEAF);
    c[1] = BabyBear::new(16);
    c
}

/// An unspent output's leaf: its commitment and recovery nonce (as
/// `output::nonce_limbs`), one permutation.
pub fn leaf(commitment: &[u8; 32], nonce: &[u8; crate::recovery::NONCE_LEN]) -> Octet {
    compress_leaf(&digest_from_bytes(commitment), &crate::output::nonce_limbs(nonce))
}

/// `leaf`, from the commitment's and nonce's field elements.
pub fn compress_leaf(commitment: &Octet, nonce_limbs: &Octet) -> Octet {
    compress(DOMAIN_STATE_LEAF, commitment, nonce_limbs)
}

/// The hash of an all-`EMPTY` subtree of each height `0..=DEPTH`.
pub fn empty_hashes() -> Vec<Octet> {
    let mut empty = vec![EMPTY];
    for level in 0..DEPTH {
        let e = empty[level];
        empty.push(node(level, &e, &e));
    }
    empty
}

/// The root of an empty tree.
pub fn empty_root() -> [u8; 32] {
    digest_to_bytes(empty_hashes()[DEPTH])
}

#[derive(Debug)]
pub enum Error {
    Storage(crate::storage::Error),
    Heed(heed::Error),
    Corrupt(&'static str),
    /// More outputs than the tree has room for.
    Full,
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
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::Storage(e) => write!(f, "{e}"),
            Error::Heed(e) => write!(f, "{e}"),
            Error::Corrupt(what) => write!(f, "corrupt state tree: {what}"),
            Error::Full => write!(f, "the state tree is full"),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

fn key(height: usize, index: u64) -> [u8; 9] {
    let mut k = [0u8; 9];
    k[0] = height as u8;
    k[1..].copy_from_slice(&index.to_be_bytes());
    k
}

pub struct StateTree {
    nodes: Database<Bytes, Bytes>,
    meta: Database<Bytes, Bytes>,
    empty: Vec<Octet>,
}

impl StateTree {
    pub fn open(storage: &Storage) -> Result<Self> {
        Ok(StateTree {
            nodes: storage.database(NODES_DB)?,
            meta: storage.database(META_DB)?,
            empty: empty_hashes(),
        })
    }

    /// How many outputs the tree holds (the next position).
    pub fn count(&self, txn: &heed::RoTxn) -> Result<u64> {
        match self.meta.get(txn, COUNT_KEY)? {
            Some(b) => Ok(u64::from_be_bytes(b.try_into().map_err(|_| Error::Corrupt("count"))?)),
            None => Ok(0),
        }
    }

    fn get(&self, txn: &heed::RoTxn, height: usize, index: u64) -> Result<Octet> {
        match self.nodes.get(txn, &key(height, index))? {
            Some(b) => Ok(digest_from_bytes(b.try_into().map_err(|_| Error::Corrupt("node"))?)),
            None => Ok(self.empty[height]),
        }
    }

    pub fn root(&self, txn: &heed::RoTxn) -> Result<[u8; 32]> {
        Ok(digest_to_bytes(self.get(txn, DEPTH, 0)?))
    }

    pub fn leaf_at(&self, txn: &heed::RoTxn, position: u64) -> Result<Octet> {
        self.get(txn, 0, position)
    }

    /// The siblings on the path from leaf `position` up, bottom first --
    /// what a proof of a spend or an append at `position` needs.
    pub fn path(&self, txn: &heed::RoTxn, position: u64) -> Result<Vec<Octet>> {
        (0..DEPTH).map(|h| self.get(txn, h, (position >> h) ^ 1)).collect()
    }

    /// Set leaf `position`, updating its path to the root.
    fn set(&self, wtxn: &mut heed::RwTxn, position: u64, leaf: Octet) -> Result<()> {
        let mut hash = leaf;
        for h in 0..=DEPTH {
            let index = position >> h;
            if hash == self.empty[h] {
                self.nodes.delete(wtxn, &key(h, index))?;
            } else {
                self.nodes.put(wtxn, &key(h, index), &digest_to_bytes(hash))?;
            }
            if h == DEPTH {
                break;
            }
            let sibling = self.get(wtxn, h, index ^ 1)?;
            hash = if index & 1 == 0 { node(h, &hash, &sibling) } else { node(h, &sibling, &hash) };
        }
        Ok(())
    }

    fn set_count(&self, wtxn: &mut heed::RwTxn, count: u64) -> Result<()> {
        self.meta.put(wtxn, COUNT_KEY, &count.to_be_bytes())?;
        Ok(())
    }

    /// Append an output; its position.
    pub fn push(&self, wtxn: &mut heed::RwTxn, commitment: &[u8; 32], nonce: &[u8; crate::recovery::NONCE_LEN]) -> Result<u64> {
        let position = self.count(wtxn)?;
        if position >= 1 << DEPTH {
            return Err(Error::Full);
        }
        self.set(wtxn, position, leaf(commitment, nonce))?;
        self.set_count(wtxn, position + 1)?;
        Ok(position)
    }

    /// Mark the output at `position` spent.
    pub fn spend(&self, wtxn: &mut heed::RwTxn, position: u64) -> Result<()> {
        self.set(wtxn, position, SPENT)
    }

    /// Undo `spend`: the output at `position` is unspent again.
    pub fn unspend(&self, wtxn: &mut heed::RwTxn, position: u64, commitment: &[u8; 32], nonce: &[u8; crate::recovery::NONCE_LEN]) -> Result<()> {
        self.set(wtxn, position, leaf(commitment, nonce))
    }

    /// Undo the last `n` appends.
    pub fn truncate(&self, wtxn: &mut heed::RwTxn, n: u64) -> Result<()> {
        let count = self.count(wtxn)?;
        let keep = count.checked_sub(n).ok_or(Error::Corrupt("truncating below zero"))?;
        for position in keep..count {
            self.set(wtxn, position, EMPTY)?;
        }
        self.set_count(wtxn, keep)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poseidon2::hash_bytes_32;

    struct TempDir(std::path::PathBuf);

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn open(name: &str) -> (TempDir, Storage, StateTree) {
        let dir = std::env::temp_dir().join(format!("state-tree-{}-{name}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let storage = Storage::open(&dir).unwrap();
        let tree = StateTree::open(&storage).unwrap();
        (TempDir(dir), storage, tree)
    }

    fn commitment(k: u64) -> [u8; 32] {
        hash_bytes_32(&k.to_le_bytes())
    }

    fn nonce(k: u64) -> [u8; 16] {
        hash_bytes_32(&(k + 1_000_000).to_le_bytes())[..16].try_into().unwrap()
    }

    /// The stored tree agrees with the in-memory reference
    /// (`state_circuit::MemTree`), operation by operation.
    #[test]
    fn the_stored_tree_matches_the_reference() {
        let (_d, storage, tree) = open("reference");
        let mut reference = crate::state_circuit::MemTree::default();
        let mut wtxn = storage.write_txn().unwrap();
        assert_eq!(tree.root(&wtxn).unwrap(), empty_root());
        assert_eq!(tree.root(&wtxn).unwrap(), digest_to_bytes(reference.root()));
        for k in 0..40 {
            assert_eq!(tree.push(&mut wtxn, &commitment(k), &nonce(k)).unwrap(), k);
            reference.append(leaf(&commitment(k), &nonce(k)));
        }
        for k in [3, 17, 39, 0] {
            tree.spend(&mut wtxn, k).unwrap();
            reference.spend(&leaf(&commitment(k), &nonce(k)));
        }
        assert_eq!(tree.root(&wtxn).unwrap(), digest_to_bytes(reference.root()));
        assert_eq!(tree.count(&wtxn).unwrap(), 40);
        for p in [0, 5, 39, 40] {
            assert_eq!(tree.path(&wtxn, p).unwrap(), reference.path(p));
        }
        assert_eq!(tree.leaf_at(&wtxn, 3).unwrap(), SPENT);
        assert_eq!(tree.leaf_at(&wtxn, 4).unwrap(), leaf(&commitment(4), &nonce(4)));
        assert_eq!(tree.leaf_at(&wtxn, 40).unwrap(), EMPTY);
        // The leaf commits to the nonce as well as the commitment.
        assert_ne!(leaf(&commitment(4), &nonce(4)), leaf(&commitment(4), &nonce(5)));
    }

    /// Undoing appends and spends restores the exact previous state --
    /// root, count, and storage (no leftover nodes).
    #[test]
    fn undo_restores_the_exact_previous_state() {
        let (_d, storage, tree) = open("undo");
        let mut wtxn = storage.write_txn().unwrap();
        for k in 0..10 {
            tree.push(&mut wtxn, &commitment(k), &nonce(k)).unwrap();
        }
        let (root, stored) = (tree.root(&wtxn).unwrap(), tree.nodes.len(&wtxn).unwrap());
        tree.spend(&mut wtxn, 2).unwrap();
        tree.spend(&mut wtxn, 7).unwrap();
        for k in 10..15 {
            tree.push(&mut wtxn, &commitment(k), &nonce(k)).unwrap();
        }
        tree.truncate(&mut wtxn, 5).unwrap();
        tree.unspend(&mut wtxn, 7, &commitment(7), &nonce(7)).unwrap();
        tree.unspend(&mut wtxn, 2, &commitment(2), &nonce(2)).unwrap();
        assert_eq!(tree.root(&wtxn).unwrap(), root);
        assert_eq!(tree.count(&wtxn).unwrap(), 10);
        assert_eq!(tree.nodes.len(&wtxn).unwrap(), stored);
        tree.truncate(&mut wtxn, 10).unwrap();
        assert_eq!(tree.root(&wtxn).unwrap(), empty_root());
        assert_eq!(tree.nodes.len(&wtxn).unwrap(), 0);
        assert!(tree.truncate(&mut wtxn, 1).is_err());
    }

    #[test]
    fn storage_grows_with_outputs_not_positions() {
        let (_d, storage, tree) = open("sparse");
        let mut wtxn = storage.write_txn().unwrap();
        for k in 0..1000 {
            tree.push(&mut wtxn, &commitment(k), &nonce(k)).unwrap();
        }
        // ~2 per leaf below the occupied subtree, plus one per level above.
        let stored = tree.nodes.len(&wtxn).unwrap();
        assert!(stored < 2 * 1000 + DEPTH as u64 + 10, "{stored} nodes");
    }
}
