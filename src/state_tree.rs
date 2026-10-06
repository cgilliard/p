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
/// Unspent outputs by position (u64 BE) -> commitment ‖ nonce: what a leaf
/// hashes, kept so a peer can be sent a subtree's contents (`snapshot`).
const LEAVES_DB: &str = "state_leaves";
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
/// The hash of an all-`SPENT` subtree of each height `0..=DEPTH`.
pub fn spent_hashes() -> Vec<Octet> {
    let mut hashes = vec![SPENT];
    for level in 0..DEPTH {
        let below = hashes[level];
        hashes.push(node(level, &below, &below));
    }
    hashes
}

/// An unspent output: its position, commitment and recovery nonce.
pub type Entry = (u64, [u8; 32], [u8; crate::recovery::NONCE_LEN]);

/// The hash of subtree `(level, index)` of a tree holding `count` outputs,
/// of which those in it still unspent are `unspent` (in position order, all
/// inside the subtree): every other position below `count` is `SPENT`,
/// every one from `count` on `EMPTY`.
pub fn subtree_hash(level: usize, index: u64, count: u64, unspent: &[Entry], empty: &[Octet], spent: &[Octet]) -> Octet {
    let (lo, hi) = (index << level, (index + 1) << level);
    if lo >= count {
        return empty[level];
    }
    if unspent.is_empty() && hi <= count {
        return spent[level];
    }
    if level == 0 {
        return match unspent {
            [(_, commitment, nonce)] => leaf(commitment, nonce),
            _ => SPENT,
        };
    }
    let mid = lo + (1 << (level - 1));
    let split = unspent.partition_point(|e| e.0 < mid);
    let left = subtree_hash(level - 1, 2 * index, count, &unspent[..split], empty, spent);
    let right = subtree_hash(level - 1, 2 * index + 1, count, &unspent[split..], empty, spent);
    node(level - 1, &left, &right)
}

/// The tree as it was after some earlier block: `count` outputs, and the
/// outputs unspent then but spent since (by position). Everything else
/// below `count` is as it is now.
#[derive(Clone, Debug, Default)]
pub struct AsOf {
    pub count: u64,
    pub restored: std::collections::BTreeMap<u64, ([u8; 32], [u8; crate::recovery::NONCE_LEN])>,
}

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
    leaves: Database<Bytes, Bytes>,
    empty: Vec<Octet>,
    spent: Vec<Octet>,
}

impl StateTree {
    pub fn open(storage: &Storage) -> Result<Self> {
        Ok(StateTree {
            nodes: storage.database(NODES_DB)?,
            meta: storage.database(META_DB)?,
            leaves: storage.database(LEAVES_DB)?,
            empty: empty_hashes(),
            spent: spent_hashes(),
        })
    }

    fn put_leaf(&self, wtxn: &mut heed::RwTxn, position: u64, commitment: &[u8; 32], nonce: &[u8; crate::recovery::NONCE_LEN]) -> Result<()> {
        self.leaves.put(wtxn, &position.to_be_bytes(), &[&commitment[..], &nonce[..]].concat())?;
        Ok(())
    }

    /// The unspent outputs at positions `lo..hi`, in order.
    pub fn unspent_in(&self, txn: &heed::RoTxn, lo: u64, hi: u64) -> Result<Vec<Entry>> {
        let (lo, hi) = (lo.to_be_bytes(), hi.to_be_bytes());
        let range = (std::ops::Bound::Included(&lo[..]), std::ops::Bound::Excluded(&hi[..]));
        let mut out = Vec::new();
        for item in self.leaves.range(txn, &range)? {
            let (key, value) = item?;
            let position = u64::from_be_bytes(key.try_into().map_err(|_| Error::Corrupt("leaf key"))?);
            if value.len() != 32 + crate::recovery::NONCE_LEN {
                return Err(Error::Corrupt("leaf record"));
            }
            out.push((position, value[..32].try_into().unwrap(), value[32..].try_into().unwrap()));
        }
        Ok(out)
    }

    /// Node `(level, index)` as of `as_of` (see `AsOf`). Read from the
    /// stored tree wherever nothing below it changed since.
    pub fn node_as_of(&self, txn: &heed::RoTxn, as_of: &AsOf, level: usize, index: u64) -> Result<Octet> {
        let (lo, hi) = (index << level, (index + 1) << level);
        if lo >= as_of.count {
            return Ok(self.empty[level]);
        }
        if hi <= as_of.count && as_of.restored.range(lo..hi).next().is_none() {
            return self.get(txn, level, index);
        }
        if level == 0 {
            return Ok(match as_of.restored.get(&lo) {
                Some((commitment, nonce)) => leaf(commitment, nonce),
                None => self.get(txn, 0, lo)?,
            });
        }
        let left = self.node_as_of(txn, as_of, level - 1, 2 * index)?;
        let right = self.node_as_of(txn, as_of, level - 1, 2 * index + 1)?;
        Ok(node(level - 1, &left, &right))
    }

    /// The outputs at positions `lo..hi` unspent as of `as_of`, in order.
    pub fn unspent_as_of(&self, txn: &heed::RoTxn, as_of: &AsOf, lo: u64, hi: u64) -> Result<Vec<Entry>> {
        let hi = hi.min(as_of.count);
        if lo >= hi {
            return Ok(Vec::new());
        }
        let mut out = self.unspent_in(txn, lo, hi)?;
        out.extend(as_of.restored.range(lo..hi).map(|(&p, &(c, n))| (p, c, n)));
        out.sort_unstable_by_key(|e| e.0);
        Ok(out)
    }

    /// Replace the whole tree with `count` outputs, of which `unspent` (in
    /// position order) are unspent and the rest spent -- a snapshot
    /// (`snapshot`). Its root. Fully spent subtrees are stored as their
    /// root alone: nothing below one is ever read again (a path only
    /// passes through subtrees holding an unspent output or the next
    /// position, and reorgs never reach back past a snapshot).
    pub fn import(&self, wtxn: &mut heed::RwTxn, count: u64, unspent: &[Entry]) -> Result<[u8; 32]> {
        if count > 1 << DEPTH {
            return Err(Error::Full);
        }
        let in_order = unspent.windows(2).all(|w| w[0].0 < w[1].0);
        if !in_order || unspent.last().is_some_and(|e| e.0 >= count) {
            return Err(Error::Corrupt("snapshot entries out of order or out of range"));
        }
        self.nodes.clear(wtxn)?;
        self.leaves.clear(wtxn)?;
        let root = self.build(wtxn, DEPTH, 0, count, unspent)?;
        for (position, commitment, nonce) in unspent {
            self.put_leaf(wtxn, *position, commitment, nonce)?;
        }
        self.set_count(wtxn, count)?;
        Ok(digest_to_bytes(root))
    }

    fn build(&self, wtxn: &mut heed::RwTxn, level: usize, index: u64, count: u64, unspent: &[Entry]) -> Result<Octet> {
        let (lo, hi) = (index << level, (index + 1) << level);
        let hash = if lo >= count {
            return Ok(self.empty[level]);
        } else if unspent.is_empty() && hi <= count {
            self.spent[level]
        } else if level == 0 {
            match unspent {
                [(p, commitment, nonce)] if *p == lo => leaf(commitment, nonce),
                _ => return Err(Error::Corrupt("snapshot entries out of order or out of range")),
            }
        } else {
            let mid = lo + (1 << (level - 1));
            let split = unspent.partition_point(|e| e.0 < mid);
            let left = self.build(wtxn, level - 1, 2 * index, count, &unspent[..split])?;
            let right = self.build(wtxn, level - 1, 2 * index + 1, count, &unspent[split..])?;
            node(level - 1, &left, &right)
        };
        self.nodes.put(wtxn, &key(level, index), &digest_to_bytes(hash))?;
        Ok(hash)
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
        self.put_leaf(wtxn, position, commitment, nonce)?;
        self.set_count(wtxn, position + 1)?;
        Ok(position)
    }

    /// Mark the output at `position` spent.
    pub fn spend(&self, wtxn: &mut heed::RwTxn, position: u64) -> Result<()> {
        self.leaves.delete(wtxn, &position.to_be_bytes())?;
        self.set(wtxn, position, SPENT)
    }

    /// Undo `spend`: the output at `position` is unspent again.
    pub fn unspend(&self, wtxn: &mut heed::RwTxn, position: u64, commitment: &[u8; 32], nonce: &[u8; crate::recovery::NONCE_LEN]) -> Result<()> {
        self.put_leaf(wtxn, position, commitment, nonce)?;
        self.set(wtxn, position, leaf(commitment, nonce))
    }

    /// Undo the last `n` appends.
    pub fn truncate(&self, wtxn: &mut heed::RwTxn, n: u64) -> Result<()> {
        let count = self.count(wtxn)?;
        let keep = count.checked_sub(n).ok_or(Error::Corrupt("truncating below zero"))?;
        for position in keep..count {
            self.leaves.delete(wtxn, &position.to_be_bytes())?;
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

    /// `subtree_hash` and `import` agree with a tree built operation by
    /// operation; the imported tree then keeps working (spends, appends)
    /// exactly like the original.
    #[test]
    fn an_imported_snapshot_matches_and_keeps_working() {
        let (_d1, storage, tree) = open("import-src");
        let (_d2, storage2, imported) = open("import-dst");
        let mut wtxn = storage.write_txn().unwrap();
        for k in 0..300 {
            tree.push(&mut wtxn, &commitment(k), &nonce(k)).unwrap();
        }
        // Everything spent but a few, leaving fully spent regions.
        let keep = [5u64, 6, 130, 257, 299];
        for k in 0..300 {
            if !keep.contains(&k) {
                tree.spend(&mut wtxn, k).unwrap();
            }
        }
        let unspent = tree.unspent_in(&wtxn, 0, 1 << 40).unwrap();
        assert_eq!(unspent.iter().map(|e| e.0).collect::<Vec<_>>(), keep);
        let (empty, spent) = (empty_hashes(), spent_hashes());
        let root = tree.root(&wtxn).unwrap();
        assert_eq!(digest_to_bytes(subtree_hash(DEPTH, 0, 300, &unspent, &empty, &spent)), root);
        // A subtree on its own.
        let in_first = tree.unspent_in(&wtxn, 0, 256).unwrap();
        assert_eq!(subtree_hash(8, 0, 300, &in_first, &empty, &spent), tree.get(&wtxn, 8, 0).unwrap());

        let mut wtxn2 = storage2.write_txn().unwrap();
        assert_eq!(imported.import(&mut wtxn2, 300, &unspent).unwrap(), root);
        assert_eq!(imported.count(&wtxn2).unwrap(), 300);
        for &p in &keep {
            assert_eq!(imported.path(&wtxn2, p).unwrap(), tree.path(&wtxn, p).unwrap());
        }
        // Both go on the same way.
        for t in [(&tree, &mut wtxn), (&imported, &mut wtxn2)] {
            t.0.spend(t.1, 130).unwrap();
            t.0.push(t.1, &commitment(300), &nonce(300)).unwrap();
            t.0.spend(t.1, 300).unwrap();
            t.0.push(t.1, &commitment(301), &nonce(301)).unwrap();
        }
        assert_eq!(imported.root(&wtxn2).unwrap(), tree.root(&wtxn).unwrap());
        assert_eq!(imported.unspent_in(&wtxn2, 0, 1000).unwrap(), tree.unspent_in(&wtxn, 0, 1000).unwrap());
        // Out-of-range entries are refused.
        assert!(imported.import(&mut wtxn2, 3, &[(3, commitment(1), nonce(1))]).is_err());
    }

    /// Views as of an earlier state, from the current tree plus what
    /// changed since, match that earlier tree exactly.
    #[test]
    fn views_as_of_an_earlier_state() {
        let (_d, storage, tree) = open("as-of");
        let mut wtxn = storage.write_txn().unwrap();
        for k in 0..100 {
            tree.push(&mut wtxn, &commitment(k), &nonce(k)).unwrap();
        }
        for k in [1, 2, 3, 50] {
            tree.spend(&mut wtxn, k).unwrap();
        }
        let (root, unspent_then) = (tree.root(&wtxn).unwrap(), tree.unspent_in(&wtxn, 0, 100).unwrap());
        let level8 = tree.get(&wtxn, 8, 0).unwrap();
        // Later: spends of old outputs and new ones, and appends.
        let mut as_of = AsOf { count: 100, ..AsOf::default() };
        for k in [0, 4, 99] {
            tree.spend(&mut wtxn, k).unwrap();
            as_of.restored.insert(k, (commitment(k), nonce(k)));
        }
        for k in 100..140 {
            tree.push(&mut wtxn, &commitment(k), &nonce(k)).unwrap();
        }
        tree.spend(&mut wtxn, 120).unwrap();
        assert_ne!(tree.root(&wtxn).unwrap(), root);
        assert_eq!(digest_to_bytes(tree.node_as_of(&wtxn, &as_of, DEPTH, 0).unwrap()), root);
        assert_eq!(tree.node_as_of(&wtxn, &as_of, 8, 0).unwrap(), level8);
        assert_eq!(tree.unspent_as_of(&wtxn, &as_of, 0, 1000).unwrap(), unspent_then);
        let middle: Vec<Entry> = unspent_then.iter().filter(|e| (40..60).contains(&e.0)).copied().collect();
        assert_eq!(tree.unspent_as_of(&wtxn, &as_of, 40, 60).unwrap(), middle);
    }

}
