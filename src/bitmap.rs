//! A sparse, updatable bitmap committed via a Merkle tree over fixed-size
//! pages. Unlike `pmmr` (append-only), **any bit here can be set at any
//! time** -- which is exactly the property needed to track spent/unspent
//! status: an output created long ago can transition from unspent to spent
//! at any later point, not just at the moment it was created.
//!
//! This module knows nothing about `pmmr`, `Output`, or spending -- it's a
//! general-purpose "position -> bit, with a Merkle commitment" structure,
//! same layering discipline as the rest of this crate: general-purpose
//! modules don't know about their specific consumers. Whatever eventually
//! calls this (block validation) is the thing that knows "bit at position
//! P" means "the output at PMMR position P has been spent" -- this module
//! just stores and commits to bits by position.
//!
//! # Structure
//!
//! Positions are grouped into fixed `PAGE_BYTES`-byte pages (`PAGE_BITS`
//! bits each); a complete binary Merkle tree of `DEPTH` levels sits above
//! them, wide enough that every `u64` position maps to a unique page
//! (`2^DEPTH` pages * `PAGE_BITS` bits/page = `2^64`). A page -- and every
//! subtree above it -- that's never been touched is implicitly all-zero
//! and is never actually stored; it's represented by one precomputed hash
//! per level (`empty_hash[k]`, the hash of an all-zero subtree of that
//! height) rather than real data. That's what keeps `set`/`get`/`root` all
//! `O(DEPTH)` regardless of how much of the position space has ever
//! actually been touched -- there's no "resize" operation, the tree is
//! always logically complete and only ever sparsely materialized.

// `main.rs` doesn't call into this module yet (it just prints "Hello
// world!"), so allow dead code here rather than suppressing warnings
// piecemeal -- this module exists to be exercised by its tests for now.
#![allow(dead_code)]

use crate::poseidon2::hash_bytes_32;
use crate::storage::Storage;
use heed::Database;
use heed::types::Bytes;

pub type Hash = [u8; 32];

/// Bytes per page.
pub const PAGE_BYTES: usize = 4096;
/// Bits per page.
const PAGE_BITS: u64 = (PAGE_BYTES as u64) * 8;
/// Levels above the pages, chosen so every `u64` position maps to a unique
/// page: `2^DEPTH` pages * `PAGE_BITS` bits/page = `2^64`.
const DEPTH: u32 = 49;

#[derive(Debug)]
pub enum Error {
    Storage(crate::storage::Error),
    Heed(heed::Error),
    /// Stored page/node data didn't have the expected length -- e.g.
    /// opening a directory that isn't actually a bitmap this code created.
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
            Error::Corrupt(msg) => write!(f, "corrupt bitmap data: {msg}"),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

fn page_index(position: u64) -> u64 {
    position / PAGE_BITS
}

fn bit_offset(position: u64) -> usize {
    (position % PAGE_BITS) as usize
}

fn encode_page_index(index: u64) -> [u8; 8] {
    index.to_be_bytes()
}

fn encode_node_key(level: u32, index: u64) -> [u8; 12] {
    let mut out = [0u8; 12];
    out[0..4].copy_from_slice(&level.to_be_bytes());
    out[4..12].copy_from_slice(&index.to_be_bytes());
    out
}

fn empty_page() -> [u8; PAGE_BYTES] {
    [0u8; PAGE_BYTES]
}

/// `node_hash(level, left, right) = Poseidon2(level_bytes || left || right)`.
/// `level` is the level of the *parent* produced by combining `left` and
/// `right`, included for the same domain-separation reasons `pmmr::node_hash`
/// includes a position: deliberately *not* including the node's own index,
/// though -- every untouched subtree at a given level must hash to the same
/// `empty_hash[level]` regardless of where in the tree it sits, which is
/// exactly what makes the sparse storage below work.
fn node_hash(level: u32, left: Hash, right: Hash) -> Hash {
    let mut bytes = Vec::with_capacity(4 + 32 + 32);
    bytes.extend_from_slice(&level.to_le_bytes());
    bytes.extend_from_slice(&left);
    bytes.extend_from_slice(&right);
    hash_bytes_32(&bytes)
}

/// `empty_hash[0]` is the hash of an all-zero page; `empty_hash[k]` is the
/// hash of an all-zero subtree of height `k` built from two
/// `empty_hash[k-1]` children. Recomputed fresh on every `open` rather than
/// cached globally -- cheap (49 Poseidon2 calls), and keeps this module
/// free of any static/global state.
fn empty_hashes() -> [Hash; (DEPTH + 1) as usize] {
    let mut hashes = [[0u8; 32]; (DEPTH + 1) as usize];
    hashes[0] = hash_bytes_32(&empty_page());
    for level in 1..=DEPTH as usize {
        hashes[level] = node_hash(level as u32, hashes[level - 1], hashes[level - 1]);
    }
    hashes
}

/// An inclusion proof for one page: enough to recompute the root from just
/// that page's own bytes, with no access to the rest of the bitmap.
#[derive(Clone)]
pub struct Proof {
    pub page_index: u64,
    pub page: [u8; PAGE_BYTES],
    /// Sibling hashes from level 0 (the page's own sibling page) up to
    /// level `DEPTH - 1`, length always `DEPTH`.
    pub siblings: Vec<Hash>,
}

impl Proof {
    /// The bit at `position` according to this proof's page. `position`
    /// must fall within this proof's page (debug-checked, not enforced in
    /// release builds -- callers are expected to request a proof for the
    /// page a position actually belongs to).
    pub fn bit(&self, position: u64) -> bool {
        debug_assert_eq!(page_index(position), self.page_index);
        let offset = bit_offset(position);
        (self.page[offset / 8] >> (offset % 8)) & 1 == 1
    }

    pub fn verify(&self, root: Hash) -> bool {
        if self.siblings.len() != DEPTH as usize {
            return false;
        }
        let mut index = self.page_index;
        let mut hash = hash_bytes_32(&self.page);
        for (level, &sibling) in (1..=DEPTH).zip(self.siblings.iter()) {
            hash = if index & 1 == 0 {
                node_hash(level, hash, sibling)
            } else {
                node_hash(level, sibling, hash)
            };
            index /= 2;
        }
        hash == root
    }
}

/// A sparse bitmap, backed by an LMDB environment (see
/// `crate::storage::Storage`). Pages and the internal nodes above them are
/// stored only once touched; everything else defaults to the precomputed
/// `empty_hash` for its level.
pub struct Bitmap {
    storage: Storage,
    pages: Database<Bytes, Bytes>,
    nodes: Database<Bytes, Bytes>,
    empty_hashes: [Hash; (DEPTH + 1) as usize],
}

impl Bitmap {
    /// Open this bitmap's tables within the given storage context, creating
    /// them if they don't already exist.
    pub fn open(storage: &Storage) -> Result<Self> {
        let pages = storage.database("bitmap_pages")?;
        let nodes = storage.database("bitmap_nodes")?;
        Ok(Bitmap {
            storage: storage.clone(),
            pages,
            nodes,
            empty_hashes: empty_hashes(),
        })
    }

    pub fn get(&self, position: u64) -> Result<bool> {
        let rtxn = self.storage.read_txn()?;
        let page = self.load_page(&rtxn, page_index(position))?;
        let offset = bit_offset(position);
        Ok((page[offset / 8] >> (offset % 8)) & 1 == 1)
    }

    /// Set the bit at `position` to `value`, updating every ancestor hash
    /// up to the root in the same write transaction.
    pub fn set(&mut self, position: u64, value: bool) -> Result<()> {
        let mut wtxn = self.storage.write_txn()?;

        let pidx = page_index(position);
        let mut page = self.load_page(&wtxn, pidx)?;
        let offset = bit_offset(position);
        if value {
            page[offset / 8] |= 1 << (offset % 8);
        } else {
            page[offset / 8] &= !(1u8 << (offset % 8));
        }
        self.pages.put(&mut wtxn, &encode_page_index(pidx), &page)?;

        let mut index = pidx;
        let mut hash = hash_bytes_32(&page);
        for level in 1..=DEPTH {
            let sibling_index = index ^ 1;
            let sibling = self.load_node(&wtxn, level - 1, sibling_index)?;
            hash = if index & 1 == 0 {
                node_hash(level, hash, sibling)
            } else {
                node_hash(level, sibling, hash)
            };
            index /= 2;
            self.nodes
                .put(&mut wtxn, &encode_node_key(level, index), &hash)?;
        }

        wtxn.commit()?;
        Ok(())
    }

    /// The current root: the hash at the top of the tree, `empty_hash[DEPTH]`
    /// if nothing has ever been set.
    pub fn root(&self) -> Result<Hash> {
        let rtxn = self.storage.read_txn()?;
        self.load_node(&rtxn, DEPTH, 0)
    }

    /// Build an inclusion proof for the page containing `position`.
    pub fn prove(&self, position: u64) -> Result<Proof> {
        let rtxn = self.storage.read_txn()?;
        let pidx = page_index(position);
        let page = self.load_page(&rtxn, pidx)?;

        let mut siblings = Vec::with_capacity(DEPTH as usize);
        let mut index = pidx;
        for level in 1..=DEPTH {
            let sibling_index = index ^ 1;
            siblings.push(self.load_node(&rtxn, level - 1, sibling_index)?);
            index /= 2;
        }

        Ok(Proof {
            page_index: pidx,
            page,
            siblings,
        })
    }

    fn load_page(&self, txn: &heed::RoTxn, index: u64) -> Result<[u8; PAGE_BYTES]> {
        match self.pages.get(txn, &encode_page_index(index))? {
            Some(bytes) => bytes
                .try_into()
                .map_err(|_| Error::Corrupt("page value was not PAGE_BYTES bytes")),
            None => Ok(empty_page()),
        }
    }

    /// The hash at `(level, index)`: for level 0, derived fresh from the
    /// stored (or implicitly empty) page; for higher levels, the stored
    /// node if present, else `empty_hashes[level]`.
    fn load_node(&self, txn: &heed::RoTxn, level: u32, index: u64) -> Result<Hash> {
        if level == 0 {
            return Ok(hash_bytes_32(&self.load_page(txn, index)?));
        }
        match self.nodes.get(txn, &encode_node_key(level, index))? {
            Some(bytes) => bytes
                .try_into()
                .map_err(|_| Error::Corrupt("node value was not 32 bytes")),
            None => Ok(self.empty_hashes[level as usize]),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    struct TempDir(std::path::PathBuf);

    impl TempDir {
        fn new() -> Self {
            static COUNTER: AtomicU64 = AtomicU64::new(0);
            let n = COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!("bitmap-test-{}-{n}", std::process::id()));
            std::fs::create_dir_all(&path).unwrap();
            TempDir(path)
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn open() -> (TempDir, Bitmap) {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let bitmap = Bitmap::open(&storage).unwrap();
        (dir, bitmap)
    }

    #[test]
    fn empty_bitmap_root_is_the_precomputed_empty_hash() {
        let (_dir, bitmap) = open();
        assert_eq!(bitmap.root().unwrap(), empty_hashes()[DEPTH as usize]);
    }

    #[test]
    fn set_then_get_roundtrips() {
        let (_dir, mut bitmap) = open();
        assert!(!bitmap.get(42).unwrap());
        bitmap.set(42, true).unwrap();
        assert!(bitmap.get(42).unwrap());
    }

    #[test]
    fn unrelated_positions_are_unaffected() {
        let (_dir, mut bitmap) = open();
        bitmap.set(42, true).unwrap();
        assert!(!bitmap.get(41).unwrap());
        assert!(!bitmap.get(43).unwrap());
        // A position in a entirely different page.
        assert!(!bitmap.get(10_000_000).unwrap());
    }

    #[test]
    fn clearing_a_bit_restores_the_empty_root() {
        let (_dir, mut bitmap) = open();
        let empty_root = bitmap.root().unwrap();
        bitmap.set(42, true).unwrap();
        assert_ne!(bitmap.root().unwrap(), empty_root);
        bitmap.set(42, false).unwrap();
        assert_eq!(bitmap.root().unwrap(), empty_root);
    }

    #[test]
    fn setting_any_bit_changes_the_root() {
        let (_dir, mut bitmap) = open();
        let before = bitmap.root().unwrap();
        bitmap.set(123_456_789, true).unwrap();
        assert_ne!(bitmap.root().unwrap(), before);
    }

    #[test]
    fn order_of_setting_bits_does_not_affect_the_final_root() {
        let (dir_a, mut a) = open();
        let (dir_b, mut b) = open();
        a.set(1, true).unwrap();
        a.set(2, true).unwrap();
        a.set(100_000, true).unwrap();
        b.set(100_000, true).unwrap();
        b.set(2, true).unwrap();
        b.set(1, true).unwrap();
        assert_eq!(a.root().unwrap(), b.root().unwrap());
        drop(dir_a);
        drop(dir_b);
    }

    #[test]
    fn touching_a_position_near_u64_max_works() {
        let (_dir, mut bitmap) = open();
        let position = u64::MAX - 7;
        bitmap.set(position, true).unwrap();
        assert!(bitmap.get(position).unwrap());
        assert!(!bitmap.get(u64::MAX).unwrap());
    }

    #[test]
    fn reopening_resumes_from_persisted_state() {
        let dir = TempDir::new();
        let root_before = {
            let storage = Storage::open(&dir.0).unwrap();
            let mut bitmap = Bitmap::open(&storage).unwrap();
            bitmap.set(7, true).unwrap();
            bitmap.set(999_999, true).unwrap();
            bitmap.root().unwrap()
        };

        let storage = Storage::open(&dir.0).unwrap();
        let reopened = Bitmap::open(&storage).unwrap();
        assert!(reopened.get(7).unwrap());
        assert!(reopened.get(999_999).unwrap());
        assert_eq!(reopened.root().unwrap(), root_before);
    }

    #[test]
    fn proof_verifies_against_the_root() {
        let (_dir, mut bitmap) = open();
        bitmap.set(42, true).unwrap();
        let root = bitmap.root().unwrap();

        let proof = bitmap.prove(42).unwrap();
        assert!(proof.bit(42));
        assert!(proof.verify(root));
    }

    #[test]
    fn proof_rejects_tampered_page() {
        let (_dir, mut bitmap) = open();
        bitmap.set(42, true).unwrap();
        let root = bitmap.root().unwrap();

        let mut proof = bitmap.prove(42).unwrap();
        proof.page[0] ^= 1;
        assert!(!proof.verify(root));
    }

    #[test]
    fn proof_rejects_tampered_sibling() {
        let (_dir, mut bitmap) = open();
        bitmap.set(42, true).unwrap();
        bitmap.set(100_000, true).unwrap();
        let root = bitmap.root().unwrap();

        let mut proof = bitmap.prove(42).unwrap();
        proof.siblings[0][0] ^= 1;
        assert!(!proof.verify(root));
    }

    /// The core sparse-tree arithmetic, hand-traced independently rather
    /// than just calling `set`/`root` and trusting them: position 0 sits at
    /// index 0 at every level on the way up, so its sibling is always
    /// `empty_hashes[level]` at every step. This is exactly the kind of
    /// bit/index arithmetic that's easy to get subtly wrong, so it's worth
    /// confirming against an independently-computed expected value, not
    /// just the module's own internal consistency.
    #[test]
    fn single_leftmost_bit_matches_hand_traced_root() {
        let (_dir, mut bitmap) = open();
        bitmap.set(0, true).unwrap();

        let empties = empty_hashes();
        let mut expected = {
            let mut page = [0u8; PAGE_BYTES];
            page[0] = 1;
            hash_bytes_32(&page)
        };
        for level in 1..=DEPTH {
            // Position 0 is page index 0, which is a left child (index even)
            // at every level on the way up.
            expected = node_hash(level, expected, empties[(level - 1) as usize]);
        }

        assert_eq!(bitmap.root().unwrap(), expected);
    }

    /// Same idea, but for a page that's a *right* child at the first step
    /// (page index 1), to exercise the other branch of the left/right
    /// ordering logic.
    #[test]
    fn single_right_child_page_matches_hand_traced_root() {
        let (_dir, mut bitmap) = open();
        // Position within page index 1 (page 1 covers positions
        // [PAGE_BITS, 2*PAGE_BITS)).
        let position = PAGE_BITS;
        bitmap.set(position, true).unwrap();

        let empties = empty_hashes();
        let mut page = [0u8; PAGE_BYTES];
        page[0] = 1;
        let mut hash = hash_bytes_32(&page);
        let mut index: u64 = 1;
        for level in 1..=DEPTH {
            hash = if index & 1 == 0 {
                node_hash(level, hash, empties[(level - 1) as usize])
            } else {
                node_hash(level, empties[(level - 1) as usize], hash)
            };
            index /= 2;
        }

        assert_eq!(bitmap.root().unwrap(), hash);
    }

    /// Two sibling pages (indices 0 and 1) both touched: they must combine
    /// with *each other* at level 1, not each independently against the
    /// empty default.
    #[test]
    fn sibling_pages_combine_with_each_other_not_with_empty() {
        let (_dir, mut bitmap) = open();
        bitmap.set(0, true).unwrap(); // page 0
        bitmap.set(PAGE_BITS, true).unwrap(); // page 1

        let empties = empty_hashes();
        let mut page0 = [0u8; PAGE_BYTES];
        page0[0] = 1;
        let mut page1 = [0u8; PAGE_BYTES];
        page1[0] = 1;
        let h0 = hash_bytes_32(&page0);
        let h1 = hash_bytes_32(&page1);

        // Level 1: page 0 and page 1 are siblings, combined with each other.
        let mut hash = node_hash(1, h0, h1);
        // From level 2 up, this combined subtree's sibling is always empty.
        for level in 2..=DEPTH {
            hash = node_hash(level, hash, empties[(level - 1) as usize]);
        }

        assert_eq!(bitmap.root().unwrap(), hash);
    }
}
