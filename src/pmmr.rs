//! A Prunable Merkle Mountain Range (PMMR) of raw 32-byte leaf hashes --
//! fully generic, with no notion of what a leaf actually represents. It
//! used to store `Output`s directly (hashing them itself); now the caller
//! supplies the leaf hash already computed, same as `merkle.rs`. That's
//! not just tidiness: the hash a leaf actually commits to is now a
//! privacy-preserving commitment (`H(H(pubkey) || amount)`, computed in
//! `block.rs`), and this module has no business knowing that, any more
//! than it needs to know what a pubkey or an amount is.
//!
//! An MMR is an append-only structure built from a forest of perfect binary
//! trees ("peaks") whose heights mirror the binary representation of the
//! number of leaves. Appending a leaf may trigger a cascade of merges
//! (exactly like incrementing a binary counter and propagating carries);
//! the *root* is a single hash committing to the current set of peaks, and
//! from it a compact proof can show that one specific leaf is included
//! without needing the rest of the set.
//!
//! This follows the same append/root structure Grin's PMMR uses, but is not
//! bit-compatible with it -- the exact hash input layout here (see
//! `node_hash` and `bag_peaks` below) is our own, clearly documented
//! choice, reusing the Poseidon2 primitives already built in this crate
//! rather than replicating Grin's.
//!
//! # Persistence
//!
//! Backed by LMDB via `heed` -- the dependency the project pulled in early
//! on and hadn't actually used until now. An ever-growing, randomly-accessed
//! append-only set like this is exactly what it's for: memory-mapped,
//! durable, and crash-safe, without holding the whole structure in RAM. Node
//! hashes live in LMDB, keyed by position; `leaf_count` and the current
//! `peaks` (at most a few dozen entries even for billions of leaves) are
//! cached in memory and mirrored into a small metadata table so a reopened
//! PMMR picks up exactly where it left off.
//!
//! The LMDB environment itself is opened by `crate::storage::Storage`, not
//! by this module -- `Pmmr::open` takes a `&Storage` rather than a path.
//! This is so the planned spent-output bitmap (for pruning) can later share
//! the exact same environment instead of opening a second one.
//!
//! # No stored parent/child links
//!
//! An earlier version of this module stored an explicit `parent` and
//! `children` table alongside `nodes`, so a proof's path from leaf to peak
//! could be found by following links instead of doing arithmetic. That's
//! simple to get right, but it roughly doubles storage: every node pays for
//! a links entry on top of its hash. Grin's PMMR avoids this entirely by
//! computing a position's height, parent, sibling, and left/right side
//! purely from its integer position -- the postorder numbering scheme makes
//! this possible with nothing but bit operations (see `peak_map_height`,
//! `family`, and `is_left_sibling` below, ported from
//! `core::core::pmmr::pmmr` in Grin's source and credited there). This is
//! the fiddly part of an MMR implementation to get right, so it's backed by
//! `bit_arithmetic_matches_reference_structure` below: an exhaustive
//! differential test comparing it, position by position across hundreds of
//! tree shapes, against a from-scratch reference that builds the same
//! links explicitly and independently.
//!
//! **Out of scope for now** (noted as explicit follow-up work, not
//! oversights): pruning/compaction of spent outputs, and rewinding to an
//! earlier size on a chain reorg. This module only covers append, root, and
//! inclusion proofs -- the core structure everything else builds on.

// `main.rs` doesn't call into this module yet (it just prints "Hello
// world!"), so allow dead code here rather than suppressing warnings
// piecemeal -- this module exists to be exercised by its tests for now.
#![allow(dead_code)]

use crate::poseidon2::hash_bytes_32;
use crate::storage::Storage;
use heed::Database;
use heed::types::Bytes;

pub type Hash = [u8; 32];

#[derive(Debug)]
pub enum Error {
    Storage(crate::storage::Error),
    Heed(heed::Error),
    /// The on-disk metadata was missing or malformed -- e.g. opening a
    /// directory that isn't actually a PMMR this code created.
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
            Error::Corrupt(msg) => write!(f, "corrupt PMMR metadata: {msg}"),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

/// `node_hash(pos, left, right) = Poseidon2(pos_bytes || left || right)`.
/// Folding the node's own position into its hash -- not just its
/// children -- domain-separates every node in the structure by where it
/// sits, so the same pair of child hashes occurring at two different
/// positions (in principle, across different-sized trees) never collides.
fn node_hash(pos: u64, left: Hash, right: Hash) -> Hash {
    let mut bytes = Vec::with_capacity(8 + 32 + 32);
    bytes.extend_from_slice(&pos.to_le_bytes());
    bytes.extend_from_slice(&left);
    bytes.extend_from_slice(&right);
    hash_bytes_32(&bytes)
}

/// Combine a set of peaks (ordered left to right, i.e. by ascending
/// position) into a single root: `Poseidon2(pos_0 || hash_0 || pos_1 ||
/// hash_1 || ...)`. One hash call over all peaks at once, rather than a
/// pairwise fold -- simpler to get right, and just as well-defined, since
/// the root is still a deterministic function of the ordered (position,
/// hash) sequence.
fn bag_peaks(peaks: &[(u64, Hash)]) -> Hash {
    let mut bytes = Vec::with_capacity(peaks.len() * 40);
    for (pos, hash) in peaks {
        bytes.extend_from_slice(&pos.to_le_bytes());
        bytes.extend_from_slice(hash);
    }
    hash_bytes_32(&bytes)
}

/// Total nodes (leaves + internal) stored after `leaf_count` leaves have
/// been pushed. Standard MMR identity: each push triggers exactly as many
/// merges as there are trailing one-bits carried away, so after `n` leaves
/// the structure has merged `n - popcount(n)` internal nodes into being.
fn size_for_leaf_count(leaf_count: u64) -> u64 {
    2 * leaf_count - leaf_count.count_ones() as u64
}

fn encode_pos(pos: u64) -> [u8; 8] {
    pos.to_be_bytes()
}

fn decode_pos(bytes: &[u8]) -> Result<u64> {
    bytes
        .try_into()
        .map(u64::from_be_bytes)
        .map_err(|_| Error::Corrupt("position value was not 8 bytes"))
}

fn encode_peaks(peaks: &[(u32, u64)]) -> Vec<u8> {
    let mut out = Vec::with_capacity(peaks.len() * 12);
    for (height, pos) in peaks {
        out.extend_from_slice(&height.to_be_bytes());
        out.extend_from_slice(&pos.to_be_bytes());
    }
    out
}

fn decode_peaks(bytes: &[u8]) -> Result<Vec<(u32, u64)>> {
    if bytes.len() % 12 != 0 {
        return Err(Error::Corrupt("peaks metadata had an invalid length"));
    }
    Ok(bytes
        .chunks_exact(12)
        .map(|c| {
            let height = u32::from_be_bytes(c[0..4].try_into().unwrap());
            let pos = u64::from_be_bytes(c[4..12].try_into().unwrap());
            (height, pos)
        })
        .collect())
}

const ALL_ONES: u64 = u64::MAX;

/// Decomposes `pos0` (treated as a running node count) into a sum of
/// perfect-subtree sizes (each `2^k - 1`), greedily from largest to
/// smallest. Returns `(peak_map, height)`: `height` is `pos0`'s own
/// postorder height (0 for a leaf), and `peak_map`'s bits double as the
/// left/right turns along the path from `pos0` up to its eventual peak --
/// bit `h` set means "a subtree of height `h` was already accounted for,"
/// which turns out to be exactly the left/right indicator `family` needs.
/// Ported from Grin's `peak_map_height` (`core/src/core/pmmr/pmmr.rs`).
fn peak_map_height(pos0: u64) -> (u64, u64) {
    if pos0 == 0 {
        return (0, 0);
    }
    let mut remaining = pos0;
    let mut peak_size = ALL_ONES >> remaining.leading_zeros();
    let mut peak_map = 0u64;
    while peak_size != 0 {
        peak_map <<= 1;
        if remaining >= peak_size {
            remaining -= peak_size;
            peak_map |= 1;
        }
        peak_size >>= 1;
    }
    (peak_map, remaining)
}

/// The postorder height of the node at position `pos0` (0 for a leaf).
fn bintree_postorder_height(pos0: u64) -> u64 {
    peak_map_height(pos0).1
}

fn is_leaf(pos0: u64) -> bool {
    bintree_postorder_height(pos0) == 0
}

/// Parent and sibling position of `pos0`, computed purely from `pos0`
/// itself -- correct regardless of how large the tree later grows, since a
/// position's local structure never changes once it's built.
fn family(pos0: u64) -> (u64, u64) {
    let (peak_map, height) = peak_map_height(pos0);
    let peak = 1u64 << height;
    if (peak_map & peak) != 0 {
        (pos0 + 1, pos0 + 1 - 2 * peak)
    } else {
        (pos0 + 2 * peak, pos0 + 2 * peak - 1)
    }
}

/// Whether `pos0` is the left (as opposed to right) child of its parent.
fn is_left_sibling(pos0: u64) -> bool {
    let (peak_map, height) = peak_map_height(pos0);
    (peak_map & (1u64 << height)) == 0
}

/// One step of an inclusion proof's path from a leaf up to the peak that
/// contains it.
#[derive(Clone, Copy, Debug)]
pub struct ProofStep {
    pub sibling_hash: Hash,
    /// Whether the sibling is the *left* child at this merge (i.e. our
    /// running hash was the right child).
    pub sibling_is_left: bool,
    /// The position the merge of (sibling, running hash) was stored at.
    pub parent_pos: u64,
}

/// An inclusion proof for one leaf: enough to recompute the root from just
/// the leaf's own hash and position, with no access to the rest of the
/// PMMR.
#[derive(Clone, Debug)]
pub struct Proof {
    pub leaf_pos: u64,
    pub leaf_hash: Hash,
    /// Path from the leaf up to (but not including) the peak that contains
    /// it.
    pub path: Vec<ProofStep>,
    /// Every *other* peak, excluding the one this leaf's path leads to,
    /// ordered by ascending position.
    pub other_peaks: Vec<(u64, Hash)>,
}

impl Proof {
    /// Verify this proof against a known root, with nothing else needed --
    /// mirrors the same "verifier only needs what's actually self-contained"
    /// principle as `wots::verify`.
    pub fn verify(&self, root: Hash) -> bool {
        let mut cur_pos = self.leaf_pos;
        let mut cur_hash = self.leaf_hash;
        for step in &self.path {
            cur_hash = if step.sibling_is_left {
                node_hash(step.parent_pos, step.sibling_hash, cur_hash)
            } else {
                node_hash(step.parent_pos, cur_hash, step.sibling_hash)
            };
            cur_pos = step.parent_pos;
        }

        let mut peaks = self.other_peaks.clone();
        peaks.push((cur_pos, cur_hash));
        peaks.sort_by_key(|(pos, _)| *pos);
        bag_peaks(&peaks) == root
    }
}

/// A PMMR of raw leaf hashes, backed by an LMDB environment (see
/// `crate::storage::Storage`). Every node (leaf and internal) is stored by
/// position; a leaf's path up to its peak, for proof generation, is
/// computed arithmetically (see `family`/`is_left_sibling` above) rather
/// than stored.
pub struct Pmmr {
    storage: Storage,
    nodes: Database<Bytes, Bytes>,
    meta: Database<Bytes, Bytes>,
    peaks: Vec<(u32, u64)>,
    leaf_count: u64,
    size: u64,
}

impl Pmmr {
    /// Open this PMMR's tables within the given storage context, creating
    /// them if they don't already exist.
    pub fn open(storage: &Storage) -> Result<Self> {
        let nodes = storage.database("nodes")?;
        let meta = storage.database("meta")?;

        let rtxn = storage.read_txn()?;
        let leaf_count = match meta.get(&rtxn, b"leaf_count".as_slice())? {
            Some(bytes) => decode_pos(bytes)?,
            None => 0,
        };
        let peaks = match meta.get(&rtxn, b"peaks".as_slice())? {
            Some(bytes) => decode_peaks(bytes)?,
            None => Vec::new(),
        };
        rtxn.commit()?;

        Ok(Pmmr {
            storage: storage.clone(),
            nodes,
            meta,
            size: size_for_leaf_count(leaf_count),
            leaf_count,
            peaks,
        })
    }

    pub fn leaf_count(&self) -> u64 {
        self.leaf_count
    }

    /// Total number of nodes stored (leaves + internal).
    pub fn size(&self) -> u64 {
        self.size
    }

    /// Append a leaf hash, returning the position it was stored at. The
    /// caller is responsible for having already hashed whatever the leaf
    /// is supposed to commit to -- this module has no idea, and doesn't
    /// need to. Durable once this returns: the write transaction backing
    /// it is committed before `push` returns.
    pub fn push(&mut self, leaf_hash: Hash) -> Result<u64> {
        let mut wtxn = self.storage.write_txn()?;

        let leaf_pos = self.size;
        self.nodes.put(&mut wtxn, &encode_pos(leaf_pos), &leaf_hash)?;
        self.size += 1;
        self.leaf_count += 1;

        self.peaks.push((0, leaf_pos));
        while self.peaks.len() >= 2 {
            let (h_top, pos_top) = self.peaks[self.peaks.len() - 1];
            let (h_second, pos_second) = self.peaks[self.peaks.len() - 2];
            if h_top != h_second {
                break;
            }
            self.peaks.pop();
            self.peaks.pop();

            let left_hash = self.get_node(&wtxn, pos_second)?;
            let right_hash = self.get_node(&wtxn, pos_top)?;
            let parent_pos = self.size;
            let parent_hash = node_hash(parent_pos, left_hash, right_hash);

            self.nodes
                .put(&mut wtxn, &encode_pos(parent_pos), &parent_hash)?;
            self.size += 1;

            self.peaks.push((h_second + 1, parent_pos));
        }

        self.meta.put(
            &mut wtxn,
            b"leaf_count".as_slice(),
            &encode_pos(self.leaf_count),
        )?;
        self.meta
            .put(&mut wtxn, b"peaks".as_slice(), &encode_peaks(&self.peaks))?;

        wtxn.commit()?;
        Ok(leaf_pos)
    }

    /// The current root: all peaks bagged together. The root of an empty
    /// PMMR is defined as the hash of an empty byte string.
    pub fn root(&self) -> Result<Hash> {
        let rtxn = self.storage.read_txn()?;
        let mut ordered = Vec::with_capacity(self.peaks.len());
        for &(_, pos) in &self.peaks {
            ordered.push((pos, self.get_node(&rtxn, pos)?));
        }
        Ok(bag_peaks(&ordered))
    }

    /// Build an inclusion proof for the leaf at `leaf_pos`, or `None` if
    /// that position isn't a leaf in this PMMR.
    pub fn prove(&self, leaf_pos: u64) -> Result<Option<Proof>> {
        let rtxn = self.storage.read_txn()?;

        if leaf_pos >= self.size || !is_leaf(leaf_pos) {
            return Ok(None);
        }

        let leaf_hash = self.get_node(&rtxn, leaf_pos)?;
        let mut path = Vec::new();
        let mut pos = leaf_pos;
        // Walk from the leaf toward its peak. `family` gives the parent and
        // sibling positions purely from `pos`'s own value; the loop stops
        // once the computed parent would fall outside the tree as it
        // currently stands, i.e. `pos` is itself a peak.
        while pos + 1 < self.size {
            let (parent_pos, sibling_pos) = family(pos);
            if parent_pos >= self.size {
                break;
            }
            path.push(ProofStep {
                sibling_hash: self.get_node(&rtxn, sibling_pos)?,
                sibling_is_left: !is_left_sibling(pos),
                parent_pos,
            });
            pos = parent_pos;
        }
        // `pos` is now the position of the peak containing this leaf.

        let mut other_peaks = Vec::new();
        for &(_, p) in &self.peaks {
            if p != pos {
                other_peaks.push((p, self.get_node(&rtxn, p)?));
            }
        }

        Ok(Some(Proof {
            leaf_pos,
            leaf_hash,
            path,
            other_peaks,
        }))
    }

    fn get_node(&self, txn: &heed::RoTxn, pos: u64) -> Result<Hash> {
        let bytes = self
            .nodes
            .get(txn, &encode_pos(pos))?
            .ok_or(Error::Corrupt("referenced node position has no entry"))?;
        bytes
            .try_into()
            .map_err(|_| Error::Corrupt("node value was not 32 bytes"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    /// An arbitrary but distinct 32-byte leaf hash for test purposes --
    /// this module doesn't care what a leaf represents, so there's no
    /// need to route through `Output`/`wots` here at all anymore.
    fn leaf(byte: u8) -> Hash {
        hash_bytes_32(&[byte; 1])
    }

    /// Builds the same merge structure `Pmmr::push` does, but as a
    /// from-scratch, independent reference: explicit `parent_of`/`children_of`
    /// tables (exactly what this module used to store in LMDB, before this
    /// turn's change), used only to check the arithmetic functions above
    /// against. Deliberately separate code from `push`'s peak-merge loop, so
    /// a bug in one is unlikely to be mirrored in the other.
    fn build_reference_links(n_leaves: u64) -> (Vec<Option<u64>>, Vec<Option<(u64, u64)>>, u64) {
        let mut parent_of: Vec<Option<u64>> = Vec::new();
        let mut children_of: Vec<Option<(u64, u64)>> = Vec::new();
        let mut peaks: Vec<(u32, u64)> = Vec::new();
        let mut size = 0u64;

        for _ in 0..n_leaves {
            let leaf_pos = size;
            parent_of.push(None);
            children_of.push(None);
            size += 1;

            peaks.push((0, leaf_pos));
            while peaks.len() >= 2 {
                let (h_top, pos_top) = peaks[peaks.len() - 1];
                let (h_second, pos_second) = peaks[peaks.len() - 2];
                if h_top != h_second {
                    break;
                }
                peaks.pop();
                peaks.pop();

                let parent_pos = size;
                parent_of.push(None);
                children_of.push(Some((pos_second, pos_top)));
                size += 1;
                parent_of[pos_second as usize] = Some(parent_pos);
                parent_of[pos_top as usize] = Some(parent_pos);

                peaks.push((h_second + 1, parent_pos));
            }
        }

        (parent_of, children_of, size)
    }

    /// The exhaustive check backing the removal of the stored parent/children
    /// tables: for 300 different tree shapes (1 to 300 leaves) and every
    /// single position within each, confirm `is_leaf`, `family`, and
    /// `is_left_sibling` -- pure position arithmetic -- agree with the
    /// independent reference structure above, built by a completely separate
    /// piece of code. This is what justifies trusting the arithmetic instead
    /// of the explicit tables it replaced.
    #[test]
    fn bit_arithmetic_matches_reference_structure() {
        for n in 1..=300u64 {
            let (parent_of, children_of, size) = build_reference_links(n);

            for pos in 0..size {
                let expected_is_leaf = children_of[pos as usize].is_none();
                assert_eq!(
                    is_leaf(pos),
                    expected_is_leaf,
                    "is_leaf mismatch at n={n} pos={pos}"
                );

                match parent_of[pos as usize] {
                    None => {
                        // `pos` is currently a peak -- `family` must agree
                        // there's no parent built yet.
                        let (parent_pos, _) = family(pos);
                        assert!(
                            parent_pos >= size,
                            "n={n} pos={pos}: expected no parent yet, \
                             family() gave {parent_pos} but size is {size}"
                        );
                    }
                    Some(expected_parent) => {
                        let (parent_pos, sibling_pos) = family(pos);
                        assert_eq!(
                            parent_pos, expected_parent,
                            "parent mismatch at n={n} pos={pos}"
                        );

                        let (left, right) = children_of[expected_parent as usize].unwrap();
                        let expected_sibling = if pos == left { right } else { left };
                        assert_eq!(
                            sibling_pos, expected_sibling,
                            "sibling mismatch at n={n} pos={pos}"
                        );

                        assert_eq!(
                            is_left_sibling(pos),
                            pos == left,
                            "is_left_sibling mismatch at n={n} pos={pos}"
                        );
                    }
                }
            }
        }
    }

    /// A fresh, uniquely-named temp directory per test, cleaned up on drop.
    struct TempDir(std::path::PathBuf);

    impl TempDir {
        fn new() -> Self {
            static COUNTER: AtomicU64 = AtomicU64::new(0);
            let n = COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!("pmmr-test-{}-{n}", std::process::id()));
            std::fs::create_dir_all(&path).unwrap();
            TempDir(path)
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn empty_root_is_deterministic() {
        let dir_a = TempDir::new();
        let dir_b = TempDir::new();
        let storage_a = Storage::open(&dir_a.0).unwrap();
        let a = Pmmr::open(&storage_a).unwrap();
        let storage_b = Storage::open(&dir_b.0).unwrap();
        let b = Pmmr::open(&storage_b).unwrap();
        assert_eq!(a.root().unwrap(), b.root().unwrap());
    }

    #[test]
    fn single_leaf_root_depends_on_leaf() {
        let dir_a = TempDir::new();
        let dir_b = TempDir::new();
        let storage_a = Storage::open(&dir_a.0).unwrap();
        let mut a = Pmmr::open(&storage_a).unwrap();
        a.push(leaf(1)).unwrap();
        let storage_b = Storage::open(&dir_b.0).unwrap();
        let mut b = Pmmr::open(&storage_b).unwrap();
        b.push(leaf(2)).unwrap();
        assert_ne!(a.root().unwrap(), b.root().unwrap());
    }

    #[test]
    fn single_leaf_root_depends_on_leaf_eq() {
        let dir_a = TempDir::new();
        let dir_b = TempDir::new();
        let storage_a = Storage::open(&dir_a.0).unwrap();
        let mut a = Pmmr::open(&storage_a).unwrap();
        a.push(leaf(1)).unwrap();
        let storage_b = Storage::open(&dir_b.0).unwrap();
        let mut b = Pmmr::open(&storage_b).unwrap();
        b.push(leaf(1)).unwrap();
        assert_eq!(a.root().unwrap(), b.root().unwrap());
    }

    #[test]
    fn structure_sizes_match_known_mmr_shapes() {
        // Tracing the standard MMR merge algorithm by hand:
        // 1 leaf  -> 1 node,  1 peak (height 0)
        // 2 leaves-> 3 nodes, 1 peak (height 1)
        // 3 leaves-> 4 nodes, 2 peaks (heights 1, 0)
        // 4 leaves-> 7 nodes, 1 peak (height 2)
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut mmr = Pmmr::open(&storage).unwrap();
        let expected_sizes = [1, 3, 4, 7];
        let expected_peak_counts = [1, 1, 2, 1];
        for (i, byte) in (1u8..=4).enumerate() {
            mmr.push(leaf(byte)).unwrap();
            assert_eq!(mmr.size(), expected_sizes[i]);
            assert_eq!(mmr.peaks.len(), expected_peak_counts[i]);
        }
        assert_eq!(mmr.leaf_count(), 4);
    }

    #[test]
    fn every_leaf_proves_against_the_root() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut mmr = Pmmr::open(&storage).unwrap();
        let mut leaf_positions = Vec::new();
        for byte in 1u8..=9 {
            leaf_positions.push(mmr.push(leaf(byte)).unwrap());
        }
        let root = mmr.root().unwrap();

        for &pos in &leaf_positions {
            let proof = mmr
                .prove(pos)
                .unwrap()
                .expect("leaf position should be provable");
            assert!(proof.verify(root));
        }
    }

    #[test]
    fn proof_rejects_wrong_root() {
        let dir_a = TempDir::new();
        let dir_b = TempDir::new();
        let storage_a = Storage::open(&dir_a.0).unwrap();
        let mut mmr = Pmmr::open(&storage_a).unwrap();
        let pos = mmr.push(leaf(1)).unwrap();
        mmr.push(leaf(2)).unwrap();
        mmr.push(leaf(3)).unwrap();
        let proof = mmr.prove(pos).unwrap().unwrap();

        let storage_b = Storage::open(&dir_b.0).unwrap();
        let mut other = Pmmr::open(&storage_b).unwrap();
        other.push(leaf(9)).unwrap();
        assert!(!proof.verify(other.root().unwrap()));
    }

    #[test]
    fn proof_rejects_tampered_leaf_hash() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut mmr = Pmmr::open(&storage).unwrap();
        let pos = mmr.push(leaf(1)).unwrap();
        mmr.push(leaf(2)).unwrap();
        mmr.push(leaf(3)).unwrap();
        let root = mmr.root().unwrap();

        let mut proof = mmr.prove(pos).unwrap().unwrap();
        proof.leaf_hash[0] ^= 1;
        assert!(!proof.verify(root));
    }

    #[test]
    fn proof_rejects_tampered_sibling() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut mmr = Pmmr::open(&storage).unwrap();
        let pos = mmr.push(leaf(1)).unwrap();
        mmr.push(leaf(2)).unwrap();
        mmr.push(leaf(3)).unwrap();
        mmr.push(leaf(4)).unwrap();
        let root = mmr.root().unwrap();

        let mut proof = mmr.prove(pos).unwrap().unwrap();
        assert!(
            !proof.path.is_empty(),
            "with 4 leaves, leaf 0 has a non-empty path"
        );
        proof.path[0].sibling_hash[0] ^= 1;
        assert!(!proof.verify(root));
    }

    #[test]
    fn non_leaf_position_is_not_provable() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut mmr = Pmmr::open(&storage).unwrap();
        mmr.push(leaf(1)).unwrap();
        mmr.push(leaf(2)).unwrap(); // positions 0,1 are leaves; position 2 is their parent
        assert!(mmr.prove(2).unwrap().is_none());
    }

    #[test]
    fn reopening_resumes_from_persisted_state() {
        let dir = TempDir::new();
        let (root_before, leaf_pos) = {
            let storage = Storage::open(&dir.0).unwrap();
            let mut mmr = Pmmr::open(&storage).unwrap();
            mmr.push(leaf(1)).unwrap();
            mmr.push(leaf(2)).unwrap();
            let pos = mmr.push(leaf(3)).unwrap();
            (mmr.root().unwrap(), pos)
        };
        // `mmr` and `storage` (and the `Env` it held) are fully dropped
        // here; everything that follows comes from what was actually
        // durably written to disk.

        let storage = Storage::open(&dir.0).unwrap();
        let mut reopened = Pmmr::open(&storage).unwrap();
        assert_eq!(reopened.leaf_count(), 3);
        assert_eq!(reopened.root().unwrap(), root_before);

        let proof = reopened.prove(leaf_pos).unwrap().unwrap();
        assert!(proof.verify(root_before));

        // Appending after reopening must continue from the right position,
        // not collide with or overwrite anything already stored.
        let new_pos = reopened.push(leaf(4)).unwrap();
        assert_eq!(new_pos, 4);
        assert_ne!(reopened.root().unwrap(), root_before);
    }
}
