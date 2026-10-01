//! A Prunable Merkle Mountain Range (PMMR) storing `Output`s -- just
//! outputs, unlike designs (e.g. Grin's) that keep a separate PMMR per kind
//! of committed data (outputs, range proofs, kernels, ...).
//!
//! An MMR is an append-only structure built from a forest of perfect binary
//! trees ("peaks") whose heights mirror the binary representation of the
//! number of leaves. Appending a leaf may trigger a cascade of merges
//! (exactly like incrementing a binary counter and propagating carries);
//! the *root* is a single hash committing to the current set of peaks, and
//! from it a compact proof can show that one specific `Output` is included
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
//! hashes and parent/child links live in LMDB; `leaf_count` and the current
//! `peaks` (at most a few dozen entries even for billions of leaves) are
//! cached in memory and mirrored into a small metadata table so a reopened
//! PMMR picks up exactly where it left off.
//!
//! **Out of scope for now** (noted as explicit follow-up work, not
//! oversights): pruning/compaction of spent outputs, and rewinding to an
//! earlier size on a chain reorg. This module only covers append, root, and
//! inclusion proofs -- the core structure everything else builds on.

// `main.rs` doesn't call into this module yet (it just prints "Hello
// world!"), so allow dead code here rather than suppressing warnings
// piecemeal -- this module exists to be exercised by its tests for now.
#![allow(dead_code)]

use crate::output::Output;
use crate::poseidon2::hash_bytes_32;
use heed::types::Bytes;
use heed::{Database, Env, EnvOpenOptions};
use std::path::Path;

pub type Hash = [u8; 32];

/// Default LMDB map size: 1 GiB of reserved address space (not disk usage --
/// LMDB only consumes what's actually written). Plenty for development;
/// bump this (or reopen with a larger value) before storing more than that.
const DEFAULT_MAP_SIZE: usize = 1 << 30;

#[derive(Debug)]
pub enum Error {
    Io(std::io::Error),
    Heed(heed::Error),
    /// The on-disk metadata was missing or malformed -- e.g. opening a
    /// directory that isn't actually a PMMR this code created.
    Corrupt(&'static str),
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

/// A PMMR of `Output`s, backed by an LMDB environment. Every node (leaf and
/// internal) is stored by position, along with parent/child links used to
/// walk a leaf's path up to its peak when generating a proof.
pub struct Pmmr {
    env: Env,
    nodes: Database<Bytes, Bytes>,
    /// Present only for internal nodes: (left_pos, right_pos), 8 bytes each.
    /// Absence of a key means that position is a leaf.
    children: Database<Bytes, Bytes>,
    parent: Database<Bytes, Bytes>,
    meta: Database<Bytes, Bytes>,
    peaks: Vec<(u32, u64)>,
    leaf_count: u64,
    size: u64,
}

impl Pmmr {
    /// Open (creating if absent) a PMMR stored at `path`, with the default
    /// 1 GiB LMDB map size.
    pub fn open(path: &Path) -> Result<Self> {
        Self::open_with_map_size(path, DEFAULT_MAP_SIZE)
    }

    pub fn open_with_map_size(path: &Path, map_size: usize) -> Result<Self> {
        std::fs::create_dir_all(path)?;
        let env = unsafe {
            EnvOpenOptions::new()
                .map_size(map_size)
                .max_dbs(4)
                .open(path)?
        };

        let mut wtxn = env.write_txn()?;
        let nodes = env.create_database(&mut wtxn, Some("nodes"))?;
        let children = env.create_database(&mut wtxn, Some("children"))?;
        let parent = env.create_database(&mut wtxn, Some("parent"))?;
        let meta = env.create_database(&mut wtxn, Some("meta"))?;
        wtxn.commit()?;

        let rtxn = env.read_txn()?;
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
            env,
            nodes,
            children,
            parent,
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

    /// Append an output, returning the position its leaf was stored at. The
    /// leaf hash is the output's own bytes directly -- an `Output` is
    /// already a Poseidon2 commitment, so there's no need to hash it again
    /// at the leaf level. Durable once this returns: the write transaction
    /// backing it is committed before `push` returns.
    pub fn push(&mut self, output: &Output) -> Result<u64> {
        let mut wtxn = self.env.write_txn()?;

        let leaf_pos = self.size;
        self.nodes
            .put(&mut wtxn, &encode_pos(leaf_pos), &output.to_bytes())?;
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
            let mut child_bytes = [0u8; 16];
            child_bytes[0..8].copy_from_slice(&encode_pos(pos_second));
            child_bytes[8..16].copy_from_slice(&encode_pos(pos_top));
            self.children
                .put(&mut wtxn, &encode_pos(parent_pos), &child_bytes)?;
            self.parent
                .put(&mut wtxn, &encode_pos(pos_second), &encode_pos(parent_pos))?;
            self.parent
                .put(&mut wtxn, &encode_pos(pos_top), &encode_pos(parent_pos))?;

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
        let rtxn = self.env.read_txn()?;
        let mut ordered = Vec::with_capacity(self.peaks.len());
        for &(_, pos) in &self.peaks {
            ordered.push((pos, self.get_node(&rtxn, pos)?));
        }
        Ok(bag_peaks(&ordered))
    }

    /// Build an inclusion proof for the leaf at `leaf_pos`, or `None` if
    /// that position isn't a leaf in this PMMR.
    pub fn prove(&self, leaf_pos: u64) -> Result<Option<Proof>> {
        let rtxn = self.env.read_txn()?;

        if leaf_pos >= self.size || self.children.get(&rtxn, &encode_pos(leaf_pos))?.is_some() {
            return Ok(None);
        }

        let leaf_hash = self.get_node(&rtxn, leaf_pos)?;
        let mut path = Vec::new();
        let mut pos = leaf_pos;
        while let Some(parent_bytes) = self.parent.get(&rtxn, &encode_pos(pos))? {
            let parent_pos = decode_pos(parent_bytes)?;
            let child_bytes =
                self.children
                    .get(&rtxn, &encode_pos(parent_pos))?
                    .ok_or(Error::Corrupt(
                        "parent link without matching children entry",
                    ))?;
            let left = decode_pos(&child_bytes[0..8])?;
            let right = decode_pos(&child_bytes[8..16])?;
            if pos == left {
                path.push(ProofStep {
                    sibling_hash: self.get_node(&rtxn, right)?,
                    sibling_is_left: false,
                    parent_pos,
                });
            } else {
                path.push(ProofStep {
                    sibling_hash: self.get_node(&rtxn, left)?,
                    sibling_is_left: true,
                    parent_pos,
                });
            }
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
    use crate::wots::keygen;
    use std::sync::atomic::{AtomicU64, Ordering};

    fn output(byte: u8) -> Output {
        let (_, pk) = keygen(&[byte; 32]);
        Output::from_pubkey(&pk)
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
        let a = Pmmr::open(&dir_a.0).unwrap();
        let b = Pmmr::open(&dir_b.0).unwrap();
        assert_eq!(a.root().unwrap(), b.root().unwrap());
    }

    #[test]
    fn single_leaf_root_depends_on_leaf() {
        let dir_a = TempDir::new();
        let dir_b = TempDir::new();
        let mut a = Pmmr::open(&dir_a.0).unwrap();
        a.push(&output(1)).unwrap();
        let mut b = Pmmr::open(&dir_b.0).unwrap();
        b.push(&output(2)).unwrap();
        assert_ne!(a.root().unwrap(), b.root().unwrap());
    }

    #[test]
        fn single_leaf_root_depends_on_leaf_eq() {
        let dir_a = TempDir::new();
        let dir_b = TempDir::new();
        let mut a = Pmmr::open(&dir_a.0).unwrap();
        a.push(&output(1)).unwrap();
        let mut b = Pmmr::open(&dir_b.0).unwrap();
        b.push(&output(1)).unwrap();
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
        let mut mmr = Pmmr::open(&dir.0).unwrap();
        let expected_sizes = [1, 3, 4, 7];
        let expected_peak_counts = [1, 1, 2, 1];
        for (i, byte) in (1u8..=4).enumerate() {
            mmr.push(&output(byte)).unwrap();
            assert_eq!(mmr.size(), expected_sizes[i]);
            assert_eq!(mmr.peaks.len(), expected_peak_counts[i]);
        }
        assert_eq!(mmr.leaf_count(), 4);
    }

    #[test]
    fn every_leaf_proves_against_the_root() {
        let dir = TempDir::new();
        let mut mmr = Pmmr::open(&dir.0).unwrap();
        let mut leaf_positions = Vec::new();
        for byte in 1u8..=9 {
            leaf_positions.push(mmr.push(&output(byte)).unwrap());
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
        let mut mmr = Pmmr::open(&dir_a.0).unwrap();
        let pos = mmr.push(&output(1)).unwrap();
        mmr.push(&output(2)).unwrap();
        mmr.push(&output(3)).unwrap();
        let proof = mmr.prove(pos).unwrap().unwrap();

        let mut other = Pmmr::open(&dir_b.0).unwrap();
        other.push(&output(9)).unwrap();
        assert!(!proof.verify(other.root().unwrap()));
    }

    #[test]
    fn proof_rejects_tampered_leaf_hash() {
        let dir = TempDir::new();
        let mut mmr = Pmmr::open(&dir.0).unwrap();
        let pos = mmr.push(&output(1)).unwrap();
        mmr.push(&output(2)).unwrap();
        mmr.push(&output(3)).unwrap();
        let root = mmr.root().unwrap();

        let mut proof = mmr.prove(pos).unwrap().unwrap();
        proof.leaf_hash[0] ^= 1;
        assert!(!proof.verify(root));
    }

    #[test]
    fn proof_rejects_tampered_sibling() {
        let dir = TempDir::new();
        let mut mmr = Pmmr::open(&dir.0).unwrap();
        let pos = mmr.push(&output(1)).unwrap();
        mmr.push(&output(2)).unwrap();
        mmr.push(&output(3)).unwrap();
        mmr.push(&output(4)).unwrap();
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
        let mut mmr = Pmmr::open(&dir.0).unwrap();
        mmr.push(&output(1)).unwrap();
        mmr.push(&output(2)).unwrap(); // positions 0,1 are leaves; position 2 is their parent
        assert!(mmr.prove(2).unwrap().is_none());
    }

    #[test]
    fn reopening_resumes_from_persisted_state() {
        let dir = TempDir::new();
        let (root_before, leaf_pos) = {
            let mut mmr = Pmmr::open(&dir.0).unwrap();
            mmr.push(&output(1)).unwrap();
            mmr.push(&output(2)).unwrap();
            let pos = mmr.push(&output(3)).unwrap();
            (mmr.root().unwrap(), pos)
        };
        // `mmr` and its `Env` are fully dropped here; everything that
        // follows comes from what was actually durably written to disk.

        let mut reopened = Pmmr::open(&dir.0).unwrap();
        assert_eq!(reopened.leaf_count(), 3);
        assert_eq!(reopened.root().unwrap(), root_before);

        let proof = reopened.prove(leaf_pos).unwrap().unwrap();
        assert!(proof.verify(root_before));

        // Appending after reopening must continue from the right position,
        // not collide with or overwrite anything already stored.
        let new_pos = reopened.push(&output(4)).unwrap();
        assert_eq!(new_pos, 4);
        assert_ne!(reopened.root().unwrap(), root_before);
    }
}
