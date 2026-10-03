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
//! # Persistence, and why there's no in-memory cache
//!
//! Backed by LMDB via `heed`. Node hashes live in `nodes`, keyed by
//! position; `leaf_count` and the current `peaks` (at most a few dozen
//! entries even for billions of leaves) live in a small `meta` table --
//! and that's genuinely the *only* copy of them. An earlier version of
//! this module cached `leaf_count`/`peaks`/`size` as struct fields,
//! mirroring them into `meta` on every `push` purely so a reopened PMMR
//! could pick up where it left off. That cache is gone now: every method
//! reads `leaf_count`/`peaks` fresh from `meta`, through whichever
//! transaction the caller hands in, every time.
//!
//! That's not a performance regression worth worrying about (`meta`'s
//! entries are tiny, and writing them was already happening on every
//! `push` regardless) -- it's what makes this module safely composable
//! with others inside one shared transaction. `push` no longer opens or
//! commits a transaction of its own; the caller (`chain.rs`, eventually)
//! does, and can thread the same transaction through `Bitmap` and
//! `UtxoIndex` calls too, committing once at the end or dropping
//! everything on failure. With no cached field of our own, there's
//! nothing here that could end up out of sync with a transaction that
//! might still be rolled back -- `self` has no state *to* roll back.
//!
//! The LMDB environment itself is opened by `crate::storage::Storage`, not
//! by this module -- `Pmmr::open` takes a `&Storage` rather than a path,
//! which is what lets `Bitmap` and `UtxoIndex` share the exact same
//! environment (and now, the exact same transaction) instead of each
//! opening their own.
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
//! # Rewinding
//!
//! `truncate` restores the exact `leaf_count`/`peaks` (and therefore
//! `root`) an earlier, smaller version of this same PMMR had -- the
//! one new primitive chain-level reorg support needs from this
//! module. It's cheap and needs no historical snapshots: the MMR
//! shape for a given leaf count is a deterministic function of that
//! count alone, so the new peaks are just recomputed from scratch
//! (`peaks_for_leaf_count`), and nothing under the new size is ever
//! actually deleted (see `truncate`'s own docs for why that's fine).
//!
//! **Still out of scope** (noted as explicit follow-up work, not an
//! oversight): pruning/compaction of spent outputs -- `truncate`
//! rewinds the *shape*, but reclaiming the storage of leaves that will
//! never be rewound back to is a separate concern this module doesn't
//! address yet.

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
    /// `truncate` was asked for a `new_leaf_count` larger than the
    /// current one -- growing the PMMR is `push`'s job, not
    /// `truncate`'s.
    WouldGrow,
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
            Error::WouldGrow => write!(f, "truncate's new_leaf_count exceeds the current leaf_count"),
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

/// The `(height, position)` of every peak a PMMR with exactly
/// `leaf_count` leaves has -- computed fresh, independent of
/// `push`/`truncate`, by replaying the same merge *bookkeeping* `push`
/// does (sizes, heights, positions) without touching storage or
/// computing a single real hash. The MMR shape for a given leaf count
/// is a deterministic function of that count alone (standard MMR
/// property: it mirrors the count's binary representation), so this
/// never needs to know what was actually pushed, only how many times.
///
/// What `truncate` uses to figure out the new `peaks` it needs to
/// write -- deliberately *not* shared code with `push`'s own loop
/// (which interleaves this same bookkeeping with real hash reads/
/// writes), so a bug in one is unlikely to be mirrored in the other.
/// The round-trip tests below (push to N, remember the root; push
/// more; truncate back to N; the root must match exactly) are what
/// actually cross-checks the two against each other.
fn peaks_for_leaf_count(leaf_count: u64) -> Vec<(u32, u64)> {
    let mut size: u64 = 0;
    let mut peaks: Vec<(u32, u64)> = Vec::new();

    for _ in 0..leaf_count {
        let leaf_pos = size;
        size += 1;
        peaks.push((0, leaf_pos));
        while peaks.len() >= 2 {
            let (h_top, _) = peaks[peaks.len() - 1];
            let (h_second, _) = peaks[peaks.len() - 2];
            if h_top != h_second {
                break;
            }
            peaks.pop();
            peaks.pop();
            let parent_pos = size;
            size += 1;
            peaks.push((h_second + 1, parent_pos));
        }
    }

    peaks
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
/// than stored. Holds no state of its own beyond the database handles --
/// see the module docs on why.
pub struct Pmmr {
    storage: Storage,
    nodes: Database<Bytes, Bytes>,
    meta: Database<Bytes, Bytes>,
}

impl Pmmr {
    /// Open this PMMR's tables within the given storage context, creating
    /// them if they don't already exist. Doesn't touch a transaction at
    /// all -- there's no cached state left to seed from `meta`.
    pub fn open(storage: &Storage) -> Result<Self> {
        let nodes = storage.database("nodes")?;
        let meta = storage.database("meta")?;
        Ok(Pmmr {
            storage: storage.clone(),
            nodes,
            meta,
        })
    }

    /// Number of leaves pushed so far, read fresh from `meta` through
    /// `txn`. `txn` can be a plain `RoTxn`, or the same `RwTxn` an
    /// in-progress `push` is using (a write transaction can always read
    /// its own pending writes).
    pub fn leaf_count(&self, txn: &heed::RoTxn) -> Result<u64> {
        match self.meta.get(txn, b"leaf_count".as_slice())? {
            Some(bytes) => decode_pos(bytes),
            None => Ok(0),
        }
    }

    /// Total number of nodes stored (leaves + internal), derived from
    /// `leaf_count`.
    pub fn size(&self, txn: &heed::RoTxn) -> Result<u64> {
        Ok(size_for_leaf_count(self.leaf_count(txn)?))
    }

    fn peaks(&self, txn: &heed::RoTxn) -> Result<Vec<(u32, u64)>> {
        match self.meta.get(txn, b"peaks".as_slice())? {
            Some(bytes) => decode_peaks(bytes),
            None => Ok(Vec::new()),
        }
    }

    /// Append a leaf hash, returning the position it was stored at. The
    /// caller is responsible for having already hashed whatever the leaf
    /// is supposed to commit to -- this module has no idea, and doesn't
    /// need to. Reads the current `leaf_count`/`peaks` fresh from `meta`
    /// through `wtxn` and writes the updated versions back through the
    /// same transaction -- nothing is committed here; that's the caller's
    /// call, once (potentially) every other store it's updating in the
    /// same transaction has also succeeded.
    pub fn push(&mut self, wtxn: &mut heed::RwTxn, leaf_hash: Hash) -> Result<u64> {
        let mut leaf_count = self.leaf_count(wtxn)?;
        let mut size = size_for_leaf_count(leaf_count);
        let mut peaks = self.peaks(wtxn)?;

        let leaf_pos = size;
        self.nodes.put(wtxn, &encode_pos(leaf_pos), &leaf_hash)?;
        size += 1;
        leaf_count += 1;

        peaks.push((0, leaf_pos));
        while peaks.len() >= 2 {
            let (h_top, pos_top) = peaks[peaks.len() - 1];
            let (h_second, pos_second) = peaks[peaks.len() - 2];
            if h_top != h_second {
                break;
            }
            peaks.pop();
            peaks.pop();

            let left_hash = self.get_node(wtxn, pos_second)?;
            let right_hash = self.get_node(wtxn, pos_top)?;
            let parent_pos = size;
            let parent_hash = node_hash(parent_pos, left_hash, right_hash);

            self.nodes.put(wtxn, &encode_pos(parent_pos), &parent_hash)?;
            size += 1;

            peaks.push((h_second + 1, parent_pos));
        }

        self.meta.put(wtxn, b"leaf_count".as_slice(), &encode_pos(leaf_count))?;
        self.meta.put(wtxn, b"peaks".as_slice(), &encode_peaks(&peaks))?;

        Ok(leaf_pos)
    }

    /// Roll back to exactly the state a PMMR with only `new_leaf_count`
    /// leaves pushed would have -- same `leaf_count`, same `peaks`,
    /// and therefore the same `root` and the same proofs for every
    /// leaf still within range. Fails with `Error::WouldGrow` if
    /// `new_leaf_count` is larger than the current `leaf_count`;
    /// growing is `push`'s job.
    ///
    /// Doesn't touch `nodes` at all: every leaf and internal node
    /// beyond the new size simply becomes unreferenced (nothing will
    /// ever look it up again, since `leaf_count`/`peaks` are the only
    /// things that say what's "current"), not deleted. That's
    /// deliberate, not an oversight -- pruning/compaction is still out
    /// of scope (see the module docs), and there's nothing to reclaim
    /// here that LMDB would actually shrink anyway. A later `push`
    /// picks up again from `new_leaf_count` and will overwrite those
    /// unreferenced positions as it goes, which is exactly what should
    /// happen once this PMMR's chain has truly moved on.
    ///
    /// This is the one new primitive chain-level reorg support needs
    /// from this module: unwinding back to a common ancestor means
    /// restoring that ancestor's own leaf count exactly, and nothing
    /// about *which* leaves existed back then needs to be recorded
    /// separately -- it's fully determined by the count alone.
    pub fn truncate(&mut self, wtxn: &mut heed::RwTxn, new_leaf_count: u64) -> Result<()> {
        let current = self.leaf_count(wtxn)?;
        if new_leaf_count > current {
            return Err(Error::WouldGrow);
        }

        let peaks = peaks_for_leaf_count(new_leaf_count);
        self.meta.put(wtxn, b"leaf_count".as_slice(), &encode_pos(new_leaf_count))?;
        self.meta.put(wtxn, b"peaks".as_slice(), &encode_peaks(&peaks))?;
        Ok(())
    }

    /// The current root: all peaks bagged together. The root of an empty
    /// PMMR is defined as the hash of an empty byte string.
    pub fn root(&self, txn: &heed::RoTxn) -> Result<Hash> {
        let peaks = self.peaks(txn)?;
        let mut ordered = Vec::with_capacity(peaks.len());
        for &(_, pos) in &peaks {
            ordered.push((pos, self.get_node(txn, pos)?));
        }
        Ok(bag_peaks(&ordered))
    }

    /// Build an inclusion proof for the leaf at `leaf_pos`, or `None` if
    /// that position isn't a leaf in this PMMR.
    pub fn prove(&self, txn: &heed::RoTxn, leaf_pos: u64) -> Result<Option<Proof>> {
        let size = self.size(txn)?;
        if leaf_pos >= size || !is_leaf(leaf_pos) {
            return Ok(None);
        }

        let leaf_hash = self.get_node(txn, leaf_pos)?;
        let mut path = Vec::new();
        let mut pos = leaf_pos;
        // Walk from the leaf toward its peak. `family` gives the parent and
        // sibling positions purely from `pos`'s own value; the loop stops
        // once the computed parent would fall outside the tree as it
        // currently stands, i.e. `pos` is itself a peak.
        while pos + 1 < size {
            let (parent_pos, sibling_pos) = family(pos);
            if parent_pos >= size {
                break;
            }
            path.push(ProofStep {
                sibling_hash: self.get_node(txn, sibling_pos)?,
                sibling_is_left: !is_left_sibling(pos),
                parent_pos,
            });
            pos = parent_pos;
        }
        // `pos` is now the position of the peak containing this leaf.

        let peaks = self.peaks(txn)?;
        let mut other_peaks = Vec::new();
        for &(_, p) in &peaks {
            if p != pos {
                other_peaks.push((p, self.get_node(txn, p)?));
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

    /// Push one leaf in its own, immediately-committed transaction --
    /// most tests below don't care about batching multiple writes into
    /// one transaction, just about the resulting structure.
    fn push_committed(storage: &Storage, mmr: &mut Pmmr, leaf_hash: Hash) -> u64 {
        let mut wtxn = storage.write_txn().unwrap();
        let pos = mmr.push(&mut wtxn, leaf_hash).unwrap();
        wtxn.commit().unwrap();
        pos
    }

    fn truncate_committed(storage: &Storage, mmr: &mut Pmmr, new_leaf_count: u64) -> Result<()> {
        let mut wtxn = storage.write_txn().unwrap();
        let result = mmr.truncate(&mut wtxn, new_leaf_count);
        if result.is_ok() {
            wtxn.commit().unwrap();
        }
        result
    }

    fn root(storage: &Storage, mmr: &Pmmr) -> Hash {
        let rtxn = storage.read_txn().unwrap();
        mmr.root(&rtxn).unwrap()
    }

    fn size(storage: &Storage, mmr: &Pmmr) -> u64 {
        let rtxn = storage.read_txn().unwrap();
        mmr.size(&rtxn).unwrap()
    }

    fn leaf_count(storage: &Storage, mmr: &Pmmr) -> u64 {
        let rtxn = storage.read_txn().unwrap();
        mmr.leaf_count(&rtxn).unwrap()
    }

    fn peak_count(storage: &Storage, mmr: &Pmmr) -> usize {
        let rtxn = storage.read_txn().unwrap();
        mmr.peaks(&rtxn).unwrap().len()
    }

    fn prove(storage: &Storage, mmr: &Pmmr, leaf_pos: u64) -> Option<Proof> {
        let rtxn = storage.read_txn().unwrap();
        mmr.prove(&rtxn, leaf_pos).unwrap()
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
        assert_eq!(root(&storage_a, &a), root(&storage_b, &b));
    }

    #[test]
    fn single_leaf_root_depends_on_leaf() {
        let dir_a = TempDir::new();
        let dir_b = TempDir::new();
        let storage_a = Storage::open(&dir_a.0).unwrap();
        let mut a = Pmmr::open(&storage_a).unwrap();
        push_committed(&storage_a, &mut a, leaf(1));
        let storage_b = Storage::open(&dir_b.0).unwrap();
        let mut b = Pmmr::open(&storage_b).unwrap();
        push_committed(&storage_b, &mut b, leaf(2));
        assert_ne!(root(&storage_a, &a), root(&storage_b, &b));
    }

    #[test]
    fn single_leaf_root_depends_on_leaf_eq() {
        let dir_a = TempDir::new();
        let dir_b = TempDir::new();
        let storage_a = Storage::open(&dir_a.0).unwrap();
        let mut a = Pmmr::open(&storage_a).unwrap();
        push_committed(&storage_a, &mut a, leaf(1));
        let storage_b = Storage::open(&dir_b.0).unwrap();
        let mut b = Pmmr::open(&storage_b).unwrap();
        push_committed(&storage_b, &mut b, leaf(1));
        assert_eq!(root(&storage_a, &a), root(&storage_b, &b));
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
            push_committed(&storage, &mut mmr, leaf(byte));
            assert_eq!(size(&storage, &mmr), expected_sizes[i]);
            assert_eq!(peak_count(&storage, &mmr), expected_peak_counts[i]);
        }
        assert_eq!(leaf_count(&storage, &mmr), 4);
    }

    #[test]
    fn every_leaf_proves_against_the_root() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut mmr = Pmmr::open(&storage).unwrap();
        let mut leaf_positions = Vec::new();
        for byte in 1u8..=9 {
            leaf_positions.push(push_committed(&storage, &mut mmr, leaf(byte)));
        }
        let expected_root = root(&storage, &mmr);

        for &pos in &leaf_positions {
            let proof = prove(&storage, &mmr, pos).expect("leaf position should be provable");
            assert!(proof.verify(expected_root));
        }
    }

    #[test]
    fn proof_rejects_wrong_root() {
        let dir_a = TempDir::new();
        let dir_b = TempDir::new();
        let storage_a = Storage::open(&dir_a.0).unwrap();
        let mut mmr = Pmmr::open(&storage_a).unwrap();
        let pos = push_committed(&storage_a, &mut mmr, leaf(1));
        push_committed(&storage_a, &mut mmr, leaf(2));
        push_committed(&storage_a, &mut mmr, leaf(3));
        let proof = prove(&storage_a, &mmr, pos).unwrap();

        let storage_b = Storage::open(&dir_b.0).unwrap();
        let mut other = Pmmr::open(&storage_b).unwrap();
        push_committed(&storage_b, &mut other, leaf(9));
        assert!(!proof.verify(root(&storage_b, &other)));
    }

    #[test]
    fn proof_rejects_tampered_leaf_hash() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut mmr = Pmmr::open(&storage).unwrap();
        let pos = push_committed(&storage, &mut mmr, leaf(1));
        push_committed(&storage, &mut mmr, leaf(2));
        push_committed(&storage, &mut mmr, leaf(3));
        let expected_root = root(&storage, &mmr);

        let mut proof = prove(&storage, &mmr, pos).unwrap();
        proof.leaf_hash[0] ^= 1;
        assert!(!proof.verify(expected_root));
    }

    #[test]
    fn proof_rejects_tampered_sibling() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut mmr = Pmmr::open(&storage).unwrap();
        let pos = push_committed(&storage, &mut mmr, leaf(1));
        push_committed(&storage, &mut mmr, leaf(2));
        push_committed(&storage, &mut mmr, leaf(3));
        push_committed(&storage, &mut mmr, leaf(4));
        let expected_root = root(&storage, &mmr);

        let mut proof = prove(&storage, &mmr, pos).unwrap();
        assert!(
            !proof.path.is_empty(),
            "with 4 leaves, leaf 0 has a non-empty path"
        );
        proof.path[0].sibling_hash[0] ^= 1;
        assert!(!proof.verify(expected_root));
    }

    #[test]
    fn non_leaf_position_is_not_provable() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut mmr = Pmmr::open(&storage).unwrap();
        push_committed(&storage, &mut mmr, leaf(1));
        push_committed(&storage, &mut mmr, leaf(2)); // positions 0,1 are leaves; position 2 is their parent
        assert!(prove(&storage, &mmr, 2).is_none());
    }

    #[test]
    fn reopening_resumes_from_persisted_state() {
        let dir = TempDir::new();
        let (root_before, leaf_pos) = {
            let storage = Storage::open(&dir.0).unwrap();
            let mut mmr = Pmmr::open(&storage).unwrap();
            // All three pushes batched into one transaction, to exercise
            // that `push` can be called repeatedly against the same
            // transaction before anything commits.
            let mut wtxn = storage.write_txn().unwrap();
            mmr.push(&mut wtxn, leaf(1)).unwrap();
            mmr.push(&mut wtxn, leaf(2)).unwrap();
            let pos = mmr.push(&mut wtxn, leaf(3)).unwrap();
            wtxn.commit().unwrap();
            (root(&storage, &mmr), pos)
        };
        // `mmr` and `storage` (and the `Env` it held) are fully dropped
        // here; everything that follows comes from what was actually
        // durably written to disk.

        let storage = Storage::open(&dir.0).unwrap();
        let mut reopened = Pmmr::open(&storage).unwrap();
        assert_eq!(leaf_count(&storage, &reopened), 3);
        assert_eq!(root(&storage, &reopened), root_before);

        let proof = prove(&storage, &reopened, leaf_pos).unwrap();
        assert!(proof.verify(root_before));

        // Appending after reopening must continue from the right position,
        // not collide with or overwrite anything already stored.
        let new_pos = push_committed(&storage, &mut reopened, leaf(4));
        assert_eq!(new_pos, 4);
        assert_ne!(root(&storage, &reopened), root_before);
    }

    #[test]
    fn truncate_rejects_growing_past_the_current_leaf_count() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut mmr = Pmmr::open(&storage).unwrap();
        push_committed(&storage, &mut mmr, leaf(1));
        push_committed(&storage, &mut mmr, leaf(2));

        let err = truncate_committed(&storage, &mut mmr, 3).unwrap_err();
        assert!(matches!(err, Error::WouldGrow));
        // Nothing should have changed.
        assert_eq!(leaf_count(&storage, &mmr), 2);
    }

    #[test]
    fn truncate_to_the_current_leaf_count_is_a_no_op() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut mmr = Pmmr::open(&storage).unwrap();
        for byte in 1u8..=6 {
            push_committed(&storage, &mut mmr, leaf(byte));
        }
        let before = root(&storage, &mmr);

        truncate_committed(&storage, &mut mmr, 6).unwrap();
        assert_eq!(root(&storage, &mmr), before);
        assert_eq!(leaf_count(&storage, &mmr), 6);
    }

    #[test]
    fn truncate_to_zero_restores_the_empty_root() {
        let dir_a = TempDir::new();
        let dir_b = TempDir::new();
        let storage_a = Storage::open(&dir_a.0).unwrap();
        let mut mmr = Pmmr::open(&storage_a).unwrap();
        let empty_root = root(&storage_a, &mmr); // before any pushes at all
        for byte in 1u8..=10 {
            push_committed(&storage_a, &mut mmr, leaf(byte));
        }

        truncate_committed(&storage_a, &mut mmr, 0).unwrap();
        assert_eq!(leaf_count(&storage_a, &mmr), 0);
        assert_eq!(root(&storage_a, &mmr), empty_root);

        // Cross-checked against an entirely separate, never-touched PMMR.
        let storage_b = Storage::open(&dir_b.0).unwrap();
        let b = Pmmr::open(&storage_b).unwrap();
        assert_eq!(root(&storage_a, &mmr), root(&storage_b, &b));
    }

    /// The key correctness property for reorg support: truncating back
    /// to `n` leaves must restore *exactly* the root (and `leaf_count`)
    /// a PMMR that only ever had `n` leaves pushed would have -- not
    /// just some different-but-plausible root. Checked against
    /// snapshots actually recorded while pushing (41 of them, for 0
    /// through 40 leaves), not a separately-derived expectation --
    /// this is the real thing `peaks_for_leaf_count` has to agree with
    /// `push` on, for every shape from totally empty up through several
    /// rounds of carrying merges.
    #[test]
    fn truncate_recovers_every_earlier_root_exactly() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut mmr = Pmmr::open(&storage).unwrap();

        let mut roots_by_count = vec![root(&storage, &mmr)]; // index 0: empty
        for byte in 1u8..=40 {
            push_committed(&storage, &mut mmr, leaf(byte));
            roots_by_count.push(root(&storage, &mmr));
        }

        // Descending, since `truncate` can only ever move to a smaller
        // leaf count than whatever it's currently at.
        for n in (0..=40u64).rev() {
            truncate_committed(&storage, &mut mmr, n).unwrap();
            assert_eq!(leaf_count(&storage, &mmr), n, "leaf_count mismatch after truncating to {n}");
            assert_eq!(
                root(&storage, &mmr),
                roots_by_count[n as usize],
                "root mismatch after truncating to {n}"
            );
        }
    }

    /// The property that actually matters for a reorg: after rewinding
    /// and pushing a *different* continuation, the result must be
    /// indistinguishable from a PMMR whose history never included the
    /// discarded leaves at all -- not just "some" self-consistent
    /// state.
    #[test]
    fn pushing_a_different_continuation_after_truncate_matches_never_having_diverged() {
        let dir_a = TempDir::new();
        let storage_a = Storage::open(&dir_a.0).unwrap();
        let mut a = Pmmr::open(&storage_a).unwrap();
        for byte in 1u8..=5 {
            push_committed(&storage_a, &mut a, leaf(byte));
        }
        // `a` goes on to leaves 6 and 7, then gets rewound -- as if a
        // competing chain, built on top of the same first 5 leaves,
        // turned out to be the one that should have won instead.
        push_committed(&storage_a, &mut a, leaf(6));
        push_committed(&storage_a, &mut a, leaf(7));
        truncate_committed(&storage_a, &mut a, 5).unwrap();
        push_committed(&storage_a, &mut a, leaf(99));
        push_committed(&storage_a, &mut a, leaf(100));

        let dir_b = TempDir::new();
        let storage_b = Storage::open(&dir_b.0).unwrap();
        let mut b = Pmmr::open(&storage_b).unwrap();
        for byte in [1u8, 2, 3, 4, 5, 99, 100] {
            push_committed(&storage_b, &mut b, leaf(byte));
        }

        assert_eq!(leaf_count(&storage_a, &a), leaf_count(&storage_b, &b));
        assert_eq!(root(&storage_a, &a), root(&storage_b, &b));
    }

    #[test]
    fn truncate_sees_pushes_still_pending_in_the_same_transaction() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut mmr = Pmmr::open(&storage).unwrap();

        let mut wtxn = storage.write_txn().unwrap();
        mmr.push(&mut wtxn, leaf(1)).unwrap();
        mmr.push(&mut wtxn, leaf(2)).unwrap();
        mmr.push(&mut wtxn, leaf(3)).unwrap();
        // Truncating back to 1, all within the same, still-uncommitted
        // transaction -- confirms `truncate` reads `leaf_count` through
        // `wtxn` itself, not some separately-committed value, same
        // composability `push` already relies on.
        mmr.truncate(&mut wtxn, 1).unwrap();
        assert_eq!(mmr.leaf_count(&wtxn).unwrap(), 1);
        wtxn.commit().unwrap();

        assert_eq!(leaf_count(&storage, &mmr), 1);
    }

    #[test]
    fn truncated_state_persists_after_reopening() {
        let dir = TempDir::new();
        let root_after_truncate = {
            let storage = Storage::open(&dir.0).unwrap();
            let mut mmr = Pmmr::open(&storage).unwrap();
            for byte in 1u8..=5 {
                push_committed(&storage, &mut mmr, leaf(byte));
            }
            truncate_committed(&storage, &mut mmr, 2).unwrap();
            root(&storage, &mmr)
        };

        let storage = Storage::open(&dir.0).unwrap();
        let reopened = Pmmr::open(&storage).unwrap();
        assert_eq!(leaf_count(&storage, &reopened), 2);
        assert_eq!(root(&storage, &reopened), root_after_truncate);
    }

    #[test]
    fn proof_for_a_position_beyond_the_truncated_size_is_unavailable() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut mmr = Pmmr::open(&storage).unwrap();
        let positions: Vec<u64> = (1u8..=5).map(|b| push_committed(&storage, &mut mmr, leaf(b))).collect();

        truncate_committed(&storage, &mut mmr, 3).unwrap();

        // The first three leaves are still provable against the new root.
        let new_root = root(&storage, &mmr);
        for &pos in &positions[..3] {
            let proof = prove(&storage, &mmr, pos).expect("still within range");
            assert!(proof.verify(new_root));
        }
        // Positions beyond the truncated size are gone, even though the
        // underlying node data technically still sits in `nodes`.
        for &pos in &positions[3..] {
            assert!(prove(&storage, &mmr, pos).is_none());
        }
    }
}
