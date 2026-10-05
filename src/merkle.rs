//! A vector commitment: commit to a power-of-two-length sequence of
//! leaves -- arbitrary byte strings: one field element, an extension
//! element, or a whole row of a STARK trace -- via a standard binary
//! Merkle tree, and open/verify individual indices against the root.
//!
//! This is the building block FRI's folding/query protocol sits on top of
//! -- each folding round commits to a new, half-length vector of
//! evaluations using exactly this scheme, and the query phase opens
//! specific indices from it -- but there's no FRI-specific logic here at
//! all. Same layering discipline as the rest of this crate: this is a
//! general-purpose "commit to a vector, open an index" tool, and whatever
//! uses it (FRI, eventually) is the thing that knows what the committed
//! values actually mean.

#![allow(dead_code)]

use crate::poseidon2::{
    BabyBear, DOMAIN_MERKLE_LEAF, DOMAIN_MERKLE_NODE, LANES, digest_from_bytes, digest_to_bytes, hash_octets, hash_octets_lanes,
    hash_pair, hash_pair_lanes,
};

pub type Hash = [u8; 32];

/// A leaf's hash: its bytes read as little-endian 4-byte field elements
/// (every leaf here is field elements: trace rows, extension values),
/// hashed with `hash_octets` under the leaf domain -- which keeps a leaf
/// from ever hashing like an internal node -- and its byte length.
pub(crate) fn leaf_hash(leaf: &[u8]) -> Hash {
    let elements: Vec<BabyBear> = leaf
        .chunks(4)
        .map(|chunk| {
            let mut padded = [0u8; 4];
            padded[..chunk.len()].copy_from_slice(chunk);
            BabyBear::from_bytes(padded)
        })
        .collect();
    digest_to_bytes(hash_octets(DOMAIN_MERKLE_LEAF, leaf.len(), &elements))
}

/// `leaf_hash` of a leaf of field elements (their 4-byte encodings),
/// without building the bytes.
pub(crate) fn leaf_hash_elements(elements: &[BabyBear]) -> Hash {
    digest_to_bytes(hash_octets(DOMAIN_MERKLE_LEAF, 4 * elements.len(), elements))
}

/// `leaf_hash_elements` of `count` leaves at once, `leaf(i)` giving leaf
/// `i`'s elements (all the same length), in parallel and in lockstep
/// batches.
pub(crate) fn leaf_hashes_elements(count: usize, leaf: impl Fn(usize) -> Vec<BabyBear> + Sync) -> Vec<Hash> {
    let groups = crate::parallel::map(count.div_ceil(LANES), |g| {
        let rows: Vec<Vec<BabyBear>> = (0..LANES).map(|l| leaf((g * LANES + l).min(count - 1))).collect();
        let len = rows[0].len();
        if rows.iter().any(|r| r.len() != len) {
            return rows.iter().map(|r| leaf_hash_elements(r)).collect::<Vec<_>>();
        }
        let inputs: [&[BabyBear]; LANES] = std::array::from_fn(|l| &rows[l][..]);
        hash_octets_lanes(DOMAIN_MERKLE_LEAF, 4 * len, inputs).map(digest_to_bytes).to_vec()
    });
    let mut out: Vec<Hash> = groups.into_iter().flatten().collect();
    out.truncate(count);
    out
}

/// One level of internal nodes over `prev`, in lockstep batches.
fn hash_level(level: u32, prev: &[Hash]) -> Vec<Hash> {
    let count = prev.len() / 2;
    let groups = crate::parallel::map(count.div_ceil(LANES), |g| {
        let pairs = std::array::from_fn(|l| {
            let i = (g * LANES + l).min(count - 1);
            (digest_from_bytes(&prev[2 * i]), digest_from_bytes(&prev[2 * i + 1]))
        });
        hash_pair_lanes(DOMAIN_MERKLE_NODE + level, pairs).map(digest_to_bytes)
    });
    let mut out: Vec<Hash> = groups.into_iter().flatten().collect();
    out.truncate(count);
    out
}

/// `node_hash(level, left, right)`: the two child digests, one
/// permutation, under a domain per `level` -- the level of the *parent*
/// (leaves are level 0), the same separation-by-level convention used in
/// `pmmr`/`bitmap`.
fn node_hash(level: u32, left: Hash, right: Hash) -> Hash {
    digest_to_bytes(hash_pair(DOMAIN_MERKLE_NODE + level, digest_from_bytes(&left), digest_from_bytes(&right)))
}

/// An opening of one index: the claimed leaf there, and enough sibling
/// hashes to recompute the root from just that leaf -- self-contained,
/// needs nothing else from the committed tree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Opening {
    pub index: usize,
    pub leaf: Vec<u8>,
    /// Sibling hashes from level 0 up to one below the root. Length equals
    /// the tree's depth (`log2` of the committed length); zero for a
    /// single-leaf commitment, where the "root" is just that leaf's hash.
    pub siblings: Vec<Hash>,
}

impl Opening {
    /// Verify against a *cap* -- a tree's whole level of `cap.len()` nodes
    /// (a power of two) instead of its single root, as `MerkleTree::cap`
    /// returns -- for a tree of exactly `leaves` leaves. The path stops at
    /// the cap's level, so it's that many hashes shorter.
    pub fn verify_cap(&self, cap: &[Hash], leaves: usize) -> bool {
        if !cap.len().is_power_of_two() || !leaves.is_power_of_two() || cap.len() > leaves {
            return false;
        }
        let path = (leaves / cap.len()).trailing_zeros() as usize;
        if self.siblings.len() != path || self.index >= leaves {
            return false;
        }
        let mut index = self.index;
        let mut hash = leaf_hash(&self.leaf);
        for (level, &sibling) in (1..=path as u32).zip(self.siblings.iter()) {
            hash = if index & 1 == 0 {
                node_hash(level, hash, sibling)
            } else {
                node_hash(level, sibling, hash)
            };
            index /= 2;
        }
        cap[index] == hash
    }

    pub fn verify(&self, root: Hash) -> bool {
        // An index too large for the path's depth would otherwise have its
        // high bits silently ignored, letting one opening pass for another.
        if self.siblings.len() < usize::BITS as usize && self.index >> self.siblings.len() != 0 {
            return false;
        }
        let mut index = self.index;
        let mut hash = leaf_hash(&self.leaf);
        for (level, &sibling) in (1..=self.siblings.len() as u32).zip(self.siblings.iter()) {
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

/// A committed vector of leaves: a complete binary Merkle tree.
pub struct MerkleTree {
    /// The leaves themselves -- or `None` for a tree built from leaf
    /// hashes alone, whose openings get their leaf from the caller.
    leaves: Option<Vec<Vec<u8>>>,
    /// `levels[0]` = leaf hashes, `levels[k]` = level-`k` internal nodes,
    /// `levels.last()` = a single-element vector holding the root.
    levels: Vec<Vec<Hash>>,
}

impl MerkleTree {
    /// Commit to `leaves`. Panics if there are none or their count isn't
    /// a power of two -- both are programmer errors for how this is meant
    /// to be used; FRI and STARK traces always work over power-of-two
    /// domains, so there's no sensible fallback behavior to define.
    pub fn commit(leaves: Vec<Vec<u8>>) -> Self {
        assert!(!leaves.is_empty(), "cannot commit to an empty vector");
        assert!(
            leaves.len().is_power_of_two(),
            "committed length must be a power of two, got {}",
            leaves.len()
        );

        let to_elements = |leaf: &[u8]| -> Vec<BabyBear> {
            leaf.chunks(4)
                .map(|chunk| {
                    let mut padded = [0u8; 4];
                    padded[..chunk.len()].copy_from_slice(chunk);
                    BabyBear::from_bytes(padded)
                })
                .collect()
        };
        // Batched when every leaf is whole elements (all here are);
        // anything else hashes leaf by leaf.
        let hashes = if leaves.iter().all(|l| l.len() % 4 == 0 && l.len() == leaves[0].len()) {
            leaf_hashes_elements(leaves.len(), |i| to_elements(&leaves[i]))
        } else {
            crate::parallel::map(leaves.len(), |i| leaf_hash(&leaves[i]))
        };
        let mut tree = Self::from_leaf_hashes(hashes);
        tree.leaves = Some(leaves);
        tree
    }

    /// A tree from its leaves' hashes only (`leaf_hash` of each) -- for
    /// large commitments whose leaves can be recomputed when opened, so
    /// they needn't be kept.
    pub fn from_leaf_hashes(hashes: Vec<Hash>) -> Self {
        assert!(!hashes.is_empty(), "cannot commit to an empty vector");
        assert!(
            hashes.len().is_power_of_two(),
            "committed length must be a power of two, got {}",
            hashes.len()
        );
        let mut levels = vec![hashes];
        let mut level_num = 1u32;
        while levels.last().unwrap().len() > 1 {
            let prev = levels.last().unwrap();
            let next = hash_level(level_num, prev);
            levels.push(next);
            level_num += 1;
        }

        MerkleTree { leaves: None, levels }
    }

    pub fn root(&self) -> Hash {
        self.levels.last().unwrap()[0]
    }

    pub fn len(&self) -> usize {
        self.levels[0].len()
    }

    /// Leaf `index`, if this tree keeps its leaves.
    pub fn leaf(&self, index: usize) -> Option<&[u8]> {
        self.leaves.as_ref().map(|l| &l[index][..])
    }

    /// The tree's top `2^height` nodes -- or, if it has fewer leaves than
    /// that, all its leaf hashes. Committing to a cap instead of the root
    /// is equally binding, and every opening's path (`open_to_cap`) gets
    /// `height` hashes shorter: worth it when many openings are made.
    pub fn cap(&self, height: usize) -> Vec<Hash> {
        let depth = self.levels.len() - 1;
        self.levels[depth - height.min(depth)].clone()
    }

    /// `open`, with the path stopping at the `cap(height)` level.
    pub fn open_to_cap(&self, index: usize, height: usize) -> Opening {
        let depth = self.levels.len() - 1;
        let mut opening = self.open(index);
        opening.siblings.truncate(depth - height.min(depth));
        opening
    }

    /// Build an opening for `index`.
    pub fn open(&self, index: usize) -> Opening {
        let leaf = self.leaf(index).expect("a hash-only tree opens with `open_leaf`").to_vec();
        self.open_leaf_full(index, leaf)
    }

    /// `open_to_cap` for a hash-only tree: `leaf` is the leaf at `index`
    /// (checked against its hash).
    pub fn open_leaf(&self, index: usize, leaf: Vec<u8>, height: usize) -> Opening {
        let depth = self.levels.len() - 1;
        let mut opening = self.open_leaf_full(index, leaf);
        opening.siblings.truncate(depth - height.min(depth));
        opening
    }

    fn open_leaf_full(&self, index: usize, leaf: Vec<u8>) -> Opening {
        assert!(index < self.len(), "index out of range");
        assert_eq!(leaf_hash(&leaf), self.levels[0][index], "not the committed leaf");
        let mut siblings = Vec::with_capacity(self.levels.len() - 1);
        let mut idx = index;
        for level in &self.levels[..self.levels.len() - 1] {
            siblings.push(level[idx ^ 1]);
            idx /= 2;
        }
        Opening { index, leaf, siblings }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(x: u32) -> Vec<u8> {
        x.to_le_bytes().to_vec()
    }

    fn leaves(range: std::ops::Range<u32>) -> Vec<Vec<u8>> {
        range.map(leaf).collect()
    }

    #[test]
    fn single_leaf_root_is_just_the_leaf_hash() {
        let tree = MerkleTree::commit(vec![leaf(42)]);
        assert_eq!(tree.root(), leaf_hash(&leaf(42)));
    }

    #[test]
    fn single_leaf_opening_verifies_with_no_siblings() {
        let tree = MerkleTree::commit(vec![leaf(42)]);
        let opening = tree.open(0);
        assert!(opening.siblings.is_empty());
        assert!(opening.verify(tree.root()));
    }

    #[test]
    fn every_index_opens_and_verifies() {
        let values = leaves(0..8);
        let tree = MerkleTree::commit(values.clone());
        let root = tree.root();
        for (i, value) in values.iter().enumerate() {
            let opening = tree.open(i);
            assert_eq!(&opening.leaf, value);
            assert!(opening.verify(root));
        }
    }

    #[test]
    fn leaves_of_any_length_work() {
        let rows: Vec<Vec<u8>> = (0..4u8).map(|i| vec![i; 100]).collect();
        let tree = MerkleTree::commit(rows);
        assert!(tree.open(3).verify(tree.root()));
    }

    #[test]
    fn tampered_leaf_rejected() {
        let tree = MerkleTree::commit(leaves(0..4));
        let mut opening = tree.open(1);
        opening.leaf = leaf(999);
        assert!(!opening.verify(tree.root()));
    }

    #[test]
    fn tampered_sibling_rejected() {
        let tree = MerkleTree::commit(leaves(0..4));
        let mut opening = tree.open(1);
        opening.siblings[0][0] ^= 1;
        assert!(!opening.verify(tree.root()));
    }

    #[test]
    fn an_index_beyond_the_path_depth_is_rejected() {
        let tree = MerkleTree::commit(leaves(0..4));
        let mut opening = tree.open(1);
        opening.index = 1 + 4; // same low bits, one bit too many
        assert!(!opening.verify(tree.root()));
    }

    #[test]
    fn wrong_root_rejected() {
        let tree_a = MerkleTree::commit(leaves(0..4));
        let tree_b = MerkleTree::commit(leaves(10..14));
        assert!(!tree_a.open(0).verify(tree_b.root()));
    }

    #[test]
    fn order_of_leaves_affects_the_root() {
        let a = MerkleTree::commit(vec![leaf(1), leaf(2)]);
        let b = MerkleTree::commit(vec![leaf(2), leaf(1)]);
        assert_ne!(a.root(), b.root());
    }

    #[test]
    #[should_panic]
    fn non_power_of_two_length_panics() {
        MerkleTree::commit(leaves(1..4));
    }

    #[test]
    #[should_panic]
    fn empty_commit_panics() {
        MerkleTree::commit(vec![]);
    }

    /// The core tree-building arithmetic, hand-traced independently for 4
    /// leaves rather than trusting the module's own internal consistency:
    /// h0,h1,h2,h3 = leaf hashes; p0 = node_hash(1, h0, h1), p1 =
    /// node_hash(1, h2, h3); root = node_hash(2, p0, p1).
    #[test]
    fn four_leaf_root_matches_hand_traced_value() {
        let values = leaves(0..4);
        let tree = MerkleTree::commit(values.clone());

        let h: Vec<Hash> = values.iter().map(|x| leaf_hash(x)).collect();
        let p0 = node_hash(1, h[0], h[1]);
        let p1 = node_hash(1, h[2], h[3]);
        let expected_root = node_hash(2, p0, p1);

        assert_eq!(tree.root(), expected_root);

        // Index 2 (binary 10): level-0 sibling is index 3 (h[3]); after
        // moving up, the new index is 1, whose level-1 sibling is index 0
        // (p0).
        let opening = tree.open(2);
        assert_eq!(opening.siblings, vec![h[3], p0]);
        assert!(opening.verify(tree.root()));
    }

    #[test]
    fn capped_openings_verify_against_the_cap_and_are_shorter() {
        let tree = MerkleTree::commit(leaves(0..64));
        let cap = tree.cap(3);
        assert_eq!(cap.len(), 8);
        for i in [0, 5, 63] {
            let opening = tree.open_to_cap(i, 3);
            assert_eq!(opening.siblings.len(), 3);
            assert!(opening.verify_cap(&cap, 64));
        }
        // A cap taller than the tree is just its leaf hashes.
        let small = MerkleTree::commit(leaves(0..4));
        assert_eq!(small.cap(5).len(), 4);
        assert!(small.open_to_cap(2, 5).verify_cap(&small.cap(5), 4));
    }

    #[test]
    fn capped_openings_reject_tampering_and_wrong_shapes() {
        let tree = MerkleTree::commit(leaves(0..64));
        let cap = tree.cap(3);
        let good = tree.open_to_cap(9, 3);

        let mut tampered = good.clone();
        tampered.leaf = leaf(999);
        assert!(!tampered.verify_cap(&cap, 64));
        let mut index = good.clone();
        index.index = 10;
        assert!(!index.verify_cap(&cap, 64));
        let mut beyond = good.clone();
        beyond.index = 9 + 64;
        assert!(!beyond.verify_cap(&cap, 64));
        // The wrong tree size, or a full-length path, doesn't pass either.
        assert!(!good.verify_cap(&cap, 128));
        assert!(!tree.open(9).verify_cap(&cap, 64));
        let mut other_cap = cap.clone();
        other_cap[1][0] ^= 1;
        assert!(!good.verify_cap(&other_cap, 64));
    }
}
