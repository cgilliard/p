//! A vector commitment: commit to a power-of-two-length sequence of field
//! elements via a standard binary Merkle tree, and open/verify individual
//! indices against the root.
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

use crate::poseidon2::{BabyBear, hash_bytes_32};

pub type Hash = [u8; 32];

fn leaf_hash(value: BabyBear) -> Hash {
    hash_bytes_32(&value.to_bytes())
}

/// `node_hash(level, left, right) = Poseidon2(level_bytes || left || right)`.
/// `level` is the level of the *parent* produced by combining `left` and
/// `right` (leaves are level 0) -- domain separation between levels, same
/// convention used in `pmmr`/`bitmap`.
fn node_hash(level: u32, left: Hash, right: Hash) -> Hash {
    let mut bytes = Vec::with_capacity(4 + 32 + 32);
    bytes.extend_from_slice(&level.to_le_bytes());
    bytes.extend_from_slice(&left);
    bytes.extend_from_slice(&right);
    hash_bytes_32(&bytes)
}

/// An opening of one index: the claimed value there, and enough sibling
/// hashes to recompute the root from just that value -- self-contained,
/// needs nothing else from the committed tree.
#[derive(Clone, Debug)]
pub struct Opening {
    pub index: usize,
    pub value: BabyBear,
    /// Sibling hashes from level 0 up to one below the root. Length equals
    /// the tree's depth (`log2` of the committed length); zero for a
    /// single-element commitment, where the "root" is just that one leaf's
    /// hash.
    pub siblings: Vec<Hash>,
}

impl Opening {
    pub fn verify(&self, root: Hash) -> bool {
        let mut index = self.index;
        let mut hash = leaf_hash(self.value);
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

/// A committed vector of field elements: a complete binary Merkle tree over
/// `values.len()` leaves.
pub struct MerkleTree {
    values: Vec<BabyBear>,
    /// `levels[0]` = leaf hashes, `levels[k]` = level-`k` internal nodes,
    /// `levels.last()` = a single-element vector holding the root.
    levels: Vec<Vec<Hash>>,
}

impl MerkleTree {
    /// Commit to `values`. Panics if `values` is empty or its length isn't
    /// a power of two -- both are programmer errors for how this is meant
    /// to be used; FRI always works over power-of-two domains, so there's
    /// no sensible fallback behavior to define instead.
    pub fn commit(values: &[BabyBear]) -> Self {
        assert!(!values.is_empty(), "cannot commit to an empty vector");
        assert!(
            values.len().is_power_of_two(),
            "committed length must be a power of two, got {}",
            values.len()
        );

        let mut levels = vec![values.iter().map(|&v| leaf_hash(v)).collect::<Vec<_>>()];

        let mut level_num = 1u32;
        while levels.last().unwrap().len() > 1 {
            let prev = levels.last().unwrap();
            let next = prev
                .chunks_exact(2)
                .map(|pair| node_hash(level_num, pair[0], pair[1]))
                .collect::<Vec<_>>();
            levels.push(next);
            level_num += 1;
        }

        MerkleTree {
            values: values.to_vec(),
            levels,
        }
    }

    pub fn root(&self) -> Hash {
        self.levels.last().unwrap()[0]
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Build an opening for `index`.
    pub fn open(&self, index: usize) -> Opening {
        assert!(index < self.values.len(), "index out of range");
        let mut siblings = Vec::with_capacity(self.levels.len() - 1);
        let mut idx = index;
        for level in &self.levels[..self.levels.len() - 1] {
            siblings.push(level[idx ^ 1]);
            idx /= 2;
        }
        Opening {
            index,
            value: self.values[index],
            siblings,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(x: u32) -> BabyBear {
        BabyBear::new(x)
    }

    #[test]
    fn single_leaf_root_is_just_the_leaf_hash() {
        let tree = MerkleTree::commit(&[v(42)]);
        assert_eq!(tree.root(), leaf_hash(v(42)));
    }

    #[test]
    fn single_leaf_opening_verifies_with_no_siblings() {
        let tree = MerkleTree::commit(&[v(42)]);
        let opening = tree.open(0);
        assert!(opening.siblings.is_empty());
        assert!(opening.verify(tree.root()));
    }

    #[test]
    fn every_index_opens_and_verifies() {
        let values: Vec<BabyBear> = (0..8).map(v).collect();
        let tree = MerkleTree::commit(&values);
        let root = tree.root();
        for i in 0..8 {
            let opening = tree.open(i);
            assert_eq!(opening.value, values[i]);
            assert!(opening.verify(root));
        }
    }

    #[test]
    fn tampered_value_rejected() {
        let values: Vec<BabyBear> = (0..4).map(v).collect();
        let tree = MerkleTree::commit(&values);
        let mut opening = tree.open(1);
        opening.value = v(999);
        assert!(!opening.verify(tree.root()));
    }

    #[test]
    fn tampered_sibling_rejected() {
        let values: Vec<BabyBear> = (0..4).map(v).collect();
        let tree = MerkleTree::commit(&values);
        let mut opening = tree.open(1);
        opening.siblings[0][0] ^= 1;
        assert!(!opening.verify(tree.root()));
    }

    #[test]
    fn wrong_root_rejected() {
        let a: Vec<BabyBear> = (0..4).map(v).collect();
        let b: Vec<BabyBear> = (10..14).map(v).collect();
        let tree_a = MerkleTree::commit(&a);
        let tree_b = MerkleTree::commit(&b);
        let opening = tree_a.open(0);
        assert!(!opening.verify(tree_b.root()));
    }

    #[test]
    fn order_of_values_affects_the_root() {
        let a = MerkleTree::commit(&[v(1), v(2)]);
        let b = MerkleTree::commit(&[v(2), v(1)]);
        assert_ne!(a.root(), b.root());
    }

    #[test]
    #[should_panic]
    fn non_power_of_two_length_panics() {
        MerkleTree::commit(&[v(1), v(2), v(3)]);
    }

    #[test]
    #[should_panic]
    fn empty_commit_panics() {
        MerkleTree::commit(&[]);
    }

    /// The core tree-building arithmetic, hand-traced independently for 4
    /// leaves rather than trusting the module's own internal consistency:
    /// h0,h1,h2,h3 = leaf hashes; p0 = node_hash(1, h0, h1), p1 =
    /// node_hash(1, h2, h3); root = node_hash(2, p0, p1).
    #[test]
    fn four_leaf_root_matches_hand_traced_value() {
        let values: Vec<BabyBear> = (0..4).map(v).collect();
        let tree = MerkleTree::commit(&values);

        let h: Vec<Hash> = values.iter().map(|&x| leaf_hash(x)).collect();
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
}
