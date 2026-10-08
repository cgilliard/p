//! Multi-use keys (`docs/CONTRACTS.md`, step 3): a Merkle tree of `2^h`
//! one-time WOTS keys whose root is the key's id -- what an output's lock
//! or a policy branch lists in place of a one-time key's hash. Each
//! signature is by one leaf key, which must never sign again; it carries
//! the leaf's index and path (`KeyProof`).
//!
//! A one-time key is the `h = 0` case: its id is its own hash, with an
//! empty path. Nodes are one permutation of their children, the level in
//! the capacity, as the block circuit hashes them.
//!
//! Every leaf is a full key generation (about 480 permutations), so a
//! tree of `2^h` leaves is that many: about 45 s at the default `h = 16`
//! (65,536 signatures), about 12 minutes at the most allowed, `h = 20`.

#![allow(dead_code)]

use crate::circuit::Octet;
use crate::poseidon2::{BabyBear, DOMAIN_KEY_NODE, digest_from_bytes, digest_to_bytes, hash_bytes_32, perm24};
use crate::wots::{self, PublicKey, SecretKey};

/// A tree's height, by default and at most (a validity rule: the circuit
/// needs no cap, but a taller tree takes impractically long to generate).
pub const DEFAULT_HEIGHT: usize = 16;
pub const MAX_HEIGHT: usize = 20;

/// The node above `left` and `right` at `level` (0: just above the leaves).
pub fn node(level: usize, left: &Octet, right: &Octet) -> Octet {
    let mut state = [BabyBear::ZERO; 24];
    state[..8].copy_from_slice(left);
    state[8..16].copy_from_slice(right);
    state[16] = BabyBear::new(DOMAIN_KEY_NODE + level as u32);
    state[17] = BabyBear::new(16);
    perm24().permute(state)[..8].try_into().unwrap()
}

/// The root a leaf reaches at `index` by `path` (siblings, bottom first).
pub fn root_from(leaf: Octet, index: u32, path: &[Octet]) -> Octet {
    path.iter().enumerate().fold(leaf, |hash, (level, sibling)| {
        if (index >> level) & 1 == 0 { node(level, &hash, sibling) } else { node(level, sibling, &hash) }
    })
}

/// Where a signing leaf key sits in its tree: its index and path. Empty
/// for a one-time key.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct KeyProof {
    pub index: u32,
    pub path: Vec<[u8; 32]>,
}

impl KeyProof {
    /// A one-time key's: no tree.
    pub fn one_time() -> Self {
        KeyProof::default()
    }

    /// Within the limits: at most `MAX_HEIGHT` levels, an index in range,
    /// canonical hashes.
    pub fn is_valid(&self) -> bool {
        self.path.len() <= MAX_HEIGHT && (self.index as u64) < 1u64 << self.path.len() && self.path.iter().all(crate::prover::is_canonical)
    }

    /// The id of the key `pk` signs for, at this place: its tree's root.
    pub fn key_id(&self, pk: &PublicKey) -> [u8; 32] {
        let path: Vec<Octet> = self.path.iter().map(digest_from_bytes).collect();
        digest_to_bytes(root_from(pk.hash(), self.index, &path))
    }
}

/// A multi-use key: its leaves' keys follow from a seed, its levels (from
/// the leaves' hashes up) are kept.
pub struct KeyTree {
    seed: [u8; 32],
    levels: Vec<Vec<Octet>>,
}

impl KeyTree {
    /// Generate the tree of `2^height` keys from `seed` (in parallel).
    pub fn generate(seed: &[u8; 32], height: usize) -> Self {
        assert!(height <= MAX_HEIGHT, "a key tree is at most {MAX_HEIGHT} levels");
        let leaves = crate::parallel::map_each(1 << height, |i| leaf_keys(seed, i as u32).1.hash());
        let mut levels = vec![leaves];
        for h in 0..height {
            let next = levels[h].chunks(2).map(|pair| node(h, &pair[0], &pair[1])).collect();
            levels.push(next);
        }
        KeyTree { seed: *seed, levels }
    }

    pub fn height(&self) -> usize {
        self.levels.len() - 1
    }

    /// The key's id: the root.
    pub fn id(&self) -> [u8; 32] {
        digest_to_bytes(self.levels[self.height()][0])
    }

    /// Leaf `index`'s key pair. Sign with each at most once.
    pub fn leaf(&self, index: u32) -> (SecretKey, PublicKey) {
        leaf_keys(&self.seed, index)
    }

    /// Leaf `index`'s place in the tree.
    pub fn proof(&self, index: u32) -> KeyProof {
        let path = (0..self.height()).map(|h| digest_to_bytes(self.levels[h][((index as usize) >> h) ^ 1])).collect();
        KeyProof { index, path }
    }
}

/// Leaf `index`'s keys, derived from the tree's seed.
fn leaf_keys(seed: &[u8; 32], index: u32) -> (SecretKey, PublicKey) {
    wots::keygen(&hash_bytes_32(&[&seed[..], &index.to_le_bytes(), b"key tree leaf"].concat()))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every leaf's key reaches the tree's id by its proof; a one-time key's
    /// id is its own hash; proofs stay within the limits.
    #[test]
    fn every_leaf_reaches_the_id() {
        let tree = KeyTree::generate(&[3; 32], 3);
        for i in 0..8 {
            let (_, pk) = tree.leaf(i);
            let proof = tree.proof(i);
            assert!(proof.is_valid());
            assert_eq!(proof.key_id(&pk), tree.id(), "leaf {i}");
        }
        let (_, pk) = wots::keygen(&[4; 32]);
        assert_eq!(KeyProof::one_time().key_id(&pk), digest_to_bytes(pk.hash()));
        assert!(!KeyProof { index: 8, path: tree.proof(0).path }.is_valid(), "index out of range");
        let tall = KeyProof { index: 0, path: vec![[0; 32]; MAX_HEIGHT + 1] };
        assert!(!tall.is_valid());
        // Another leaf's key at this index's place doesn't reach the id.
        assert_ne!(tree.proof(0).key_id(&tree.leaf(1).1), tree.id());
    }
}
