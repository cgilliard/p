//! Spending policies (`docs/CONTRACTS.md`): an output can be locked to a
//! **policy** instead of a single key. Its lock -- what the output's
//! commitment hashes in place of a key hash -- is then the root of a small
//! Merkle tree of **branches**, each a conjunction of conditions:
//!
//! - `threshold` signatures from distinct keys among `keys` (`1 ≤ threshold
//!   ≤ keys ≤ MAX_KEYS`);
//! - `after_height`: the spending block's height is at least this;
//! - `after_age`: the spending block's height is at least the spent
//!   output's creation height plus this;
//! - `hashlock`: a preimage of this image (`hashlock`);
//! - `rebind`: its signatures are REBIND signatures (over a declared state
//!   and the outputs they name, not the input), and the spending input's
//!   declared state must exceed this one -- what lets an eltoo update
//!   spend any earlier one (`docs/CONTRACTS.md`, step 4).
//!
//! A spend reveals one branch, its path to the root, and what satisfies
//! it. The unused branches stay hidden; on chain a policy output looks like
//! any other.
//!
//! Encodings match the block circuit (`block_air`) exactly: a branch's
//! leaf is a sponge over a 16-element header and its key hashes, two to a
//! block; a node is one permutation of its children with its level in the
//! capacity, like the state tree's (`state_tree::node`).

#![allow(dead_code)]

use crate::circuit::Octet;
use crate::prover::is_canonical;
use crate::poseidon2::{
    BabyBear, DOMAIN_HASHLOCK, DOMAIN_POLICY_LEAF, DOMAIN_POLICY_NODE, digest_from_bytes, digest_to_bytes, hash_elements, perm24,
};

/// Keys in a branch, at most -- and so signatures a branch can need.
pub const MAX_KEYS: usize = 12;
/// A policy tree's depth, at most: up to 256 branches.
pub const MAX_DEPTH: usize = 8;
/// Heights and ages in a branch are below this (as are the chain's
/// heights, for a thousand years and more): the circuit compares them as
/// 30-bit numbers.
pub const MAX_LOCK: u32 = 1 << 30;

/// One way to spend a policy output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Branch {
    /// How many of `keys` must sign.
    pub threshold: u8,
    /// Key hashes (`wots::PublicKey::hash`, as bytes).
    pub keys: Vec<[u8; 32]>,
    /// The spending block's height must be at least this (0: no lock).
    pub after_height: u32,
    /// The spending block's height must be at least the spent output's
    /// creation height plus this (0: no lock).
    pub after_age: u32,
    /// A preimage of this image must be revealed (`hashlock`).
    pub hashlock: Option<[u8; 32]>,
    /// REBIND: the state the spending input must exceed.
    pub rebind: Option<u32>,
}

impl Branch {
    /// Within the limits the circuit and consensus allow.
    pub fn is_valid(&self) -> bool {
        let keys = self.keys.len();
        (1..=MAX_KEYS).contains(&keys)
            && (1..=keys).contains(&(self.threshold as usize))
            && self.after_height < MAX_LOCK
            && self.after_age < MAX_LOCK
            && self.rebind.is_none_or(|s| s < MAX_LOCK)
            && self.keys.iter().all(is_canonical)
            && self.hashlock.as_ref().is_none_or(is_canonical)
    }

    /// The header block: `[threshold, keys, after_height, after_age,
    /// has_hash, rebind, state, 0, hash lock]`.
    pub fn header(&self) -> [BabyBear; 16] {
        let mut h = [BabyBear::ZERO; 16];
        h[0] = BabyBear::new(self.threshold as u32);
        h[1] = BabyBear::new(self.keys.len() as u32);
        h[2] = BabyBear::new(self.after_height);
        h[3] = BabyBear::new(self.after_age);
        if let Some(x) = &self.hashlock {
            h[4] = BabyBear::ONE;
            h[8..].copy_from_slice(&digest_from_bytes(x));
        }
        if let Some(state) = self.rebind {
            h[5] = BabyBear::ONE;
            h[6] = BabyBear::new(state);
        }
        h
    }

    /// What the leaf hashes: the header, then the key hashes.
    pub fn elements(&self) -> Vec<BabyBear> {
        let mut out = self.header().to_vec();
        for key in &self.keys {
            out.extend(digest_from_bytes(key));
        }
        out
    }

    /// The branch's leaf in its policy's tree.
    pub fn leaf(&self) -> Octet {
        hash_elements(DOMAIN_POLICY_LEAF, &self.elements())
    }

    /// Whether the locks hold for a spend in a block at `height` of an
    /// output created at `created`.
    pub fn locks_hold(&self, height: u32, created: u32) -> bool {
        height >= self.after_height && height.checked_sub(created).is_some_and(|age| age >= self.after_age)
    }
}

/// The node above `left` and `right` at `level` (0: just above the leaves).
pub fn node(level: usize, left: &Octet, right: &Octet) -> Octet {
    let mut state = [BabyBear::ZERO; 24];
    state[..8].copy_from_slice(left);
    state[8..16].copy_from_slice(right);
    state[16] = BabyBear::new(DOMAIN_POLICY_NODE + level as u32);
    state[17] = BabyBear::new(16);
    perm24().permute(state)[..8].try_into().unwrap()
}

/// A hash lock's image: `H(DOMAIN_HASHLOCK, preimage)`, the preimage as a
/// digest's 8 elements (`None` unless it's canonical).
pub fn hashlock(preimage: &[u8; 32]) -> Option<[u8; 32]> {
    is_canonical(preimage).then(|| digest_to_bytes(hash_elements(DOMAIN_HASHLOCK, &digest_from_bytes(preimage))))
}

/// The root a branch's leaf reaches at `index` by `path` (its siblings,
/// bottom first): a policy's lock, if the branch is in it.
pub fn root_from(leaf: Octet, index: u32, path: &[Octet]) -> Octet {
    path.iter().enumerate().fold(leaf, |hash, (level, sibling)| {
        if (index >> level) & 1 == 0 { node(level, &hash, sibling) } else { node(level, sibling, &hash) }
    })
}

/// A spending policy: its branches, in order (a branch's index is its
/// position). The tree pads to a power of two with zero leaves; one
/// branch's root is its leaf.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Policy {
    pub branches: Vec<Branch>,
}

impl Policy {
    pub fn is_valid(&self) -> bool {
        (1..=1 << MAX_DEPTH).contains(&self.branches.len()) && self.branches.iter().all(Branch::is_valid)
    }

    fn depth(&self) -> usize {
        self.branches.len().next_power_of_two().trailing_zeros() as usize
    }

    /// Every level of the tree, leaves first.
    fn levels(&self) -> Vec<Vec<Octet>> {
        let mut level: Vec<Octet> = self.branches.iter().map(Branch::leaf).collect();
        level.resize(1 << self.depth(), [BabyBear::ZERO; 8]);
        let mut levels = vec![level];
        for h in 0..self.depth() {
            let below = &levels[h];
            let next = below.chunks(2).map(|pair| node(h, &pair[0], &pair[1])).collect();
            levels.push(next);
        }
        levels
    }

    pub fn root(&self) -> Octet {
        self.levels().last().unwrap()[0]
    }

    /// The lock an output to this policy carries.
    pub fn lock(&self) -> [u8; 32] {
        digest_to_bytes(self.root())
    }

    /// Branch `index`'s path to the root: its siblings, bottom first.
    pub fn path(&self, index: u32) -> Vec<Octet> {
        let levels = self.levels();
        (0..self.depth()).map(|h| levels[h][((index as usize) >> h) ^ 1]).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(k: u8) -> [u8; 32] {
        digest_to_bytes(crate::wots::keygen(&[k; 32]).1.hash())
    }

    fn branch(threshold: u8, keys: &[u8]) -> Branch {
        Branch { threshold, keys: keys.iter().map(|&k| key(k)).collect(), after_height: 0, after_age: 0, hashlock: None, rebind: None }
    }

    /// Every branch's path leads from its leaf to the root, whatever the
    /// count; one branch's root is its leaf; the leaf commits to every
    /// field.
    #[test]
    fn every_branch_reaches_the_root() {
        for count in [1, 2, 3, 5, 8] {
            let policy = Policy { branches: (0..count).map(|i| branch(1, &[i as u8 + 1, 50])).collect() };
            assert!(policy.is_valid());
            for (i, b) in policy.branches.iter().enumerate() {
                assert_eq!(root_from(b.leaf(), i as u32, &policy.path(i as u32)), policy.root(), "{count} branches, branch {i}");
            }
            if count == 1 {
                assert_eq!(policy.root(), policy.branches[0].leaf());
            }
        }
        let base = branch(2, &[1, 2, 3]);
        let variants = [
            Branch { threshold: 3, ..base.clone() },
            Branch { keys: vec![key(1), key(2), key(4)], ..base.clone() },
            Branch { after_height: 1, ..base.clone() },
            Branch { after_age: 1, ..base.clone() },
            Branch { hashlock: hashlock(&key(9)), ..base.clone() },
            Branch { rebind: Some(0), ..base.clone() },
            Branch { rebind: Some(1), ..base.clone() },
        ];
        for v in variants {
            assert_ne!(v.leaf(), base.leaf());
        }
    }

    #[test]
    fn branches_stay_within_the_limits() {
        assert!(!branch(0, &[1]).is_valid(), "someone must sign");
        assert!(!branch(3, &[1, 2]).is_valid());
        assert!(branch(12, &(1..=12).collect::<Vec<_>>()).is_valid());
        assert!(!branch(1, &(1..=13).collect::<Vec<_>>()).is_valid());
        assert!(!Branch { after_height: MAX_LOCK, ..branch(1, &[1]) }.is_valid());
        assert!(!Branch { after_age: MAX_LOCK, ..branch(1, &[1]) }.is_valid());
    }

    #[test]
    fn locks_hold_from_their_heights_on() {
        let b = Branch { after_height: 100, after_age: 10, ..branch(1, &[1]) };
        assert!(b.locks_hold(100, 90));
        assert!(!b.locks_hold(99, 50), "too early");
        assert!(!b.locks_hold(100, 91), "too young");
        assert!(!b.locks_hold(100, 101), "created after the spend");
    }
}
