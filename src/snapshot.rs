//! Fast sync's state download (`docs/CHAIN_RECURSION.md`, 5d): the state
//! tree as of a sync point, fetched as pieces any peer can serve and the
//! syncing node checks one by one.
//!
//! A *piece* is a subtree, named `(level, index)`, whose hash the syncing
//! node already knows -- from the state root (attested by the chain proof)
//! for the first, from its parent piece for the rest:
//!
//! - an inner piece (level above `LEAF_LEVEL`) is the hashes of its
//!   descendants `FANOUT_BITS` levels down (or down to `LEAF_LEVEL`);
//!   they must hash up to the piece's own hash. Each descendant that's
//!   neither all-`EMPTY` nor all-`SPENT` is a piece to fetch next.
//! - a leaf piece (`LEAF_LEVEL`, 4096 positions) is the subtree's unspent
//!   outputs; with the attested output count -- every other position
//!   below it spent, every one from it on empty -- they must hash to the
//!   piece's hash.
//!
//! So a bad piece is caught on arrival and blamed on whoever sent it, any
//! number of peers can serve pieces in parallel, and fully spent history
//! is never downloaded at all. The pieces are the levels 40, 32, 24, 16, 12:
//! inner pieces up to 256 hashes (8 KB), leaf pieces up to 4096 outputs
//! (~200 KB; most far fewer).

use crate::poseidon2::{BabyBear, digest_from_bytes, digest_to_bytes};
use crate::recovery::NONCE_LEN;
use crate::state_tree::{self, DEPTH, Entry};

type Octet = [BabyBear; 8];

/// The level of leaf pieces: 2^12 positions each.
pub const LEAF_LEVEL: usize = 12;
/// How many levels one inner piece spans.
pub const FANOUT_BITS: usize = 8;
/// A leaf piece's entry: offset in the subtree (u16), commitment, nonce,
/// creation height (u32).
const ENTRY_LEN: usize = 2 + 32 + NONCE_LEN + 4;
/// The largest a piece can be: a leaf piece of nothing but unspent outputs.
pub const MAX_PIECE_BYTES: usize = (1 << LEAF_LEVEL) * ENTRY_LEN;

/// What a fast-syncing node needs about its sync point besides the
/// block itself -- what the chain proof of it attests, along with the
/// header: the target and retarget window start after it, and the
/// cumulative work up to it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SyncPoint {
    pub target: [u8; 32],
    pub anchor_timestamp: u64,
    pub work: [u8; 32],
}

/// The level a piece at `level` reaches down to.
pub fn child_level(level: usize) -> usize {
    level.saturating_sub(FANOUT_BITS).max(LEAF_LEVEL)
}

/// Whether `(level, index)` names a piece.
pub fn is_piece(level: usize, index: u64) -> bool {
    let mut l = DEPTH;
    loop {
        if l == level {
            return index < 1 << (DEPTH - level);
        }
        if l == LEAF_LEVEL {
            return false;
        }
        l = child_level(l);
    }
}

/// An inner piece's bytes: its descendants' hashes, in order.
pub fn encode_inner(children: &[Octet]) -> Vec<u8> {
    children.iter().flat_map(|c| digest_to_bytes(*c)).collect()
}

/// A leaf piece's bytes: the unspent outputs of subtree `index`, in order.
pub fn encode_leaves(index: u64, entries: &[Entry]) -> Vec<u8> {
    let base = index << LEAF_LEVEL;
    let mut out = Vec::with_capacity(entries.len() * ENTRY_LEN);
    for (position, commitment, nonce, height) in entries {
        out.extend_from_slice(&((position - base) as u16).to_be_bytes());
        out.extend_from_slice(commitment);
        out.extend_from_slice(nonce);
        out.extend_from_slice(&height.to_be_bytes());
    }
    out
}

/// A piece to fetch: which subtree, and the hash it must have.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Piece {
    pub level: usize,
    pub index: u64,
    pub hash: [u8; 32],
}

/// The state download for one sync point: what's left to fetch, and the
/// unspent outputs found so far.
pub struct Plan {
    count: u64,
    empty: Vec<Octet>,
    spent: Vec<Octet>,
    pending: Vec<Piece>,
    entries: Vec<Entry>,
}

impl Plan {
    /// For a tree with root `root` holding `count` outputs.
    pub fn new(root: [u8; 32], count: u64) -> Plan {
        let mut plan = Plan {
            count,
            empty: state_tree::empty_hashes(),
            spent: state_tree::spent_hashes(),
            pending: Vec::new(),
            entries: Vec::new(),
        };
        plan.want(DEPTH, 0, digest_from_bytes(&root));
        plan
    }

    /// Fetch `(level, index)` unless its hash says there's nothing in it.
    fn want(&mut self, level: usize, index: u64, hash: Octet) {
        if hash != self.empty[level] && hash != self.spent[level] {
            self.pending.push(Piece {
                level,
                index,
                hash: digest_to_bytes(hash),
            });
        }
    }

    /// The next piece to fetch, if any is left (each is handed out once;
    /// `retry` one that failed).
    pub fn next(&mut self) -> Option<Piece> {
        self.pending.pop()
    }

    /// Put back a piece whose fetch failed.
    pub fn retry(&mut self, piece: Piece) {
        self.pending.push(piece);
    }

    /// Check `bytes` as `piece`, and take what it holds: false (nothing
    /// taken) if it isn't exactly that subtree.
    pub fn accept(&mut self, piece: &Piece, bytes: &[u8]) -> bool {
        let hash = digest_from_bytes(&piece.hash);
        if piece.level == LEAF_LEVEL {
            let Some(entries) = self.decode_leaves(piece.index, bytes) else {
                return false;
            };
            if state_tree::subtree_hash(LEAF_LEVEL, piece.index, self.count, &entries, &self.empty, &self.spent) != hash {
                return false;
            }
            self.entries.extend(entries);
            return true;
        }
        let below = child_level(piece.level);
        let n = 1usize << (piece.level - below);
        if bytes.len() != n * 32 {
            return false;
        }
        let children: Vec<Octet> = bytes.chunks_exact(32).map(|c| digest_from_bytes(c.try_into().unwrap())).collect();
        let mut layer = children.clone();
        for level in below..piece.level {
            layer = layer.chunks_exact(2).map(|p| state_tree::node(level, &p[0], &p[1])).collect();
        }
        if layer[0] != hash {
            return false;
        }
        for (j, child) in children.into_iter().enumerate() {
            self.want(below, (piece.index << (piece.level - below)) + j as u64, child);
        }
        true
    }

    fn decode_leaves(&self, index: u64, bytes: &[u8]) -> Option<Vec<Entry>> {
        if !bytes.len().is_multiple_of(ENTRY_LEN) {
            return None;
        }
        let base = index << LEAF_LEVEL;
        let mut entries: Vec<Entry> = Vec::with_capacity(bytes.len() / ENTRY_LEN);
        for e in bytes.chunks_exact(ENTRY_LEN) {
            let offset = u16::from_be_bytes([e[0], e[1]]) as u64;
            let position = base + offset;
            let in_order = entries.last().is_none_or(|last| last.0 < position);
            if offset >= 1 << LEAF_LEVEL || position >= self.count || !in_order {
                return None;
            }
            let height = u32::from_be_bytes(e[34 + NONCE_LEN..].try_into().unwrap());
            entries.push((position, e[2..34].try_into().unwrap(), e[34..34 + NONCE_LEN].try_into().unwrap(), height));
        }
        Some(entries)
    }

    /// The whole unspent set, in position order, once nothing is left to
    /// fetch (`next` is `None` and nothing is out).
    pub fn finish(mut self) -> Vec<Entry> {
        self.entries.sort_unstable_by_key(|e| e.0);
        self.entries
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poseidon2::hash_bytes_32;

    fn entry(p: u64) -> Entry {
        let h = hash_bytes_32(&p.to_le_bytes());
        (p, h, h[..16].try_into().unwrap(), (p % 5_000) as u32)
    }

    /// Serve every piece of a tree from its full contents.
    fn serve(count: u64, unspent: &[Entry], piece: &Piece) -> Vec<u8> {
        let (empty, spent) = (state_tree::empty_hashes(), state_tree::spent_hashes());
        let in_range = |level: usize, index: u64| -> Vec<Entry> {
            unspent.iter().filter(|e| e.0 >> level == index).copied().collect()
        };
        if piece.level == LEAF_LEVEL {
            return encode_leaves(piece.index, &in_range(LEAF_LEVEL, piece.index));
        }
        let below = child_level(piece.level);
        let children: Vec<Octet> = (0..1u64 << (piece.level - below))
            .map(|j| {
                let index = (piece.index << (piece.level - below)) + j;
                state_tree::subtree_hash(below, index, count, &in_range(below, index), &empty, &spent)
            })
            .collect();
        encode_inner(&children)
    }

    #[test]
    fn pieces_are_the_levels_down_to_the_leaves() {
        assert!(is_piece(40, 0) && is_piece(32, 255) && is_piece(24, 65535) && is_piece(16, (1 << 24) - 1) && is_piece(12, (1 << 28) - 1));
        assert!(!is_piece(40, 1) && !is_piece(32, 256) && !is_piece(20, 0) && !is_piece(8, 0) && !is_piece(0, 0));
    }

    /// A tree downloads piece by piece into exactly its unspent outputs,
    /// skipping fully spent subtrees; a tampered piece is refused.
    #[test]
    fn a_tree_downloads_piece_by_piece() {
        // 20,000 outputs, all spent but a scattering -- positions 4096..8192
        // (one leaf piece) entirely spent.
        let count = 20_000;
        let unspent: Vec<Entry> = (0..count).filter(|p| p % 97 == 3 && !(4096..8192).contains(p)).map(entry).collect();
        let (empty, spent) = (state_tree::empty_hashes(), state_tree::spent_hashes());
        let root = digest_to_bytes(state_tree::subtree_hash(DEPTH, 0, count, &unspent, &empty, &spent));
        let mut plan = Plan::new(root, count);
        let mut fetched = Vec::new();
        while let Some(piece) = plan.next() {
            let bytes = serve(count, &unspent, &piece);
            // Tampering: a dropped output, a changed nonce, a wrong hash.
            if piece.level == LEAF_LEVEL && bytes.len() > ENTRY_LEN {
                assert!(!plan.accept(&piece, &bytes[ENTRY_LEN..]));
                let mut changed = bytes.clone();
                changed[40] ^= 1;
                assert!(!plan.accept(&piece, &changed));
            } else if piece.level > LEAF_LEVEL {
                let mut changed = bytes.clone();
                changed[0] ^= 1;
                assert!(!plan.accept(&piece, &changed));
            }
            assert!(plan.accept(&piece, &bytes));
            fetched.push((piece.level, piece.index));
        }
        assert_eq!(plan.finish(), unspent);
        // Root, one level-32, one level-24 and one level-16 piece, and the
        // leaf pieces with something in them -- not the fully spent one.
        let leaves: Vec<u64> = fetched.iter().filter(|f| f.0 == LEAF_LEVEL).map(|f| f.1).collect();
        assert_eq!(fetched.len(), 4 + leaves.len());
        assert!(!leaves.contains(&1) && leaves.contains(&0) && leaves.contains(&4));
        // An empty tree needs nothing.
        assert!(Plan::new(state_tree::empty_root(), 0).next().is_none());
    }
}
