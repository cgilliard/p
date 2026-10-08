//! Proof of work: a cheap-to-check, expensive-to-produce puzzle a block
//! header's nonce must solve -- **memory-bound** (`docs/BIBLE.md`): an
//! attempt is mostly reading a dataset expanded from the Bible's text, so
//! mining is bound by memory (DRAM, or SRAM on an ASIC -- ASICs are
//! welcome), not by hashing.
//!
//! # The dataset
//!
//! `2^items_log` items of `ITEM_ELEMS` field elements (512 bytes), each
//! computed independently from a block of the text (`scripture`) at a
//! deliberately high cost -- `item_rounds` Poseidon2 permutations -- so
//! recomputing an item costs far more than reading it: **miners** keep the
//! dataset in memory (`Dataset`; 64 MiB on main). **Validators** don't:
//! they recompute only the items a header touches, from the text alone --
//! light enough for very small hardware.
//!
//! # One attempt
//!
//! - **Midstate:** the header (all but the nonce) is hashed once per
//!   template (`prefix`); an attempt is one permutation of prefix ‖ nonce,
//!   whose output is the block's **id** (what `prev_hash` points to) and
//!   the starting **mix** (16 elements).
//! - `lookups` times: an index from the mix (`2^items_log` items), that
//!   item read, and folded into the mix with field arithmetic: every
//!   element times a mix-dependent weight (`acc[e] = Σ_c item[16c+e] ·
//!   mix[(e+c) mod 16]`), then one nonlinear step (`t = acc + mix`,
//!   `mix[e] = t[e]·t[e+1] + K[e]`). Every element of every item read
//!   counts, with weights that change every attempt (so items can't be
//!   precompressed); each index depends on the last read (no prefetching
//!   or skipping); the 128 products are independent (they vectorize, so
//!   memory, not arithmetic, bounds a CPU too); and no hashing per lookup.
//! - The **proof-of-work value**: Poseidon2(id ‖ mix), which must be no
//!   larger than the target (as 256-bit big-endian integers, as in
//!   Bitcoin).
//!
//! An attempt's compute is ~2 permutations and cheap elementwise
//! arithmetic; its memory is `lookups` × 512 bytes. The parameters are
//! consensus (`chain::DifficultyConfig::pow`): `Params::MAIN` and `DEV`
//! for the networks, `TEST` (tiny) for tests.
//!
//! The nonce is a full 32 bytes; `mine` counts a `u64` in its low 8.
#![allow(dead_code)]

use crate::poseidon2::{BabyBear, digest_to_bytes, hash_bytes, hash_octets, perm24};
use crate::scripture;

pub type Nonce = [u8; 32];

/// Field elements per dataset item: 512 bytes.
pub const ITEM_ELEMS: usize = 128;
/// The mix's width, and how many elements are folded in at a time.
pub const MIX: usize = 16;

const DOMAIN_ATTEMPT: u32 = 0x600;
const DOMAIN_ITEM: u32 = 0x601;
const DOMAIN_POW: u32 = 0x602;
/// A dataset item's leaf in the dataset tree.
pub const DOMAIN_ITEM_LEAF: u32 = 0x603;
/// Plus the level: the dataset tree's nodes.
pub const DOMAIN_DATASET_NODE: u32 = 0x700;
/// `attempt`'s domain, as the circuit lays it out.
pub const ATTEMPT_DOMAIN: u32 = DOMAIN_ATTEMPT;
/// The final hash's domain.
pub const POW_DOMAIN: u32 = DOMAIN_POW;

/// The mixing constants `K`.
pub const K: [u32; MIX] = [
    0x0123_4567, 0x0234_5678, 0x0345_6789, 0x0456_789a, 0x0567_89ab, 0x0678_9abc, 0x0789_abcd, 0x089a_bcde,
    0x09ab_cdef, 0x0abc_def0, 0x0bcd_ef01, 0x0cde_f012, 0x0def_0123, 0x0ef0_1234, 0x0f01_2345, 0x1012_3456,
];

/// Proof-of-work parameters -- consensus, per network.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Params {
    /// `log2` of the dataset's item count.
    pub items_log: u32,
    /// Permutations per item: what recomputing one costs.
    pub item_rounds: u32,
    /// Dataset reads per attempt.
    pub lookups: u32,
}

impl Params {
    /// 2^17 items × 512 B = 64 MiB: SRAM-feasible for an ASIC.
    pub const MAIN: Params = Params { items_log: 17, item_rounds: 128, lookups: 64 };
    /// 16 MiB, for quick startup -- and 12 lookups, so the chain step's
    /// proof of work fits dev's smaller (2^17-row) recursion.
    pub const DEV: Params = Params { items_log: 15, item_rounds: 128, lookups: 12 };
    /// Tiny, for tests that mine many blocks.
    pub const TEST: Params = Params { items_log: 6, item_rounds: 2, lookups: 4 };

    pub fn items(&self) -> usize {
        1 << self.items_log
    }
}

fn nonce_from_counter(counter: u64) -> Nonce {
    let mut nonce = [0u8; 32];
    nonce[..8].copy_from_slice(&counter.to_le_bytes());
    nonce
}

/// A header's prefix: everything but its nonce, hashed -- once per
/// template.
pub fn prefix(header_bytes: &[u8]) -> [BabyBear; 8] {
    hash_bytes(header_bytes)
}

/// The nonce as field elements, three bytes to an element.
fn nonce_elements(nonce: &Nonce) -> [BabyBear; 11] {
    std::array::from_fn(|e| {
        let chunk = &nonce[3 * e..(3 * e + 3).min(32)];
        BabyBear::new(chunk.iter().rev().fold(0u32, |acc, &b| (acc << 8) | b as u32))
    })
}

/// One permutation of prefix ‖ nonce: the block's id (`[..8]`) and the
/// starting mix (`[8..]`).
pub fn attempt(prefix: &[BabyBear; 8], nonce: &Nonce) -> [BabyBear; 24] {
    let mut state = [BabyBear::ZERO; 24];
    state[..8].copy_from_slice(prefix);
    state[8..19].copy_from_slice(&nonce_elements(nonce));
    state[19] = BabyBear::new(DOMAIN_ATTEMPT);
    perm24().permute(state)
}

/// The block id: what the header hashes to.
pub fn header_id(header_bytes: &[u8], nonce: Nonce) -> [u8; 32] {
    let out = attempt(&prefix(header_bytes), &nonce);
    digest_to_bytes(out[..8].try_into().unwrap())
}

/// Dataset item `i`, computed: a block of the text and `i`, through
/// `item_rounds` permutations, then squeezed out to `ITEM_ELEMS` elements.
pub fn item(params: &Params, i: usize) -> [BabyBear; ITEM_ELEMS] {
    let perm = perm24();
    let mut state = [BabyBear::ZERO; 24];
    state[..scripture::BLOCK_ELEMENTS].copy_from_slice(&scripture::block_elements(i % scripture::BLOCKS));
    state[11] = BabyBear::new((i & 0xff_ffff) as u32);
    state[12] = BabyBear::new((i >> 24) as u32);
    state[16] = BabyBear::new(DOMAIN_ITEM);
    state[17] = BabyBear::new(params.item_rounds);
    for _ in 0..params.item_rounds {
        state = perm.permute(state);
    }
    let mut out = [BabyBear::ZERO; ITEM_ELEMS];
    for (k, chunk) in out.chunks_exact_mut(16).enumerate() {
        if k > 0 {
            state = perm.permute(state);
        }
        chunk.copy_from_slice(&state[..16]);
    }
    out
}

/// The whole dataset, in memory: what a miner reads -- items as raw
/// (reduced) `u32`s, for `fast`.
pub struct Dataset {
    pub params: Params,
    elements: Vec<u32>,
}

impl Dataset {
    /// Compute every item, across every core.
    pub fn generate(params: Params) -> Dataset {
        let items = crate::parallel::map(params.items(), |i| item(&params, i));
        Dataset {
            params,
            elements: items.into_iter().flatten().map(|e| e.value()).collect(),
        }
    }

    pub fn item(&self, i: usize) -> &[u32] {
        &self.elements[i * ITEM_ELEMS..(i + 1) * ITEM_ELEMS]
    }
}

/// The miner's fast path: the same mixing as `fold`, on raw `u32` lanes
/// with Montgomery multiplication -- no division, so it vectorizes (and
/// is compiled for AVX2 when the CPU has it). Consensus is `fold`; this
/// must agree with it exactly (`the_fast_path_matches_the_reference`).
mod fast {
    use super::{ITEM_ELEMS, K, MIX};
    use crate::poseidon2::P;

    /// 2^64 mod p: Montgomery form is `x·2^32`, reached by multiplying by
    /// this and reducing.
    const R2: u64 = 1_172_168_163;
    /// -p^-1 mod 2^32.
    const P_INV_NEG: u32 = 0x77ffffff;

    /// `x · 2^-32 mod p`, for `x < p · 2^32`.
    #[inline(always)]
    fn reduce(x: u64) -> u32 {
        let q = (x as u32).wrapping_mul(P_INV_NEG);
        let t = ((x + q as u64 * P as u64) >> 32) as u32;
        if t >= P { t - P } else { t }
    }

    #[inline(always)]
    fn add(a: u32, b: u32) -> u32 {
        let s = a + b;
        if s >= P { s - P } else { s }
    }

    /// `a` in Montgomery form, so that `reduce(b · mont(a)) = a·b`.
    #[inline(always)]
    fn mont(a: u32) -> u32 {
        reduce(a as u64 * R2)
    }

    #[inline(always)]
    fn fold_lanes(mix: &mut [u32; MIX], item: &[u32]) {
        let item: &[u32; ITEM_ELEMS] = item.try_into().unwrap();
        // The weights, laid out like the item: weight[16c + e] =
        // mix[(e + c) % 16], in Montgomery form -- so the 128 products are
        // one straight loop.
        let m: [u32; MIX] = std::array::from_fn(|e| mont(mix[e]));
        let mut weights = [0u32; ITEM_ELEMS];
        for c in 0..ITEM_ELEMS / MIX {
            for e in 0..MIX {
                weights[MIX * c + e] = m[(e + c) % MIX];
            }
        }
        let mut products = [0u32; ITEM_ELEMS];
        for k in 0..ITEM_ELEMS {
            products[k] = reduce(item[k] as u64 * weights[k] as u64);
        }
        let mut acc = [0u32; MIX];
        for c in 0..ITEM_ELEMS / MIX {
            for e in 0..MIX {
                acc[e] = add(acc[e], products[MIX * c + e]);
            }
        }
        let mut t = [0u32; MIX];
        for e in 0..MIX {
            t[e] = add(acc[e], mix[e]);
        }
        let tm: [u32; MIX] = std::array::from_fn(|e| mont(t[(e + 1) % MIX]));
        for e in 0..MIX {
            mix[e] = add(reduce(t[e] as u64 * tm[e] as u64), K[e]);
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "avx2")]
    unsafe fn fold_avx2(mix: &mut [u32; MIX], item: &[u32]) {
        fold_lanes(mix, item)
    }

    /// `super::fold`, fast.
    pub fn fold(mix: &mut [u32; MIX], item: &[u32]) {
        debug_assert_eq!(item.len(), ITEM_ELEMS);
        #[cfg(target_arch = "x86_64")]
        if std::arch::is_x86_feature_detected!("avx2") {
            // SAFETY: the CPU has AVX2.
            return unsafe { fold_avx2(mix, item) };
        }
        fold_lanes(mix, item)
    }

    /// `super::index_of`, on raw lanes.
    pub fn index_of(items_log: u32, mix: &[u32; MIX]) -> usize {
        let sum = mix.iter().fold(0u64, |a, &b| a + b as u64) % P as u64;
        sum as usize & ((1 << items_log) - 1)
    }
}

/// The dataset for `params`, generated on first use and kept. Each
/// parameter set generates on its own: one being generated doesn't hold
/// up another.
pub fn dataset(params: Params) -> std::sync::Arc<Dataset> {
    use std::sync::{Arc, Mutex, OnceLock};
    type Slot = Arc<OnceLock<Arc<Dataset>>>;
    static DATASETS: OnceLock<Mutex<Vec<(Params, Slot)>>> = OnceLock::new();
    let slot = {
        let mut datasets = DATASETS.get_or_init(Default::default).lock().unwrap();
        match datasets.iter().find(|(p, _)| *p == params) {
            Some((_, slot)) => slot.clone(),
            None => {
                let slot: Slot = Default::default();
                datasets.push((params, slot.clone()));
                slot
            }
        }
    };
    slot.get_or_init(|| Arc::new(Dataset::generate(params))).clone()
}

/// An item's leaf in the dataset tree: one sponge over its 128 elements.
pub fn item_leaf(item: &[BabyBear]) -> [BabyBear; 8] {
    hash_octets(DOMAIN_ITEM_LEAF, ITEM_ELEMS * 4, item)
}

/// The dataset tree's node capacity at `level` (0: just above leaves).
pub fn node_capacity(level: usize) -> [BabyBear; 8] {
    let mut c = [BabyBear::ZERO; 8];
    c[0] = BabyBear::new(DOMAIN_DATASET_NODE + level as u32);
    c[1] = BabyBear::new(16);
    c
}

/// The dataset tree's node above `left` and `right` at `level`.
pub fn node(level: usize, left: &[BabyBear; 8], right: &[BabyBear; 8]) -> [BabyBear; 8] {
    let mut state = [BabyBear::ZERO; 24];
    state[..8].copy_from_slice(left);
    state[8..16].copy_from_slice(right);
    state[16..].copy_from_slice(&node_capacity(level));
    perm24().permute(state)[..8].try_into().unwrap()
}

/// A Merkle tree over the dataset's items: what a chain step proves its
/// header's lookups against (its root is built into the step's key). Kept
/// by provers -- miners -- alongside the dataset: 2^(items_log + 1)
/// digests (8 MB on main).
pub struct DatasetTree {
    levels: Vec<Vec<[BabyBear; 8]>>,
}

impl DatasetTree {
    pub fn build(data: &Dataset) -> DatasetTree {
        let leaves = crate::parallel::map(data.params.items(), |i| {
            let item: Vec<BabyBear> = data.item(i).iter().map(|&v| BabyBear::new(v)).collect();
            item_leaf(&item)
        });
        let mut levels = vec![leaves];
        for h in 0..data.params.items_log as usize {
            let next = levels[h].chunks_exact(2).map(|p| node(h, &p[0], &p[1])).collect();
            levels.push(next);
        }
        DatasetTree { levels }
    }

    pub fn root(&self) -> [BabyBear; 8] {
        self.levels.last().unwrap()[0]
    }

    /// Item `i`'s siblings, bottom first.
    pub fn path(&self, i: usize) -> Vec<[BabyBear; 8]> {
        (0..self.levels.len() - 1).map(|h| self.levels[h][(i >> h) ^ 1]).collect()
    }
}

/// The dataset tree for `params`, built on first use and kept.
pub fn dataset_tree(params: Params) -> std::sync::Arc<DatasetTree> {
    use std::sync::{Arc, Mutex, OnceLock};
    type Slot = Arc<OnceLock<Arc<DatasetTree>>>;
    static TREES: OnceLock<Mutex<Vec<(Params, Slot)>>> = OnceLock::new();
    let slot = {
        let mut trees = TREES.get_or_init(Default::default).lock().unwrap();
        match trees.iter().find(|(p, _)| *p == params) {
            Some((_, slot)) => slot.clone(),
            None => {
                let slot: Slot = Default::default();
                trees.push((params, slot.clone()));
                slot
            }
        }
    };
    slot.get_or_init(|| Arc::new(DatasetTree::build(&dataset(params)))).clone()
}

/// The items an attempt reads, in order (index, item) -- a chain step's
/// witness for its header's proof of work.
pub fn lookups(params: &Params, out: &[BabyBear; 24]) -> Vec<(usize, Vec<BabyBear>)> {
    let data = dataset(*params);
    let mut mix: [BabyBear; MIX] = out[8..].try_into().unwrap();
    let mut read = Vec::with_capacity(params.lookups as usize);
    for _ in 0..params.lookups {
        let i = index_of(params, &mix);
        let item: Vec<BabyBear> = data.item(i).iter().map(|&v| BabyBear::new(v)).collect();
        fold(&mut mix, &item);
        read.push((i, item));
    }
    read
}

/// The index the mix picks.
pub fn index_of(params: &Params, mix: &[BabyBear; MIX]) -> usize {
    let sum = mix.iter().fold(BabyBear::ZERO, |a, &b| a + b);
    sum.value() as usize & (params.items() - 1)
}

/// Fold an item into the mix (consensus; see the module docs).
pub fn fold(mix: &mut [BabyBear; MIX], item: &[BabyBear]) {
    let acc: [BabyBear; MIX] = std::array::from_fn(|e| {
        item.chunks_exact(MIX)
            .enumerate()
            .fold(BabyBear::ZERO, |sum, (c, chunk)| sum + chunk[e] * mix[(e + c) % MIX])
    });
    let t: [BabyBear; MIX] = std::array::from_fn(|e| acc[e] + mix[e]);
    for e in 0..MIX {
        mix[e] = t[e] * t[(e + 1) % MIX] + BabyBear::new(K[e]);
    }
}

/// The proof-of-work value of an attempt's output, reading items through
/// `read`.
pub fn pow_value<'a>(params: &Params, out: &[BabyBear; 24], mut read: impl FnMut(usize) -> std::borrow::Cow<'a, [BabyBear]>) -> [u8; 32] {
    let mut mix: [BabyBear; MIX] = out[8..].try_into().unwrap();
    for _ in 0..params.lookups {
        let item = read(index_of(params, &mix));
        fold(&mut mix, &item);
    }
    let mut elements = [BabyBear::ZERO; 24];
    elements[..8].copy_from_slice(&out[..8]);
    elements[8..].copy_from_slice(&mix);
    digest_to_bytes(hash_octets(DOMAIN_POW, 24, &elements))
}

/// The proof-of-work value of `header_bytes` with `nonce`, items computed
/// as needed -- what a validator does (no dataset).
pub fn pow_value_of(header_bytes: &[u8], nonce: Nonce, params: &Params) -> [u8; 32] {
    let out = attempt(&prefix(header_bytes), &nonce);
    pow_value(params, &out, |i| std::borrow::Cow::Owned(item(params, i).to_vec()))
}

/// Whether `hash` satisfies the target `max_hash` -- `hash <= max_hash`
/// as 256-bit big-endian integers, which is exactly `[u8; 32]`'s
/// lexicographic order.
pub fn meets_target(hash: &[u8; 32], max_hash: &[u8; 32]) -> bool {
    hash <= max_hash
}

/// Whether `nonce` is a valid proof of work for `header_bytes` under
/// target `max_hash` -- without the dataset.
pub fn verify(header_bytes: &[u8], nonce: Nonce, max_hash: &[u8; 32], params: &Params) -> bool {
    meets_target(&pow_value_of(header_bytes, nonce, params), max_hash)
}

/// Search nonces from 0 with the dataset, returning the first `(nonce,
/// block id)` whose proof-of-work value meets `max_hash`, or `None` if
/// none of the first `max_attempts` do -- bounded so callers (the node's
/// loop, tests) can interleave other work.
pub fn mine(header_bytes: &[u8], max_hash: &[u8; 32], max_attempts: u64, params: &Params) -> Option<(Nonce, [u8; 32])> {
    mine_from(header_bytes, max_hash, 0, max_attempts, params)
}

/// `mine`, from nonce counter `first`.
pub fn mine_from(header_bytes: &[u8], max_hash: &[u8; 32], first: u64, max_attempts: u64, params: &Params) -> Option<(Nonce, [u8; 32])> {
    let data = dataset(*params);
    let prefix = prefix(header_bytes);
    for counter in first..first + max_attempts {
        let nonce = nonce_from_counter(counter);
        let out = attempt(&prefix, &nonce);
        if meets_target(&pow_value_with(&data, &out), max_hash) {
            return Some((nonce, digest_to_bytes(out[..8].try_into().unwrap())));
        }
    }
    None
}

/// `pow_value`, reading `data` on the fast path -- what a miner does.
pub fn pow_value_with(data: &Dataset, out: &[BabyBear; 24]) -> [u8; 32] {
    let mut mix: [u32; MIX] = std::array::from_fn(|e| out[8 + e].value());
    for _ in 0..data.params.lookups {
        let i = fast::index_of(data.params.items_log, &mix);
        fast::fold(&mut mix, data.item(i));
    }
    let mut elements = [BabyBear::ZERO; 24];
    elements[..8].copy_from_slice(&out[..8]);
    for e in 0..MIX {
        elements[8 + e] = BabyBear::new(mix[e]);
    }
    digest_to_bytes(hash_octets(DOMAIN_POW, 24, &elements))
}

/// Multiply `value`, treated as a 256-bit big-endian integer, by the
/// plain scalar `multiplier`. Returns the low 256 bits of the product
/// plus whether the true product actually needed more than that (i.e.
/// whether it overflowed) -- long multiplication, one byte at a time
/// from the least significant end, carrying in a `u128` (comfortably
/// wide enough for a `u8 * u64` partial product plus carry).
fn mul_small(value: [u8; 32], multiplier: u64) -> ([u8; 32], bool) {
    let mut out = [0u8; 32];
    let mut carry: u128 = 0;
    for i in (0..32).rev() {
        let product = value[i] as u128 * multiplier as u128 + carry;
        out[i] = (product & 0xff) as u8;
        carry = product >> 8;
    }
    (out, carry != 0)
}

/// Divide `value`, treated as a 256-bit big-endian integer, by the
/// plain scalar `divisor` (floor division). Long division, one byte at
/// a time from the most significant end, carrying the remainder
/// forward.
fn div_small(value: [u8; 32], divisor: u64) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut remainder: u128 = 0;
    for i in 0..32 {
        let dividend = (remainder << 8) | value[i] as u128;
        out[i] = (dividend / divisor as u128) as u8;
        remainder = dividend % divisor as u128;
    }
    out
}

/// Scale `target`, treated as a 256-bit big-endian integer, by
/// `numerator / denominator` -- multiply then divide, each exactly
/// (only the final division's remainder is ever lost, same as real
/// integer division), saturating to the maximum representable value
/// instead of wrapping if the intermediate product overflows 256 bits.
/// What `chain`'s difficulty retargeting uses to scale the PoW target
/// by how an actual window's elapsed time compared to how long it was
/// supposed to take -- see that module's docs.
pub fn scale(target: [u8; 32], numerator: u64, denominator: u64) -> [u8; 32] {
    let (product, overflowed) = mul_small(target, numerator);
    if overflowed {
        return [0xffu8; 32];
    }
    div_small(product, denominator)
}

/// A `max_hash` with exactly `zero_bits` leading zero bits (clamped to
/// 256) and every bit after that set to 1 -- the easiest (largest)
/// value with that many leading zero bits, so a uniformly random
/// 256-bit value meets it with probability almost exactly `2^-zero_bits`.
///
/// Generalizes the "first N bytes zero, rest 0xff" pattern used
/// elsewhere in this crate (`block::INITIAL_MAX_HASH` is exactly
/// `max_hash_with_leading_zero_bits(8)`) to arbitrary *bit*
/// granularity instead of whole bytes -- each whole byte is a 256x
/// jump in difficulty, too coarse to dial in a starting point by hand.
/// `max_hash_with_leading_zero_bits(20)`, for instance, sits precisely
/// between 16 and 24 zero bits (two and three zero bytes).
pub fn max_hash_with_leading_zero_bits(zero_bits: u32) -> [u8; 32] {
    let zero_bits = zero_bits.min(256);
    let full_zero_bytes = (zero_bits / 8) as usize;
    let remaining_bits = zero_bits % 8;

    let mut out = [0xffu8; 32];
    for byte in out.iter_mut().take(full_zero_bytes) {
        *byte = 0x00;
    }
    if full_zero_bytes < 32 && remaining_bits > 0 {
        // Zero just the top `remaining_bits` bits of the next byte,
        // leaving the rest of it set.
        out[full_zero_bytes] = 0xffu8 >> remaining_bits;
    }
    out
}

// # Chain work
//
// `chain::Chain`'s fork-choice needs to compare competing chains by
// total accumulated work, not height -- height alone stopped being a
// valid proxy once difficulty could actually change block to block.
// This is Bitcoin's own definition (`GetBlockProof` in its source),
// computed exactly, as a fixed-width 256-bit integer throughout, the
// same way Bitcoin's `arith_uint256` does: summing work across many
// blocks is technically unbounded, but true overflow would require
// accumulating work on a scale many, many orders of magnitude beyond
// anything physically realistic, so -- deliberately, matching Bitcoin
// -- this wraps instead of growing arbitrarily wide. Nothing here
// needs revisiting as this crate's difficulty grows; the fixed width
// is the design, not a shortcut.

/// Bitwise NOT of a 256-bit value.
fn not256(x: [u8; 32]) -> [u8; 32] {
    x.map(|b| !b)
}

/// Add 1 to a 256-bit big-endian value, wrapping to all-zero on
/// overflow -- see the "Chain work" docs above on why wrapping is the
/// deliberate choice here, not a bug.
fn increment256(x: [u8; 32]) -> [u8; 32] {
    let mut out = x;
    for byte in out.iter_mut().rev() {
        if *byte == 0xff {
            *byte = 0;
        } else {
            *byte += 1;
            return out;
        }
    }
    out // overflowed all the way around to zero
}

/// Add two 256-bit big-endian values, wrapping on overflow -- see the
/// "Chain work" docs above.
pub fn add256(a: [u8; 32], b: [u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut carry: u16 = 0;
    for i in (0..32).rev() {
        let sum = a[i] as u16 + b[i] as u16 + carry;
        out[i] = (sum & 0xff) as u8;
        carry = sum >> 8;
    }
    out
}

/// Subtract `b` from `a`, treating both as 256-bit big-endian
/// integers. Only ever called by `divmod256` with `a >= b`; wraps
/// (silently, like the rest of this fixed-width arithmetic) rather
/// than panicking if that's ever violated.
fn sub256(a: [u8; 32], b: [u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut borrow: i16 = 0;
    for i in (0..32).rev() {
        let diff = a[i] as i16 - b[i] as i16 - borrow;
        if diff < 0 {
            out[i] = (diff + 256) as u8;
            borrow = 1;
        } else {
            out[i] = diff as u8;
            borrow = 0;
        }
    }
    out
}

/// Shift a 256-bit big-endian value left by one bit, setting the new
/// low bit to `carry_in` (0 or 1) -- the "bring in the next dividend
/// bit" step `divmod256` needs. Whatever bit overflows out the top is
/// simply dropped: in long division, the running remainder is always
/// smaller than the divisor going in, so that bit is never actually
/// significant.
fn shift_left_1_with_carry_in(x: [u8; 32], carry_in: u8) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut carry = carry_in;
    for i in (0..32).rev() {
        let overflow_bit = (x[i] & 0x80) >> 7;
        out[i] = (x[i] << 1) | carry;
        carry = overflow_bit;
    }
    out
}

/// Divide `dividend` by `divisor`, treating both as 256-bit big-endian
/// integers, returning `(quotient, remainder)`. Plain schoolbook
/// binary long division -- one bit at a time, 256 iterations, built
/// from nothing but the shift/compare/subtract primitives above
/// (`[u8; 32]`'s derived `Ord` already does big-endian integer
/// comparison correctly, same observation `meets_target` relies on).
///
/// `divisor` must be nonzero; returns `([0xff; 32], dividend)` instead
/// of panicking if it isn't, since there's no meaningful quotient --
/// the one caller, `work_for_target`, already special-cases its own
/// zero-divisor-adjacent inputs before ever reaching here.
pub(crate) fn divmod256(dividend: [u8; 32], divisor: [u8; 32]) -> ([u8; 32], [u8; 32]) {
    if divisor == [0u8; 32] {
        return ([0xffu8; 32], dividend);
    }

    let mut quotient = [0u8; 32];
    let mut remainder = [0u8; 32];

    for byte_index in 0..32 {
        for bit_index in (0..8).rev() {
            let incoming_bit = (dividend[byte_index] >> bit_index) & 1;
            remainder = shift_left_1_with_carry_in(remainder, incoming_bit);
            if remainder >= divisor {
                remainder = sub256(remainder, divisor);
                quotient[byte_index] |= 1 << bit_index;
            }
        }
    }

    (quotient, remainder)
}

/// The work one block mined against `target` represents -- Bitcoin's
/// own definition, `2^256 / (target + 1)`, computed without ever
/// needing a 257-bit intermediate value via the identity Bitcoin
/// itself uses: since `2^256 == !target + target + 1` (true for any
/// 256-bit `target`, by definition of bitwise NOT), dividing through
/// by `target + 1` gives `2^256/(target+1) == !target/(target+1) + 1`
/// *exactly* (the `+1` term is itself an exact multiple of the
/// divisor, so flooring the sum is the same as flooring the first
/// term and then adding the exact `1`). Smaller `target` (harder)
/// means more work; this is the per-block value `chain::Chain` sums
/// (via `add256`) to compare competing chains' total work.
///
/// Two boundary inputs get special-cased rather than falling through
/// the general formula, both because the natural result doesn't fit
/// in 256 bits otherwise:
/// - `target == 0` (a target no hash could ever satisfy) returns zero
///   work, matching Bitcoin's own special case for this input --
///   moot in practice either way, since no real block could ever be
///   mined against it.
/// - `target == [0xff; 32]` (the easiest possible target) would make
///   `target + 1` equal to exactly `2^256`, one past what 256 bits
///   can represent; the exact answer here is just `1`, so this
///   short-circuits rather than let that wrap incorrectly.
pub fn work_for_target(target: [u8; 32]) -> [u8; 32] {
    if target == [0u8; 32] {
        return [0u8; 32];
    }
    if target == [0xffu8; 32] {
        let mut one = [0u8; 32];
        one[31] = 1;
        return one;
    }

    let divisor = increment256(target); // target != MAX, so this can't wrap
    let (quotient, _remainder) = divmod256(not256(target), divisor);
    increment256(quotient) // quotient is well below MAX for any target in [1, MAX-1], so this can't wrap either
}

#[cfg(test)]
mod tests {
    use super::*;

    const T: Params = Params::TEST;

    #[test]
    fn ids_differ_across_nonces_and_headers() {
        assert_ne!(header_id(b"abc", nonce_from_counter(0)), header_id(b"abc", nonce_from_counter(1)));
        assert_ne!(header_id(b"abc", nonce_from_counter(0)), header_id(b"xyz", nonce_from_counter(0)));
        // The proof-of-work value isn't the id.
        assert_ne!(header_id(b"abc", nonce_from_counter(0)), pow_value_of(b"abc", nonce_from_counter(0), &T));
    }

    #[test]
    fn meets_target_boundary_behavior() {
        let h = [5u8; 32];

        // Equal to the target passes.
        assert!(meets_target(&h, &h));

        // Strictly larger than the target fails.
        let mut lower_target = h;
        lower_target[31] -= 1;
        assert!(!meets_target(&h, &lower_target));

        // Strictly smaller than the target passes.
        let mut higher_target = h;
        higher_target[31] += 1;
        assert!(meets_target(&h, &higher_target));
    }

    #[test]
    fn verify_accepts_a_value_used_as_its_own_target() {
        let header = b"block header bytes";
        let nonce = nonce_from_counter(42);
        let value = pow_value_of(header, nonce, &T);
        assert!(verify(header, nonce, &value, &T));
        assert!(!verify(header, nonce, &[0u8; 32], &T)); // only an exactly-zero value would pass
    }

    /// Mining with the dataset and validating without it agree, and
    /// mining returns the smallest satisfying nonce and its id.
    #[test]
    fn mining_with_the_dataset_matches_validating_without_it() {
        let header = b"abc";
        let target = pow_value_of(header, nonce_from_counter(3), &T);
        let (nonce, id) = mine(header, &target, 10, &T).expect("counter 3 itself satisfies the target");
        assert!(u64::from_le_bytes(nonce[..8].try_into().unwrap()) <= 3);
        assert_eq!(id, header_id(header, nonce));
        assert!(verify(header, nonce, &target, &T));
        assert!(mine(header, &[0u8; 32], 100, &T).is_none());
        // The stored dataset is exactly the computed items.
        let d = dataset(T);
        for i in [0, 1, T.items() - 1] {
            assert_eq!(d.item(i), item(&T, i).map(|e| e.value()));
        }
    }

    /// The miner's fast path agrees with the reference (consensus) mixing
    /// exactly, on random inputs and at the field's edges.
    #[test]
    fn the_fast_path_matches_the_reference() {
        let mut x = 0x1234_5678_9abc_def0u64;
        let mut next = move || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            (x % crate::poseidon2::P as u64) as u32
        };
        let edge = |k: usize| [0, 1, crate::poseidon2::P - 1, crate::poseidon2::P - 2][k % 4];
        for round in 0..200 {
            let mix: [u32; MIX] = std::array::from_fn(|e| if round < 4 { edge(e + round) } else { next() });
            let item: Vec<u32> = (0..ITEM_ELEMS).map(|k| if round < 4 { edge(k + round) } else { next() }).collect();
            let mut fast_mix = mix;
            fast::fold(&mut fast_mix, &item);
            let mut reference = mix.map(BabyBear::new);
            let item_ref: Vec<BabyBear> = item.iter().map(|&v| BabyBear::new(v)).collect();
            fold(&mut reference, &item_ref);
            assert_eq!(fast_mix, reference.map(|e| e.value()), "round {round}");
            assert_eq!(fast::index_of(T.items_log, &fast_mix), index_of(&T, &reference));
        }
        // And whole attempts agree.
        let d = dataset(T);
        for c in 0..20 {
            let out = attempt(&prefix(b"agree"), &nonce_from_counter(c));
            let reference = pow_value(&T, &out, |i| std::borrow::Cow::Owned(item(&T, i).to_vec()));
            assert_eq!(pow_value_with(&d, &out), reference);
        }
    }

    /// Items depend on their index and on the text, and every lookup moves
    /// the mix.
    #[test]
    fn items_and_mixing() {
        assert_ne!(item(&T, 0), item(&T, 1));
        assert_ne!(item(&T, 0), item(&Params { item_rounds: 3, ..T }, 0));
        let mut mix = [BabyBear::ONE; MIX];
        let before = mix;
        fold(&mut mix, &item(&T, 5));
        assert_ne!(mix, before);
        assert!(index_of(&T, &mix) < T.items());
    }

    /// Hash rate with the real parameters, and how memory-bound it is:
    /// mining against the real dataset vs one small enough to sit in cache
    /// (same work per attempt, only the memory differs). `[NETWORK=..]
    /// cargo test --release -- --ignored --nocapture pow_rates`.
    #[test]
    #[ignore]
    fn pow_rates() {
        for (name, params) in [("main", Params::MAIN), ("dev", Params::DEV), ("in cache (64 KiB)", Params { items_log: 7, ..Params::MAIN })] {
            let start = std::time::Instant::now();
            let d = dataset(params);
            println!("{name}: dataset {} MiB generated in {:.1?}", (d.params.items() * ITEM_ELEMS * 4) >> 20, start.elapsed());
            let header = b"pow rates";
            let bytes_per_attempt = (params.lookups as usize * ITEM_ELEMS * 4) as f64;
            for threads in [1u64, crate::parallel::threads() as u64] {
                let attempts = 20_000 * threads;
                let start = std::time::Instant::now();
                crate::parallel::map_each(threads as usize, |t| mine_from(header, &[0u8; 32], t as u64 * attempts, attempts / threads, &params));
                let rate = attempts as f64 / start.elapsed().as_secs_f64();
                println!("  {threads:>2} thread(s): {rate:>9.0} attempts/s ({:.2} GB/s of items read)", rate * bytes_per_attempt / 1e9);
            }
            // Where one attempt's time goes, on one thread.
            let n = 20_000u32;
            let (pre, nonce) = (prefix(header), nonce_from_counter(7));
            let start = std::time::Instant::now();
            for c in 0..n {
                std::hint::black_box(attempt(&pre, &nonce_from_counter(c as u64)));
            }
            let t_attempt = start.elapsed() / n;
            let mut mix = [1u32; MIX];
            let item0 = d.item(3).to_vec();
            let start = std::time::Instant::now();
            for _ in 0..n {
                fast::fold(&mut mix, std::hint::black_box(&item0));
            }
            let t_fold = start.elapsed() / n;
            let out = attempt(&pre, &nonce);
            let start = std::time::Instant::now();
            for _ in 0..n / 10 {
                std::hint::black_box(pow_value_with(&d, &out));
            }
            let t_value = start.elapsed() / (n / 10);
            println!("  one attempt: {t_attempt:.2?} start + {:.2?} = {} folds (in cache) ; whole pow value {t_value:.2?}", t_fold * params.lookups, params.lookups);
            let start = std::time::Instant::now();
            let n = 50;
            for c in 0..n {
                pow_value_of(header, nonce_from_counter(c), &params);
            }
            println!("  validating one header (no dataset): {:.2?}", start.elapsed() / n as u32);
        }
    }

    #[test]
    fn nonce_from_counter_zero_pads_the_upper_bytes() {
        let nonce = nonce_from_counter(0x0102030405060708);
        assert_eq!(&nonce[..8], &0x0102030405060708u64.to_le_bytes());
        assert!(nonce[8..].iter().all(|&b| b == 0));
    }

    #[test]
    fn scale_by_one_over_one_is_identity() {
        let target = {
            let mut b = [0xffu8; 32];
            b[0] = 0x00;
            b
        };
        assert_eq!(scale(target, 1, 1), target);
    }

    /// Hand-traced: byte 0 is `0x00` so nothing carries into the
    /// multiply; dividing by 2 after multiplying by 1 is a plain right
    /// shift -- byte 1's low bit (`0xff` is odd) carries into byte 2's
    /// new high bit, and every byte after that is `0xff >> 1 | 0x80 ==
    /// 0xff` again, so the carry just propagates to the end.
    #[test]
    fn scale_by_one_over_two_matches_a_hand_traced_halving() {
        let target = {
            let mut b = [0xffu8; 32];
            b[0] = 0x00;
            b
        };
        let mut expected = [0xffu8; 32];
        expected[0] = 0x00;
        expected[1] = 0x7f;
        assert_eq!(scale(target, 1, 2), expected);
    }

    #[test]
    fn scale_by_two_over_one_matches_a_hand_traced_doubling() {
        let target = {
            let mut b = [0x00u8; 32];
            b[1] = 0x7f;
            b
        };
        let mut expected = [0x00u8; 32];
        expected[1] = 0xfe;
        assert_eq!(scale(target, 2, 1), expected);
    }

    #[test]
    fn scale_saturates_instead_of_wrapping_on_overflow() {
        let target = {
            let mut b = [0u8; 32];
            b[0] = 0x80; // top bit set -- doubling overflows past bit 255
            b
        };
        assert_eq!(scale(target, 2, 1), [0xffu8; 32]);
    }

    /// A ratio that isn't a power of two, to confirm this is genuinely
    /// doing proportional arithmetic and not secretly just a bit shift
    /// in disguise. `0xff == 255 == 5 * 51`, with no remainder, so
    /// every byte of `[0xff; 32]` divides down to exactly `0x33` (51)
    /// with nothing left over to carry between bytes.
    #[test]
    fn scale_computes_a_non_power_of_two_ratio() {
        assert_eq!(scale([0xffu8; 32], 1, 5), [0x33u8; 32]);
    }

    #[test]
    fn zero_leading_zero_bits_is_the_maximum_possible_value() {
        assert_eq!(max_hash_with_leading_zero_bits(0), [0xffu8; 32]);
    }

    #[test]
    fn whole_byte_counts_match_the_first_n_bytes_zero_pattern() {
        let mut one_byte = [0xffu8; 32];
        one_byte[0] = 0x00;
        assert_eq!(max_hash_with_leading_zero_bits(8), one_byte);

        let mut two_bytes = [0xffu8; 32];
        two_bytes[0] = 0x00;
        two_bytes[1] = 0x00;
        assert_eq!(max_hash_with_leading_zero_bits(16), two_bytes);
    }

    /// The whole point: a count that isn't a multiple of 8 lands
    /// strictly between the two whole-byte values on either side of
    /// it, instead of jumping straight from one to the other.
    #[test]
    fn partial_byte_counts_land_strictly_between_the_adjacent_whole_bytes() {
        let sixteen = max_hash_with_leading_zero_bits(16);
        let twenty = max_hash_with_leading_zero_bits(20);
        let twenty_four = max_hash_with_leading_zero_bits(24);
        assert!(twenty < sixteen);
        assert!(twenty_four < twenty);

        // Hand-traced: 16 full zero bits is bytes 0-1; the next 4 bits
        // zero out the top nibble of byte 2 (0xff >> 4 == 0x0f),
        // leaving the rest (bytes 2's low nibble, and bytes 3..31) set.
        let mut expected = [0xffu8; 32];
        expected[0] = 0x00;
        expected[1] = 0x00;
        expected[2] = 0x0f;
        assert_eq!(twenty, expected);
    }

    #[test]
    fn two_hundred_fifty_six_leading_zero_bits_is_the_minimum_possible_value() {
        assert_eq!(max_hash_with_leading_zero_bits(256), [0x00u8; 32]);
    }

    #[test]
    fn counts_above_256_clamp_rather_than_panic() {
        assert_eq!(max_hash_with_leading_zero_bits(1000), [0x00u8; 32]);
    }

    /// A 256-bit big-endian value holding the small number `n` in its
    /// low 8 bytes, zero everywhere else -- makes the chain-work tests
    /// below readable as ordinary arithmetic instead of 32-byte arrays.
    fn u256(n: u64) -> [u8; 32] {
        let mut out = [0u8; 32];
        out[24..32].copy_from_slice(&n.to_be_bytes());
        out
    }

    #[test]
    fn add256_adds_small_values() {
        assert_eq!(add256(u256(2), u256(3)), u256(5));
    }

    #[test]
    fn add256_carries_across_a_byte_boundary() {
        assert_eq!(add256(u256(0xff), u256(1)), u256(0x100));
    }

    #[test]
    fn add256_wraps_on_overflow() {
        assert_eq!(add256([0xffu8; 32], u256(1)), [0u8; 32]);
    }

    #[test]
    fn divmod256_matches_ordinary_small_division() {
        assert_eq!(divmod256(u256(10), u256(3)), (u256(3), u256(1)));
    }

    #[test]
    fn divmod256_with_zero_remainder() {
        assert_eq!(divmod256(u256(12), u256(4)), (u256(3), u256(0)));
    }

    #[test]
    fn divmod256_by_a_divisor_larger_than_the_dividend() {
        assert_eq!(divmod256(u256(3), u256(10)), (u256(0), u256(3)));
    }

    #[test]
    fn work_for_target_of_zero_is_zero() {
        assert_eq!(work_for_target([0u8; 32]), [0u8; 32]);
    }

    #[test]
    fn work_for_target_of_the_easiest_target_is_one() {
        assert_eq!(work_for_target([0xffu8; 32]), u256(1));
    }

    /// Hand-traced independently of the identity `work_for_target`
    /// actually uses: `target` here is `2^255 - 1` (first byte `0x7f`,
    /// rest `0xff`), so `target + 1 == 2^255` exactly, and
    /// `2^256 / 2^255 == 2` exactly -- a clean value with no rounding
    /// to obscure a sign of a wrong implementation.
    #[test]
    fn work_for_target_matches_a_hand_traced_half_target() {
        let mut target = [0xffu8; 32];
        target[0] = 0x7f;
        assert_eq!(work_for_target(target), u256(2));
    }

    /// Ties back to this crate's own `INITIAL_MAX_HASH` (first byte
    /// zero, rest `0xff`): a uniformly random hash satisfies it with
    /// probability `1/256`, so finding one takes 256 attempts on
    /// average -- exactly the work value this must come out to.
    #[test]
    fn work_for_target_of_initial_max_hash_is_256() {
        assert_eq!(work_for_target(max_hash_with_leading_zero_bits(8)), u256(256));
    }

    #[test]
    fn work_for_target_of_sixteen_leading_zero_bits_is_65536() {
        assert_eq!(work_for_target(max_hash_with_leading_zero_bits(16)), u256(65_536));
    }

    #[test]
    fn harder_targets_have_strictly_more_work() {
        let easier = work_for_target(max_hash_with_leading_zero_bits(10));
        let harder = work_for_target(max_hash_with_leading_zero_bits(20));
        assert!(harder > easier);
    }
}
