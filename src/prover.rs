//! A block's zero-knowledge proof: the one thing that attests a block
//! body's commitments are properly authorized and that everything
//! balances, without revealing any of the plaintext (pubkeys, amounts,
//! signatures) behind them. See `block`'s and `chain`'s module docs for
//! why that check belongs here, permanently, rather than anywhere in
//! plaintext.
//!
//! The statement proven is `block_air`'s: for the body's public input
//! and output commitment lists, there are transactions such that every
//! input carries its owner's valid WOTS signature over its transaction,
//! every commitment is correctly formed, and `sum(inputs) + REWARD ==
//! sum(outputs)` exactly. The proof is a two-phase, zero-knowledge
//! `stark` proof of that circuit, at `PARAMS`.
//!
//! Deliberately generic over raw commitment lists (`inputs`/`outputs` as
//! `&[[u8; 32]]`), not `block::BlockBody` -- same layering discipline
//! already used by `pmmr`/`bitmap`: this module doesn't need to know
//! `BlockBody`'s specific shape, just the commitments it's attesting
//! about. It also avoids a dependency cycle: `BlockBody` holds a `Proof`
//! (see that module's docs), so `Proof` can't be defined in terms of
//! `BlockBody`.
//!
//! The miner proves every transaction in its block itself, from their
//! plaintext -- see `docs/BLOCK_TODO.md` #1.

#![allow(dead_code)]

use crate::recovery::NONCE_LEN;
use crate::aggregate::{self, Key, TreeParams, VerifyingKey};
use crate::block_air::{self, BlockAir, ChunkShape};
use crate::poseidon2::{BabyBear, P, digest_from_bytes, hash_bytes_32};
use crate::poseidon2_air::ROWS;
use crate::stark::{self, Params};
use crate::transaction::Transaction;

/// Every block's reward: a flat 1,000,000,000 units at every height
/// (`docs/BLOCK_TODO.md` #1). A consensus constant -- the proof enforces
/// `sum(inputs) + REWARD == sum(outputs)` exactly.
pub const REWARD: u64 = 1_000_000_000;

/// The proof system's parameters -- consensus constants, since a verifier
/// must check every block at the same ones. Chosen for small proofs and
/// fast verification over prover speed (blocks are minutes apart in
/// production): blowup 16 gives 4 bits per query, so 20 queries plus 20
/// bits of grinding come to 100 bits of (conjectured) soundness.
/// Challenges themselves come from the ~124-bit extension field.
pub const PARAMS: Params = Params {
    log_blowup: 4,
    num_queries: 20,
    grinding_bits: 20,
    hiding: true,
};

/// Every proof starts with its kind.
const KIND_DIRECT: u8 = 0;
const KIND_TREE: u8 = 1;

/// An encoded block proof -- what's published and hashed into
/// `body_hash`, decoded only to verify. Either kind proves the same
/// statement about the body's commitment lists, and consensus accepts
/// either for any block:
///
/// - **Direct** (`KIND_DIRECT`): the whole block in one `block_air`
///   trace -- then the trace's block count (`u32`, little-endian) and the
///   `stark::Proof`. Cheapest for small blocks; one trace can hold only
///   so much.
/// - **Tree** (`KIND_TREE`): the block's transactions proven in chunks
///   (`CHUNK_SHAPE`) and aggregated (`aggregate`) -- then the root's
///   amount totals `A`, `B` (`u64`s; `A - B` must be `REWARD`), the chunk
///   count (`u16`), every input's and then every output's chunk (`u16`
///   each, in body order), and the root `stark::Proof`. Any size.
///
/// Which kind to make is the miner's choice; `prove_block_auto` is the
/// reference miner's rule.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Proof {
    bytes: Vec<u8>,
}

/// Whether `commitment` is eight canonical field elements (each 4-byte
/// group below P). Every commitment a proof can attest to is; anything
/// else is a second byte string for the same elements, which the proof
/// can't tell apart but the UTXO set would treat as a different output.
pub fn is_canonical(commitment: &[u8; 32]) -> bool {
    commitment
        .chunks_exact(4)
        .all(|c| u32::from_le_bytes(c.try_into().unwrap()) < P)
}

fn elements(list: &[[u8; 32]]) -> Vec<[BabyBear; 8]> {
    list.iter().map(digest_from_bytes).collect()
}

fn nonce_elements(nonces: &[[u8; NONCE_LEN]]) -> Vec<[BabyBear; 8]> {
    nonces.iter().map(crate::output::nonce_limbs).collect()
}

// ---- Tree proofs: consensus constants ----------------------------------------

/// Every chunk's shape: up to 10 inputs and 256 outputs, padded to 2^17
/// rows (4096 blocks; ten inputs take about 2,600). A transaction with
/// more inputs than a chunk holds can only go in a direct proof.
pub const CHUNK_SHAPE: ChunkShape = ChunkShape {
    num_blocks: 4096,
    inputs: 10,
    outputs: 256,
};

/// Chunk proofs use the block parameters (zero knowledge: their witness
/// is the transactions).
pub const CHUNK_PARAMS: Params = PARAMS;

/// Every tree proof's size and parameters: the same soundness as `PARAMS`,
/// without zero-knowledge blinding -- a tree proof's witness is other
/// proofs, ultimately zero-knowledge chunk proofs (see `stark::Params::
/// hiding` and `docs/RECURSION.md`).
pub const TREE: TreeParams = TreeParams {
    trace_len: 1 << 18,
    params: Params {
        log_blowup: 4,
        num_queries: 20,
        grinding_bits: 20,
        hiding: false,
    },
};

/// `log2` of tree proofs' low-degree extension (`2^18` rows, composition
/// factor 4, blowup 16).
const TREE_LOG_LDE: usize = 24;

/// The verifying keys: the wrap and aggregation circuits' preprocessed
/// caps, as hex. Derived from the circuits (see the `tree_keys` test,
/// which regenerates them); any change to those circuits changes these.
const WRAP_CAP: &str = "50fc1065320d304ed895ba1f2d3e5125e32cd16a0d2c426eab165671bcbb0325c08ff50eda98885290d340586cf83f4424b0a44477884823afa3430b21f9706d40552b453dafd4497429e221d114c83ea62dca7357cc18226044e9426ab2623b1008a4288052a31f7a40f152cf6c960e789c0d1bd0f1f55d2744576dada872489a77fa3934638e1e5339a64667e9c72b92462f5646018a75636c0e0df2b7c9583702f15b2b5c5e74d64b0f5e37963f075876d409e8581c614e6178052c7f142eb2a3bc6ae1f7f2474f177b1cc451822cd17de2109dc69f2362f9d54c233b6d761930176eabb30463c624a82ff6b48857d162c773e3d80777a505fa282ae9bc4eec9dcd55c04e75309352541b75584b0a3b27fb0fc2052937ff7d154ae913bc14d29f99485f9276461bb51935c026bb4a86815060f9c7c253d1b8b4133856794893fd1c37582e7e3f56b1bd57d20e2a41613fe135a400310a7757f36576b33e3a128c5a17fea3cc4880c86e1728e2ab00c9781f648d277f46b8bd457232037f02104fcd35a170645ee8f9be150b4c4d69d1871852355f2935a326f9716829725e28610e3d63ddc51037b1f06fda824b71a0d2cb48d427115a31da190618a9966487ff1537d52004405636d95b3b74a12f417c4e453aaffd30f23d9a1e63409965dd2df5486f095373c51b6008e7b6c473d5a5ef2624824200ead5d33fc520ce1e9127ab71c8d409537b381151b964f410e5cc91337ab108183caf723f3e240c2635a181607ee0472d21b876248b0e012dc1f5d06663526048eaeee2642be3420fb3d16153e414e03c9238f141bf232a748c043006cd0c9977e9c652230bf80219012b071e416e976e8ab4017402f64b57c574f95e58d94a2491724839950e2e2a3be311566c473e752a926f614c7f315b135aca521eb9fc487aebe125396190518cf7b349e309505a6d1b1243a19b7e34cce2053db00e79281167a62b990cde137f3bb272936632596ff5397119e3e80693fd794360645d58e9579b52442c1532ed43323d98911c06e34eea489aaa1d028a2efc2245bf786bc6ed3041de19103f24e9fb6536c5ac27ebada61968498823e6021408815a6f727d7b2275bd09da2ac00b1a07aa7c4f6a80c190447b05ee469526571fa446e7042a1c320399ffa91252f3376274980f5238fd7d30e8de5250f6b1e158b5f87e2d8311d06d1f6bf90f2307e906b3461d32943fb500891bb4095695e02de6bf935a1a966146f0a6fa7003a96b75f1b6d20ab0e0d574a541dc1d905b8e43379d494a4ab77c778dfcb726555f4a713c1be91ea0f4385e2a8fdb3d83789d1e6250bd477619534ed5c68f4b995cc429a58dcd2885f4f41870d86964045d78618eba0d014a08d26a9e4832541500ac3fc171285478532d366740c765e5e6963cc3f4344af86ab30e05358908";
const AGGREGATE_CAP: &str = "34f3753a5695284bfe15c03ef2d73513157321718ab749542edecc70c4b9d50df7bbcb40d52d8c4214722733767eb028877f685238138769ceb3350868e3152536e20a5b0bf1180a36b3b531f36e1f17d896b12fe868fd738e341f4036fbf44e08b79b415e55c66817459b14f021df05762dc53ccca7171dff1099345a48361c657e3f12da9cb4061546790aa2afba3041ac4a2393cab95324dd2e4025fd074bcb531c24d23942011ff2531d1f16021b39ef9a3314af2d33bb66272011fc436dd54dc854c568156817308671ffb2e80227df800496e45239185cc63859e2ea480068423192950131b4161b38eccd6741990e2d138e7289044570961e9099b66244e1d051a40e792c349aca12290e110d82c6db082af5605d9afc8d1ed7ba544fe19edf030af45402de1c2f05e536405ac9d4396160b99d0cf140d81d3a63d063567a1a54a92a8c6355fa23381741e4230a62a84bfeedec24c7a82c25c82b6f31b1208a746e23006d13fecf7687e5c226f9de0740b241a015116595597a09923af0e31f2e3bd6d62fa9abc066a06ac63b1d8600042952212adc16d43ecd89834a18299d4d08666a5408be83684f90eb38fa124f2465612b312c0b6924aa7efc51b2068c5099d94e335dc9fc59cc53276b7c3fbb0802be111a90244a4d238cb85fb7d43f4118ef2507919516401005be5bb9e91f50e08fcf4a9d0e98047f29981da439696e6a207b5edc1b3b52c5baad6cf75e201dc4c08a4dee997772acd6ae377630c8177c792f6fb9b89c74b4df901bdf01720a6e5f1972a5fed7133a50ec084dec286d19a3fd551b02cb28b0f9324ab8039c0ba1eebe752bd9c17591c0225d53609e4664237d4e69e8d009b8052475a279903337cb563f29c9063e0d26d120979eac76ad894c2f43b4a70b0d5c172bbf268755601af1544200622483404a60097f834a860f6e2ef77f835a860a5a02b10ced1b5ec2bf4a224a681f62f632290fbd2b0a6260bd3f02a5904c0de4524b160ee11bba89f73608f14b60781d1e177bdae568df80830536fcdf660cd3090253be5143d76672631b5c104b266eb93d20a0826489fd6d01bb5db4290239dc296c0c6a00e048d30e2e202204b0fd7e11207e680d2d9da047f955325cc49f19722899b26d20130167b3cefa76bc3ad84df58c826a5784536d01717171c9e1a341fb69fb60a560a248afcc89481fdb2f40300e6d58991cae258b1c7e255828d56a59124a639d2d4a6d888053173bea833289bb604f27f67d2529383561614b873cdf72a569db6d4b36e131ee0a24b569552f8ee31dd38d0657a9240217066ee802e40a307601e20d148dfc07628730ba6777cc551d0f581d1584fa394a75dc7d6f5bff903597891d6c6203c72920d23132df6eb85a3257254b72d4bd39efcaeb60f0a7a3723ea95c6ebc80474ea1a8e54d";

fn cap_from_hex(hex: &str) -> Vec<[u8; 32]> {
    let bytes: Vec<u8> = (0..hex.len() / 2).map(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap()).collect();
    bytes.chunks_exact(32).map(|c| c.try_into().unwrap()).collect()
}

fn cap_to_hex(cap: &[[u8; 32]]) -> String {
    cap.iter().flatten().map(|b| format!("{b:02x}")).collect()
}

/// The consensus verifying key for tree proofs.
pub fn tree_verifying_key() -> VerifyingKey {
    VerifyingKey {
        wrap_cap: cap_from_hex(WRAP_CAP),
        aggregate_cap: cap_from_hex(AGGREGATE_CAP),
        log_lde: TREE_LOG_LDE,
        tree: TREE,
    }
}

/// Little-endian reads off the front of a byte slice.
struct Bytes<'a>(&'a [u8]);

impl<'a> Bytes<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let (head, tail) = (self.0.get(..n)?, &self.0[n..]);
        self.0 = tail;
        Some(head)
    }
    fn u16(&mut self) -> Option<u16> {
        Some(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
    }
    fn u32(&mut self) -> Option<u32> {
        Some(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
    fn u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }
}

impl Proof {
    pub fn from_bytes(bytes: Vec<u8>) -> Self {
        Proof { bytes }
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    /// Whether this is a tree proof (else direct, or garbage).
    pub fn is_tree(&self) -> bool {
        self.bytes.first() == Some(&KIND_TREE)
    }

    /// An empty stand-in proof, for tests about everything *but* proofs
    /// (forks, retargeting, sync), whose chains skip proof checks.
    #[cfg(test)]
    pub fn placeholder() -> Self {
        Proof::default()
    }

    /// What `BlockBody::body_hash` folds in to commit to the proof.
    pub fn commitment_hash(&self) -> [u8; 32] {
        hash_bytes_32(&self.bytes)
    }

    /// Whether this proves the block statement for exactly these public
    /// commitment lists and outputs' recovery nonces (`nonces[i]` is
    /// `outputs[i]`'s) -- of either kind.
    pub fn verify(&self, inputs: &[[u8; 32]], outputs: &[[u8; 32]], nonces: &[[u8; NONCE_LEN]]) -> bool {
        if !inputs.iter().chain(outputs).all(is_canonical) || nonces.len() != outputs.len() {
            return false;
        }
        let mut r = Bytes(&self.bytes);
        match r.take(1).map(|k| k[0]) {
            Some(KIND_DIRECT) => verify_direct(r, inputs, outputs, nonces),
            Some(KIND_TREE) => verify_tree(r, inputs, outputs, nonces),
            _ => false,
        }
    }
}

fn verify_direct(mut r: Bytes, inputs: &[[u8; 32]], outputs: &[[u8; 32]], nonces: &[[u8; NONCE_LEN]]) -> bool {
    let Some(num_blocks) = r.u32().map(|n| n as usize) else {
        return false;
    };
    let max_blocks = (1 << block_air::max_log_rows(&PARAMS)) / ROWS;
    if !num_blocks.is_power_of_two() || num_blocks < 2 || num_blocks > max_blocks {
        return false;
    }
    let Some(proof) = stark::Proof::from_bytes(r.0) else {
        return false;
    };
    let air = BlockAir::new(num_blocks, elements(inputs), elements(outputs), nonce_elements(nonces), REWARD);
    stark::verify(&air, &proof, &PARAMS)
}

/// One chunk's input and output commitments, and its outputs' nonces.
type ChunkLists = (Vec<[u8; 32]>, Vec<[u8; 32]>, Vec<[u8; NONCE_LEN]>);

/// Split the body's lists into chunks by the given chunk indices,
/// keeping body order (so each chunk's lists stay sorted). `None` if an
/// index is out of range or a chunk overflows `CHUNK_SHAPE`.
fn chunk_lists(
    count: usize,
    input_chunks: &[u16],
    output_chunks: &[u16],
    inputs: &[[u8; 32]],
    outputs: &[[u8; 32]],
    nonces: &[[u8; NONCE_LEN]],
) -> Option<Vec<ChunkLists>> {
    let mut chunks = vec![(Vec::new(), Vec::new(), Vec::new()); count];
    for (&c, commitment) in input_chunks.iter().zip(inputs) {
        chunks.get_mut(c as usize)?.0.push(*commitment);
    }
    for ((&c, commitment), nonce) in output_chunks.iter().zip(outputs).zip(nonces) {
        let chunk = chunks.get_mut(c as usize)?;
        chunk.1.push(*commitment);
        chunk.2.push(*nonce);
    }
    chunks
        .iter()
        .all(|(i, o, _)| i.len() <= CHUNK_SHAPE.inputs && o.len() <= CHUNK_SHAPE.outputs)
        .then_some(chunks)
}

fn chunk_air(inputs: &[[u8; 32]], outputs: &[[u8; 32]], nonces: &[[u8; NONCE_LEN]], net: (u64, u64)) -> BlockAir {
    BlockAir::chunk(
        CHUNK_SHAPE.num_blocks,
        elements(inputs),
        elements(outputs),
        nonce_elements(nonces),
        net,
        Some((CHUNK_SHAPE.inputs, CHUNK_SHAPE.outputs)),
    )
}

fn verify_tree(mut r: Bytes, inputs: &[[u8; 32]], outputs: &[[u8; 32]], nonces: &[[u8; NONCE_LEN]]) -> bool {
    let header = (|| {
        let amounts = (r.u64()?, r.u64()?);
        let count = r.u16()? as usize;
        let input_chunks: Vec<u16> = (0..inputs.len()).map(|_| r.u16()).collect::<Option<_>>()?;
        let output_chunks: Vec<u16> = (0..outputs.len()).map(|_| r.u16()).collect::<Option<_>>()?;
        Some((amounts, count, input_chunks, output_chunks))
    })();
    let Some((amounts, count, input_chunks, output_chunks)) = header else {
        return false;
    };
    if count == 0 {
        return false;
    }
    let Some(chunks) = chunk_lists(count, &input_chunks, &output_chunks, inputs, outputs, nonces) else {
        return false;
    };
    let Some(proof) = stark::Proof::from_bytes(r.0) else {
        return false;
    };
    // A chunk's data leaves its amounts out, so any will do here.
    let airs: Vec<BlockAir> = chunks.iter().map(|(i, o, n)| chunk_air(i, o, n, (0, 0))).collect();
    tree_verifying_key().verify_block(&airs, amounts, REWARD, &proof)
}

/// Prove the block statement for `transactions` (each fully signed),
/// whose commitments must come out to exactly `inputs` and `outputs` --
/// the lists the block body will publish -- as a direct proof. `seed`
/// must be fresh random bytes for every proof: it's what keeps the proof
/// zero-knowledge (see `stark`'s docs). `None` if the transactions don't
/// verify, don't balance against `REWARD`, don't match the lists, or
/// don't fit one trace.
pub fn prove_block(inputs: &[[u8; 32]], outputs: &[[u8; 32]], transactions: &[Transaction], seed: [u8; 32]) -> Option<Proof> {
    let witness = block_air::build(transactions, REWARD).ok()?;
    if witness.air.public_inputs() != elements(inputs) || witness.air.public_outputs() != elements(outputs) {
        return None;
    }
    let proof = stark::prove(&witness.air, &witness.trace, &PARAMS, seed).ok()?;
    let mut bytes = vec![KIND_DIRECT];
    bytes.extend((witness.air.num_blocks() as u32).to_le_bytes());
    bytes.extend(proof.to_bytes());
    Some(Proof { bytes })
}

/// The reference miner's rule: a direct proof for blocks of up to
/// `CHUNK_SHAPE.inputs` inputs, a tree proof beyond (falling back to
/// direct if the block can't be chunked -- a transaction with too many
/// inputs or outputs for one chunk). Consensus accepts either kind for any
/// block; this is only a cost choice.
pub fn prove_block_auto(inputs: &[[u8; 32]], outputs: &[[u8; 32]], transactions: &[Transaction], seed: [u8; 32]) -> Option<Proof> {
    if prefers_tree(inputs.len())
        && let Some(proof) = prove_block_tree(inputs, outputs, transactions, seed)
    {
        return Some(proof);
    }
    prove_block(inputs, outputs, transactions, seed)
}

/// The reference rule: a tree for blocks with more inputs than one chunk
/// holds.
fn prefers_tree(inputs: usize) -> bool {
    inputs > CHUNK_SHAPE.inputs
}

/// Group transactions, in order, into chunks that fit `CHUNK_SHAPE`;
/// `None` if one doesn't fit even alone.
fn partition(transactions: &[Transaction]) -> Option<Vec<Vec<Transaction>>> {
    let mut chunks: Vec<Vec<Transaction>> = Vec::new();
    let (mut ins, mut outs) = (usize::MAX, usize::MAX);
    for tx in transactions {
        let (i, o) = (tx.inputs.len(), tx.outputs.len());
        if i > CHUNK_SHAPE.inputs || o > CHUNK_SHAPE.outputs {
            return None;
        }
        if chunks.is_empty() || ins + i > CHUNK_SHAPE.inputs || outs + o > CHUNK_SHAPE.outputs {
            chunks.push(Vec::new());
            (ins, outs) = (0, 0);
        }
        chunks.last_mut().unwrap().push(tx.clone());
        (ins, outs) = (ins + i, outs + o);
    }
    Some(chunks)
}

/// The tree circuits' proving keys -- derived from the first tree block
/// this process proves (their fixed columns don't depend on which), then
/// kept.
struct TreeKeys {
    wrap: Key,
    aggregate: Option<Key>,
}

static TREE_KEYS: std::sync::Mutex<Option<TreeKeys>> = std::sync::Mutex::new(None);

/// Prove the block as a tree: chunks, wraps, aggregation. `None` as for
/// `prove_block`, or if the transactions can't be chunked.
pub fn prove_block_tree(inputs: &[[u8; 32]], outputs: &[[u8; 32]], transactions: &[Transaction], seed: [u8; 32]) -> Option<Proof> {
    let groups = partition(transactions)?;
    let derive = |k: u8| {
        let mut s = seed;
        s[31] ^= k;
        s[30] ^= 0x5a;
        s
    };
    // Each chunk's net: what its outputs take beyond its inputs (a), or
    // the reverse (b) -- its share of reward and fees.
    let mut chunks = Vec::with_capacity(groups.len());
    for (k, txs) in groups.iter().enumerate() {
        let spent: u128 = txs.iter().flat_map(|t| &t.inputs).map(|i| i.amount as u128).sum();
        let created: u128 = txs.iter().flat_map(|t| &t.outputs).map(|o| o.amount as u128).sum();
        let net = if created >= spent {
            (u64::try_from(created - spent).ok()?, 0)
        } else {
            (0, u64::try_from(spent - created).ok()?)
        };
        let witness = block_air::build_chunk(txs, net, CHUNK_SHAPE).ok()?;
        let proof = stark::prove(&witness.air, &witness.trace, &CHUNK_PARAMS, derive(k as u8)).ok()?;
        chunks.push((witness.air, proof));
    }

    // Each body commitment's chunk.
    let mut chunk_of: std::collections::HashMap<[u8; 32], u16> = Default::default();
    for (k, (air, _)) in chunks.iter().enumerate() {
        for c in air.public_inputs().iter().chain(air.public_outputs()) {
            chunk_of.insert(crate::poseidon2::digest_to_bytes(*c), k as u16);
        }
    }
    let input_chunks: Vec<u16> = inputs.iter().map(|c| chunk_of.get(c).copied()).collect::<Option<_>>()?;
    let output_chunks: Vec<u16> = outputs.iter().map(|c| chunk_of.get(c).copied()).collect::<Option<_>>()?;
    if chunk_of.len() != inputs.len() + outputs.len() {
        return None; // the transactions' commitments aren't exactly the body's
    }

    let mut keys = TREE_KEYS.lock().unwrap();
    if keys.is_none() {
        let (air, proof) = &chunks[0];
        let wrap = aggregate::wrap_key(air, proof, &CHUNK_PARAMS, &TREE).ok()?;
        *keys = Some(TreeKeys { wrap, aggregate: None });
    }
    let keys = keys.as_mut().unwrap();
    let mut wraps = Vec::with_capacity(chunks.len());
    for (k, (air, proof)) in chunks.iter().enumerate() {
        wraps.push(aggregate::wrap(&keys.wrap, air, proof, &CHUNK_PARAMS, &TREE, derive(0x80 | k as u8)).ok()?);
    }
    let root = if wraps.len() == 1 {
        wraps.pop().unwrap()
    } else {
        if keys.aggregate.is_none() {
            keys.aggregate = Some(aggregate::aggregate_key([&wraps[0], &wraps[1]], &keys.wrap, &TREE).ok()?);
        }
        aggregate::aggregate_all(keys.aggregate.as_ref().unwrap(), &keys.wrap, wraps, &TREE, derive(0xff)).ok()?
    };

    let mut bytes = vec![KIND_TREE];
    bytes.extend(root.amounts.0.to_le_bytes());
    bytes.extend(root.amounts.1.to_le_bytes());
    bytes.extend((chunks.len() as u16).to_le_bytes());
    for c in input_chunks.iter().chain(&output_chunks) {
        bytes.extend(c.to_le_bytes());
    }
    bytes.extend(root.proof.to_bytes());
    // Check against the consensus key before anyone else has to: keys
    // derived here that don't match it (stale constants) would make every
    // tree proof this miner publishes invalid.
    let proof = Proof { bytes };
    let nonce_of: std::collections::HashMap<[u8; 32], [u8; NONCE_LEN]> =
        transactions.iter().flat_map(|t| &t.outputs).map(|o| (o.commitment(), o.nonce)).collect();
    let nonces: Vec<[u8; NONCE_LEN]> = outputs.iter().map(|c| nonce_of.get(c).copied()).collect::<Option<_>>()?;
    proof.verify(inputs, outputs, &nonces).then_some(proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block::BlockBody;
    use crate::output::Output;
    use crate::stark::Air;
    use crate::wots;

    /// A block's public lists -- inputs, outputs, the outputs' nonces --
    /// and the transactions behind them.
    type TestBlock = (Vec<[u8; 32]>, Vec<[u8; 32]>, Vec<[u8; NONCE_LEN]>, Vec<Transaction>);

    fn reward_block() -> TestBlock {
        let (_, pk) = wots::keygen(&[1; 32]);
        let mut tx = Transaction::new();
        tx.add_output(Output::new(&pk, REWARD)).unwrap();
        let body = BlockBody::from_transactions(std::slice::from_ref(&tx)).unwrap();
        (body.inputs, body.outputs, body.nonces, vec![tx])
    }

    #[test]
    fn a_reward_proof_verifies_against_its_lists_and_no_others() {
        let (inputs, outputs, nonces, txs) = reward_block();
        let proof = prove_block(&inputs, &outputs, &txs, [1; 32]).unwrap();
        assert!(proof.verify(&inputs, &outputs, &nonces));

        let mut other = outputs.clone();
        other[0][0] ^= 1;
        assert!(!proof.verify(&inputs, &other, &nonces));
        assert!(!proof.verify(&inputs, &[], &[]));
        // The outputs' nonces are part of the statement.
        let mut altered = nonces.clone();
        altered[0][0] ^= 1;
        assert!(!proof.verify(&inputs, &outputs, &altered));
    }

    #[test]
    fn proving_refuses_lists_that_dont_match_the_transactions() {
        let (inputs, mut outputs, _nonces, txs) = reward_block();
        outputs[0][0] ^= 1;
        assert!(prove_block(&inputs, &outputs, &txs, [1; 32]).is_none());
    }

    #[test]
    fn proving_refuses_a_block_that_overclaims_the_reward() {
        let (_, pk) = wots::keygen(&[1; 32]);
        let mut tx = Transaction::new();
        tx.add_output(Output::new(&pk, REWARD + 1)).unwrap();
        let body = BlockBody::from_transactions(std::slice::from_ref(&tx)).unwrap();
        assert!(prove_block(&body.inputs, &body.outputs, &[tx], [1; 32]).is_none());
    }

    #[test]
    fn garbage_and_placeholder_proofs_dont_verify() {
        let (inputs, outputs, nonces, _) = reward_block();
        assert!(!Proof::placeholder().verify(&inputs, &outputs, &nonces));
        assert!(!Proof::from_bytes(vec![4, 0, 0, 0, 1, 2, 3]).verify(&inputs, &outputs, &nonces));
        assert!(!Proof::from_bytes(vec![3, 0, 0, 0]).verify(&inputs, &outputs, &nonces));
    }

    #[test]
    fn tree_proof_headers_are_checked_before_anything_expensive() {
        let (inputs, outputs, nonces, _) = reward_block();
        // Truncated header, zero chunks, an out-of-range chunk index.
        let mut header = vec![KIND_TREE];
        header.extend(REWARD.to_le_bytes());
        header.extend(0u64.to_le_bytes());
        assert!(!Proof::from_bytes(header.clone()).verify(&inputs, &outputs, &nonces));
        let mut zero = header.clone();
        zero.extend(0u16.to_le_bytes());
        zero.extend(0u16.to_le_bytes());
        assert!(!Proof::from_bytes(zero).verify(&inputs, &outputs, &nonces));
        let mut out_of_range = header;
        out_of_range.extend(1u16.to_le_bytes());
        out_of_range.extend(5u16.to_le_bytes());
        assert!(!Proof::from_bytes(out_of_range).verify(&inputs, &outputs, &nonces));
    }

    #[test]
    fn chunks_overflowing_their_shape_are_refused() {
        let commitment = |k: u8| [k; 32];
        let inputs: Vec<[u8; 32]> = (0..=CHUNK_SHAPE.inputs as u8).map(commitment).collect();
        let all_in_one = vec![0u16; inputs.len()];
        assert!(chunk_lists(1, &all_in_one, &[], &inputs, &[], &[]).is_none());
        let mut split = all_in_one;
        split[0] = 1;
        let chunks = chunk_lists(2, &split, &[], &inputs, &[], &[]).unwrap();
        assert_eq!((chunks[0].0.len(), chunks[1].0.len()), (CHUNK_SHAPE.inputs, 1));
        // Body order is kept within each chunk.
        assert_eq!(chunks[0].0[0], commitment(1));
    }

    /// `count` single-input spends (each paying a fee of 10) and the reward
    /// transaction claiming the reward plus all fees.
    fn spends(count: u8) -> TestBlock {
        let mut txs = Vec::new();
        for k in 0..count {
            let (sk, pk) = wots::keygen(&[100 + k; 32]);
            let (_, to) = wots::keygen(&[200 - k; 32]);
            let mut tx = Transaction::new();
            tx.add_input(&pk, 1000).unwrap();
            tx.add_output(Output::new(&to, 990)).unwrap();
            assert!(tx.sign_input(&pk, &sk));
            txs.push(tx);
        }
        let (_, miner) = wots::keygen(&[7; 32]);
        let mut reward = Transaction::new();
        reward.add_output(Output::new(&miner, REWARD + 10 * count as u64)).unwrap();
        txs.push(reward);
        let body = BlockBody::from_transactions(&txs).unwrap();
        (body.inputs, body.outputs, body.nonces, txs)
    }

    #[test]
    fn the_reference_rule_uses_a_tree_beyond_one_chunk_of_inputs() {
        assert!(!prefers_tree(0) && !prefers_tree(10));
        assert!(prefers_tree(11) && prefers_tree(10_000));
    }

    #[test]
    fn transactions_partition_into_chunks_in_order() {
        let (_, _, _, txs) = spends(12);
        let chunks = partition(&txs).unwrap();
        assert_eq!(chunks.iter().map(|c| c.len()).collect::<Vec<_>>(), vec![10, 3]);
        let mut big = Transaction::new();
        for k in 0..=CHUNK_SHAPE.inputs as u8 {
            big.add_input(&wots::keygen(&[k; 32]).1, 1).unwrap();
        }
        assert!(partition(&[big]).is_none());
    }

    /// Prove an 11-input block as a tree with the consensus parameters,
    /// and print the tree circuits' verifying keys -- run after changing
    /// any circuit, then update `WRAP_CAP` / `AGGREGATE_CAP`. Then checks
    /// the proof verifies, and tampering is refused. Slow (minutes):
    /// `cargo test --release -- --ignored --nocapture tree_keys`.
    #[test]
    #[ignore]
    fn tree_keys() {
        let (inputs, outputs, nonces, txs) = spends(11);
        let start = std::time::Instant::now();
        let proof = prove_block_tree(&inputs, &outputs, &txs, [3; 32]);
        println!("proved in {:.2?}", start.elapsed());
        // (The lock is released at the end of this block: proving again
        // below takes it.)
        let (wrap, aggregate) = {
            let keys = TREE_KEYS.lock().unwrap();
            let keys = keys.as_ref().unwrap();
            assert_eq!(keys.wrap.preprocessed.log_lde, TREE_LOG_LDE);
            (
                cap_to_hex(&keys.wrap.preprocessed.cap),
                cap_to_hex(&keys.aggregate.as_ref().unwrap().preprocessed.cap),
            )
        };
        if wrap != WRAP_CAP || aggregate != AGGREGATE_CAP {
            println!("const WRAP_CAP: &str = \"{wrap}\";");
            println!("const AGGREGATE_CAP: &str = \"{aggregate}\";");
            panic!("the verifying-key constants are stale: update them to the above");
        }
        let proof = proof.expect("a tree proof that verifies");
        assert!(proof.is_tree());
        println!("tree proof: {} KB", proof.len() / 1024);
        let start = std::time::Instant::now();
        assert!(proof.verify(&inputs, &outputs, &nonces));
        println!("verified in {:.2?}", start.elapsed());
        // Other lists, or a different claimed split of the totals.
        let mut other = outputs.clone();
        other.swap(0, 1);
        assert!(!proof.verify(&inputs, &other, &nonces));
        let mut bytes = proof.as_bytes().to_vec();
        bytes[1] ^= 1; // A
        bytes[9] ^= 1; // B, keeping A - B
        assert!(!Proof::from_bytes(bytes).verify(&inputs, &outputs, &nonces));
        // The reference rule makes a small block's proof direct.
        let (i, o, n, t) = spends(2);
        let small = prove_block_auto(&i, &o, &t, [5; 32]).unwrap();
        assert!(!small.is_tree() && small.verify(&i, &o, &n));
    }

    /// Not a correctness test: proving costs, one case per process (so
    /// peak memory can be measured per case, e.g. with `/usr/bin/time -v`).
    /// `COST=direct INPUTS=n`: a direct proof of a block with `n` one-input
    /// spends plus the reward. `COST=chunk`: one chunk proof (fixed shape,
    /// so any chunk costs the same). `COST=tree INPUTS=n`: a whole tree
    /// block, stage by stage. Run with
    /// `COST=... cargo test --release -- --ignored --nocapture proof_costs`.
    #[test]
    #[ignore]
    fn proof_costs() {
        let case = std::env::var("COST").unwrap_or_default();
        let count: u8 = std::env::var("INPUTS").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
        let (inputs, outputs, nonces, txs) = spends(count);
        let time = std::time::Instant::now;
        match case.as_str() {
            "direct" => {
                let witness = block_air::build(&txs, REWARD).unwrap();
                let start = time();
                let proof = prove_block(&inputs, &outputs, &txs, [1; 32]).unwrap();
                let proving = start.elapsed();
                let start = time();
                assert!(proof.verify(&inputs, &outputs, &nonces));
                println!(
                    "direct, {count} inputs: {} rows; prove {proving:.2?}; {:.1} KB; verify {:.2?}",
                    witness.air.trace_len(),
                    proof.len() as f64 / 1024.0,
                    start.elapsed()
                );
            }
            "chunk" => {
                let chunk = block_air::build_chunk(&txs, (REWARD, 0), CHUNK_SHAPE).unwrap();
                let start = time();
                let proof = stark::prove(&chunk.air, &chunk.trace, &CHUNK_PARAMS, [1; 32]).unwrap();
                println!(
                    "chunk, {count} inputs: {} rows; prove {:.2?}; {:.1} KB",
                    chunk.air.trace_len(),
                    start.elapsed(),
                    proof.to_bytes().len() as f64 / 1024.0
                );
            }
            "tree" => {
                let groups = partition(&txs).unwrap();
                let mut chunks = Vec::new();
                for txs in &groups {
                    let spent: u64 = txs.iter().flat_map(|t| &t.inputs).map(|i| i.amount).sum();
                    let created: u64 = txs.iter().flat_map(|t| &t.outputs).map(|o| o.amount).sum();
                    let net = if created >= spent { (created - spent, 0) } else { (0, spent - created) };
                    let w = block_air::build_chunk(txs, net, CHUNK_SHAPE).unwrap();
                    let start = time();
                    let proof = stark::prove(&w.air, &w.trace, &CHUNK_PARAMS, [1; 32]).unwrap();
                    println!("  chunk proof: {:.2?}", start.elapsed());
                    chunks.push((w.air, proof));
                }
                let start = time();
                let wrap_key = aggregate::wrap_key(&chunks[0].0, &chunks[0].1, &CHUNK_PARAMS, &TREE).unwrap();
                println!("  wrap key (one-time): {:.2?}", start.elapsed());
                let mut wraps = Vec::new();
                for (air, proof) in &chunks {
                    let start = time();
                    wraps.push(aggregate::wrap(&wrap_key, air, proof, &CHUNK_PARAMS, &TREE, [2; 32]).unwrap());
                    println!("  wrap: {:.2?}", start.elapsed());
                }
                let start = time();
                let key = aggregate::aggregate_key([&wraps[0], &wraps[1]], &wrap_key, &TREE).unwrap();
                println!("  aggregation key (one-time): {:.2?}", start.elapsed());
                let start = time();
                let root = aggregate::aggregate_all(&key, &wrap_key, wraps, &TREE, [3; 32]).unwrap();
                println!("  aggregation(s): {:.2?}; root {:.1} KB", start.elapsed(), root.proof.to_bytes().len() as f64 / 1024.0);
            }
            _ => panic!("set COST to direct, chunk or tree"),
        }
    }

    #[test]
    fn non_canonical_commitments_are_refused() {
        assert!(is_canonical(&[0u8; 32]));
        let mut bad = [0u8; 32];
        bad[..4].copy_from_slice(&P.to_le_bytes());
        assert!(!is_canonical(&bad));
    }
}
