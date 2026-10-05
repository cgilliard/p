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
const WRAP_CAP: &str = "33b49c24b8636d0f0284fd4dbcb52f6299d74d2e09d49352275be35a328d4320a3249a6f2b1a593bcfef9102c72ae06d7b9e25396085bb37c535f623220fde27ddff0115b6bfd8571c94fa004d8ad717f3e65a69ceab28238c2bba53b40ab95e7602ce4619ae425d614b7f17de1ba2721ea5b35689824d03c6f0bc51d1a9155407568a34025747027a89eb1046d4af1ef1c52d07e8573e35a2a43b295f2eba079aef8c325906361fdca9055daad67732530a332d50123f6b8c999b159078ad41f713b9333fa6fc5ea66ed66838d3eb0079402216b83a5a34c9e71a7778bfd43d3bedbb21a7af4159f982c1653203c61c65bb801f9d58760db716420bf96dc3530d51f72c045b704e01f9401f24ffa2672d6a272831d49c31b2c7835c10c96c1b2206825844569a024c4a2702a6c9f24d5a43c41729d2a216df2bff469dbe0d33881b1c2caa5b182a9fdc915c926b664793530445faa5133300860822742f204b5e73b6341bb4d06e04347813859b851f15d6b07318864526665ce32b45ee5b5983bec6578fe5ad1128087f6a763f3770e395396470d9081cbcd9136815560c161e6a314eb0ce41393f7db709f0d4c81e099bc5624018be2e4f3b64247c81b6249c71f504fde3c2764f055d679fce945c0d25f045e4c97c230e1a74161470f00622f9ea6c6102a021af68c12159bb1104c4542929d3b1ae27d3f70a679799df1a2057fb43a485a14f98ebdf198226010100dc05203370ee1b44e09e59c067de17503c90603cad89273db8ec6617e8be2565df9a424563750a6c535f668f05b41534661a7159b6b458c0fc4c758add982edb4f2a4ffa58d619aa890c35df0b8a1ce29345430fcb8c6183273211c722815764070c3fdc92241ae4e9d97716ea614c259e9b1da0c5d54fdf1d3d5d726a4455245ced192032e648811ffc74f669bd1805aec9603d5c1e7036b394085eef0d50a4302b14e1a858569849905ad95e1c5e2d7bd267cce64a2338056b68ab51d5331cfddd3ed6e15e775938ea73efef5a351af4be3e1d06d97336ad212d882e5c613bc1502468c01826d746bf52b00c4e6bd1ce05130fc31f0bb9787e6863880f53bc1bca5deba42c0e012ad717b8e8f06818098b580a39f846ef165f0c0c971c3ad56ed73f8ecc486b3f0fbd3076da595ad502030f71fbbd3a9256e8257c642a436f194d51c32f67669950491c07ccf2656e6e2c69702d4613a5cb472ea8b980157942050f0cb692229e8e4452fa8ab414c2734358526ab86dc275c66e5911ed0415de625b55283b640fbf790f34376359c327fa0be9633d097ac3043d4e38e012bd0a1c0c931e80717bc3733046376718bde9216870e9f407d2b3130708df265981a7df377542ff13e40d2b44aef15a41c3d7ec0c2390645cc7d2db13b06be33f67464f1bab538361c4825e3055ebde01";
const AGGREGATE_CAP: &str = "c87f2571536d12525835d0316b02531ae45d3f72449caf04ea603527667fef38785a0134256b3776a686692b69c81b3131051f778a52bb6f6b9f9c637a8dc6667fe60e303b1472741c714d536f0cda2cd546c766b335de271eed954cff69e36286fc5d6e01424b6e9038044b7d473f5a04ced8177302f610b006287529b15a310392615b458d701435bb1b31c95742040cc15a429955694c46de4a17cebd681dddf0fa056d4e72184d8bd4491d0ea7172108554811a36a40f1c80b6082050a54c53f1d64ae41d354da64ec328954cf2977afd14a6158c6778d15b074c53028287c08553c0b2351434b563f2ef3b04208ca8b2b7465d22d708ea8c46b2204375d896b6e25c812301ea842a3242f1be555316024774c13961f2e0eee2cdcb15e231aba373eee095c601c738a4a0db7aa11a36bc662cc18cb2e5ecca95cd457d87184d820713c034508e317e15d8a7a074d206e8374483d10673bb8d747db8f542293a5674be389081a7d4bec6be53f1338ef988c05dacd7a0051759d54c2baa103f3c70456ac27e406ba2457205bd2810e6fc98b6257c6eb407208772f37b0ab3c41b0e7087dbbdf47224e9b6fc468c10a4610d962dd8ac1239a2e57529b6d7e3a21921c14bd3d6d2e642a9f02fe045c5639144e408335075bef5e74302b98be6d89fd9a553ab38b738f84bf35861a6377ba4e75726c164d23ac5ef8275c2f3f23cddeb740dcd9ac585dfbca42bb7513467ddb525cd774fc6ef00dca524e6bea52c2bbe9187a98dc4097b529601907cc2f3b7595582db767209bb2e20a7d03247150eb4406cd187f355cf02919d35d8e298fd21e0770a8090f992b1e758b71f50f5dd03b5cc1e0ff4630c9b90872bd6242f0057f18c666fa4f78c1991f62636f3741d8c1638300666f4947ae39a244bc1e0c3786334a519a083254fd025cfa331878ad975962603258a6ecc92717ee8b2c7fb37310896f473558724713d526396436a69a55840a325b8205af6945b7924071813605b9d0eb077d411c36ed04dc6d0dd08521fb4e4a293fe8326588a67802d1ea6140e2b3ca119d6b6704a1f1b319844cfa687306ef51e070cd3690061d31495fee282dcdc94415fb2509064d804b306f145910119120f60cf26c41ea1c20337fad4ce476d94590e84d5e907b7d19d5628e0adfa78e482aa4d7422c58995af2be13423166485a12f37a34a39b7d0639e03a68d043ce32b4a6f105af632f629bfc6853ac5db84ca5522560b1d99a37e6997b158c4f7a1e11d11a0c0540426a7c5c515961cb56142e4b5d72d4d01d5c375eb150f0776e1d5692960cad5a2e0fa2832e393cdfc407dad0f26f9cc428273963fb492ac02a59d479c324f962002242526e51f1cbcc24d474361d5636336e575f455cc1b3e566674bda074806a92e770db80465828e1d6f09c557c1e72156";

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
    /// commitment lists -- of either kind.
    pub fn verify(&self, inputs: &[[u8; 32]], outputs: &[[u8; 32]]) -> bool {
        if !inputs.iter().chain(outputs).all(is_canonical) {
            return false;
        }
        let mut r = Bytes(&self.bytes);
        match r.take(1).map(|k| k[0]) {
            Some(KIND_DIRECT) => verify_direct(r, inputs, outputs),
            Some(KIND_TREE) => verify_tree(r, inputs, outputs),
            _ => false,
        }
    }
}

fn verify_direct(mut r: Bytes, inputs: &[[u8; 32]], outputs: &[[u8; 32]]) -> bool {
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
    let air = BlockAir::new(num_blocks, elements(inputs), elements(outputs), REWARD);
    stark::verify(&air, &proof, &PARAMS)
}

/// One chunk's input and output commitments.
type ChunkLists = (Vec<[u8; 32]>, Vec<[u8; 32]>);

/// Split the body's lists into chunks by the given chunk indices,
/// keeping body order (so each chunk's lists stay sorted). `None` if an
/// index is out of range or a chunk overflows `CHUNK_SHAPE`.
fn chunk_lists(
    count: usize,
    input_chunks: &[u16],
    output_chunks: &[u16],
    inputs: &[[u8; 32]],
    outputs: &[[u8; 32]],
) -> Option<Vec<ChunkLists>> {
    let mut chunks = vec![(Vec::new(), Vec::new()); count];
    for (&c, commitment) in input_chunks.iter().zip(inputs) {
        chunks.get_mut(c as usize)?.0.push(*commitment);
    }
    for (&c, commitment) in output_chunks.iter().zip(outputs) {
        chunks.get_mut(c as usize)?.1.push(*commitment);
    }
    chunks
        .iter()
        .all(|(i, o)| i.len() <= CHUNK_SHAPE.inputs && o.len() <= CHUNK_SHAPE.outputs)
        .then_some(chunks)
}

fn chunk_air(inputs: &[[u8; 32]], outputs: &[[u8; 32]], net: (u64, u64)) -> BlockAir {
    BlockAir::chunk(
        CHUNK_SHAPE.num_blocks,
        elements(inputs),
        elements(outputs),
        net,
        Some((CHUNK_SHAPE.inputs, CHUNK_SHAPE.outputs)),
    )
}

fn verify_tree(mut r: Bytes, inputs: &[[u8; 32]], outputs: &[[u8; 32]]) -> bool {
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
    let Some(chunks) = chunk_lists(count, &input_chunks, &output_chunks, inputs, outputs) else {
        return false;
    };
    let Some(proof) = stark::Proof::from_bytes(r.0) else {
        return false;
    };
    // A chunk's data leaves its amounts out, so any will do here.
    let airs: Vec<BlockAir> = chunks.iter().map(|(i, o)| chunk_air(i, o, (0, 0))).collect();
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
    proof.verify(inputs, outputs).then_some(proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block::BlockBody;
    use crate::output::Output;
    use crate::stark::Air;
    use crate::wots;

    fn reward_block() -> (Vec<[u8; 32]>, Vec<[u8; 32]>, Vec<Transaction>) {
        let (_, pk) = wots::keygen(&[1; 32]);
        let mut tx = Transaction::new();
        tx.add_output(Output::new(&pk, REWARD)).unwrap();
        let body = BlockBody::from_transactions(std::slice::from_ref(&tx)).unwrap();
        (body.inputs, body.outputs, vec![tx])
    }

    #[test]
    fn a_reward_proof_verifies_against_its_lists_and_no_others() {
        let (inputs, outputs, txs) = reward_block();
        let proof = prove_block(&inputs, &outputs, &txs, [1; 32]).unwrap();
        assert!(proof.verify(&inputs, &outputs));

        let mut other = outputs.clone();
        other[0][0] ^= 1;
        assert!(!proof.verify(&inputs, &other));
        assert!(!proof.verify(&inputs, &[]));
    }

    #[test]
    fn proving_refuses_lists_that_dont_match_the_transactions() {
        let (inputs, mut outputs, txs) = reward_block();
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
        let (inputs, outputs, _) = reward_block();
        assert!(!Proof::placeholder().verify(&inputs, &outputs));
        assert!(!Proof::from_bytes(vec![4, 0, 0, 0, 1, 2, 3]).verify(&inputs, &outputs));
        assert!(!Proof::from_bytes(vec![3, 0, 0, 0]).verify(&inputs, &outputs));
    }

    #[test]
    fn tree_proof_headers_are_checked_before_anything_expensive() {
        let (inputs, outputs, _) = reward_block();
        // Truncated header, zero chunks, an out-of-range chunk index.
        let mut header = vec![KIND_TREE];
        header.extend(REWARD.to_le_bytes());
        header.extend(0u64.to_le_bytes());
        assert!(!Proof::from_bytes(header.clone()).verify(&inputs, &outputs));
        let mut zero = header.clone();
        zero.extend(0u16.to_le_bytes());
        zero.extend(0u16.to_le_bytes());
        assert!(!Proof::from_bytes(zero).verify(&inputs, &outputs));
        let mut out_of_range = header;
        out_of_range.extend(1u16.to_le_bytes());
        out_of_range.extend(5u16.to_le_bytes());
        assert!(!Proof::from_bytes(out_of_range).verify(&inputs, &outputs));
    }

    #[test]
    fn chunks_overflowing_their_shape_are_refused() {
        let commitment = |k: u8| [k; 32];
        let inputs: Vec<[u8; 32]> = (0..=CHUNK_SHAPE.inputs as u8).map(commitment).collect();
        let all_in_one = vec![0u16; inputs.len()];
        assert!(chunk_lists(1, &all_in_one, &[], &inputs, &[]).is_none());
        let mut split = all_in_one;
        split[0] = 1;
        let chunks = chunk_lists(2, &split, &[], &inputs, &[]).unwrap();
        assert_eq!((chunks[0].0.len(), chunks[1].0.len()), (CHUNK_SHAPE.inputs, 1));
        // Body order is kept within each chunk.
        assert_eq!(chunks[0].0[0], commitment(1));
    }

    /// `count` single-input spends (each paying a fee of 10) and the reward
    /// transaction claiming the reward plus all fees.
    fn spends(count: u8) -> (Vec<[u8; 32]>, Vec<[u8; 32]>, Vec<Transaction>) {
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
        (body.inputs, body.outputs, txs)
    }

    #[test]
    fn the_reference_rule_uses_a_tree_beyond_one_chunk_of_inputs() {
        assert!(!prefers_tree(0) && !prefers_tree(10));
        assert!(prefers_tree(11) && prefers_tree(10_000));
    }

    #[test]
    fn transactions_partition_into_chunks_in_order() {
        let (_, _, txs) = spends(12);
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
        let (inputs, outputs, txs) = spends(11);
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
        assert!(proof.verify(&inputs, &outputs));
        println!("verified in {:.2?}", start.elapsed());
        // Other lists, or a different claimed split of the totals.
        let mut other = outputs.clone();
        other.swap(0, 1);
        assert!(!proof.verify(&inputs, &other));
        let mut bytes = proof.as_bytes().to_vec();
        bytes[1] ^= 1; // A
        bytes[9] ^= 1; // B, keeping A - B
        assert!(!Proof::from_bytes(bytes).verify(&inputs, &outputs));
        // The reference rule makes a small block's proof direct.
        let (i, o, t) = spends(2);
        let small = prove_block_auto(&i, &o, &t, [5; 32]).unwrap();
        assert!(!small.is_tree() && small.verify(&i, &o));
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
        let (inputs, outputs, txs) = spends(count);
        let time = std::time::Instant::now;
        match case.as_str() {
            "direct" => {
                let witness = block_air::build(&txs, REWARD).unwrap();
                let start = time();
                let proof = prove_block(&inputs, &outputs, &txs, [1; 32]).unwrap();
                let proving = start.elapsed();
                let start = time();
                assert!(proof.verify(&inputs, &outputs));
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
