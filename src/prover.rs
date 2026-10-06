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
//! already used by `state_tree`/`utxo`: this module doesn't need to know
//! `BlockBody`'s specific shape, just the commitments it's attesting
//! about. It also avoids a dependency cycle: `BlockBody` holds a `Proof`
//! (see that module's docs), so `Proof` can't be defined in terms of
//! `BlockBody`.
//!
//! The miner proves every transaction in its block itself, from their
//! plaintext -- see `docs/BLOCK_TODO.md` #1.

#![allow(dead_code)]

use crate::recovery::NONCE_LEN;
use crate::aggregate::{self, ChunkTransition, Key, StateChange, TreeParams, VerifyingKey};
use crate::block_air::{self, BlockAir, ChunkShape};
use crate::poseidon2::{BabyBear, P, digest_from_bytes, hash_bytes_32};
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

/// Every proof starts with its kind. (Kind 0, a direct proof of the
/// whole block in one trace, was retired: a chain step can only verify
/// one fixed proof shape -- `docs/CHAIN_RECURSION.md`.)
const KIND_TREE: u8 = 1;

/// An encoded block proof -- what's published and hashed into
/// `body_hash`, decoded only to verify. The block's transactions are
/// proven in chunks (`CHUNK_SHAPE`), each chunk's proof wrapped together
/// with the chunk's state transition, and the wraps aggregated
/// (`aggregate`) -- encoded as: the kind (`KIND_TREE`), the root's amount
/// totals `A`, `B` (`u64`s; `A - B` must be `REWARD`), the chunk count
/// (`u16`), every input's and then every output's chunk (`u16` each, in
/// body order), and the root `stark::Proof`.
///
/// It attests that the body's commitments are authorized and balance,
/// **and** that applying them -- chunk by chunk, inputs spent, outputs
/// appended in chunk order -- takes the parent's state (`state_tree`
/// root and output count) to the block's.
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

/// Every chunk's shape: up to 8 inputs and 20 outputs, padded to 2^17
/// rows (4096 blocks). Also the most one transaction may have, since a
/// transaction is proven whole in one chunk. Sized so the wrap circuit --
/// which verifies the chunk proof *and* applies the chunk's 28 state
/// updates -- fits the tree's 2^18 rows.
pub const CHUNK_SHAPE: ChunkShape = ChunkShape {
    num_blocks: 4096,
    inputs: 8,
    outputs: 20,
};

/// Chunk proofs use the block parameters (zero knowledge: their witness
/// is the transactions).
pub const CHUNK_PARAMS: Params = PARAMS;

/// The dev network's parameters (`network`): blowup 4, 8 queries, no
/// grinding -- about 16 bits of soundness. **Not secure**; for testing
/// only, where they make proving several times faster.
pub const DEV_PARAMS: Params = Params {
    log_blowup: 2,
    num_queries: 8,
    grinding_bits: 0,
    hiding: true,
};

/// The dev network's tree proofs: the same lightening, and half the rows
/// (fewer queries make the verifier circuits small enough).
pub const DEV_TREE: TreeParams = TreeParams {
    trace_len: 1 << 17,
    params: Params {
        log_blowup: 2,
        num_queries: 8,
        grinding_bits: 0,
        hiding: false,
    },
};

/// The chunk proofs' parameters on this node's network.
pub fn chunk_params() -> Params {
    match crate::network::current() {
        crate::network::Network::Main => CHUNK_PARAMS,
        crate::network::Network::Dev => DEV_PARAMS,
    }
}

/// The tree proofs' size and parameters on this node's network.
pub fn tree() -> TreeParams {
    match crate::network::current() {
        crate::network::Network::Main => TREE,
        crate::network::Network::Dev => DEV_TREE,
    }
}

/// `log2` of tree proofs' low-degree extension: the trace, times the
/// composition factor (4), times the blowup.
fn tree_log_lde() -> usize {
    let t = tree();
    t.trace_len.trailing_zeros() as usize + 2 + t.params.log_blowup
}

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


/// The verifying keys: the wrap and aggregation circuits' preprocessed
/// caps, as hex. Derived from the circuits (see the `tree_keys` test,
/// which regenerates them); any change to those circuits changes these.
const WRAP_CAP: &str = "afb2257750e6971509069a77563a73227ad0e15fb5401a09d639a906bc7ba2710f658927aadc762226170509e14e903e635c3814e9be4f431b0ea46da85c631c1b1b6f0f76c6081fb9dec31c622e8749e92118389c80d94d3b03e82e962cf80ad210ad481fc8385c41cbfc1320286a4c9241b92c67764201570a2c3b4de1286084f4052bdfea616fb1cce65462121e51ee62eb6aa8a0ff3f85075725a8e0804541935015fa0174224096b1662392b600db78ec264d0ea220c1f09e210fc8ba4257245c0a9ad5e154b66ca140b65e3c3a8028ca1f92bfaa578dd7675103d0685dae7e5a350b5b6207f798a627b5b8ec4d4a6b525ec308a53db77383068e74690bce5c5a3041b74776b1dae05bfb5b3e46461e231e3eb7fc2f8ab08c3063cf7d0994634e55ead5d7442828a50f4bcef2310d248e6f82eca036bb6dcd4479dc2d02bd4b491eb0b52a6f9b32c05a097d8b103c2f9c24e07f790aba321620e0fff06500fef302ee51900357111f1ab95a276637fadc5ad815035ed66e116d37885420bb28b85b3eb08976b2f6f6671c72e0201fb94d50cbf84c46e5be1e0f24a0ca69b6330305c9799606c3503966e708cb59811174163ba4e62fb1ef385cf7914a77473a0218452c620bda402433049d3d04cf54b04ce2660d168ce2a13571d8ac67c46a6e3bc3ad1119ca2a873072603e1783345950c1ceff5caf95b61596246501bfe95b054950a656e4ea932e8f7d1143a23954495bf73903b6a42416f22c06639046912fd5253d3f74e8404ed3617212e76d4a0169f445679ca7a523dc7f85134e248126454427313f2e185728bcf74626985270ae60c8751196f11377a8886c35552c6645803d5fa9ef441940f292518288154d03e76442511fe82c43d2024fc42ca32505d3f204ed51b2013fbcfd336bba1e32a8e6390afbcbae17f0c92a2f758f6658a05f6477b8ce535422958f3c2de6a94a6f37ce1206f96555d054ea58381e4450ef6eda748c38e0427d27f360fdec7d5da1929215ca8b9247ecdba854079c1e5b0591d55a1bf844445c5b22742edab43ff426dc6c6b8fba518b482725560e00352ba6dc03477320577fbe312802acad33b0a503597bb6605248fa435b4283621dc8c0783bcd76e7562640d9266a4996228b9702062a417b1d595ddf3e499790600a275a0ace0eda0f5732d76fa7d6831fed8e231b41f597665d6ba05fd4c1f762beb1696d4133d22141cdae26a8ca6812538075105a0f35429587a60dd41927083b442b5b0a271d61408c2131fa1d7036f66025179cc0b53c0f3bdf5a071299619beb061570d46a036b3f68742b061c053d31c55293d9d13aff7c4544eb2ea13a388a1337c6919300a2b42244d67ac65f4a721a4ad79d956fb03c16163d51dd761b596520e3750d1af0983a1b66edae65b2d19953afa2aa6947de913e";
const AGGREGATE_CAP: &str = "c8666b02152ab74925db740796d448599c6a1733c35cfd00ecad83391d31cc4742f5fd1bcfda622750dc324e110b72013bf26f1c0283ec04f652cf741583f76162932757217f9629add59429740cdd14892cce77fcc0501aaf87bc47fea958110da3cf6b0b5aa315a9174453df89613c81aaa60ac16fa4731bf9d146df17c75e2cc144715800a910f00d7c365c2a0950e10c293c4c0fe3016f69005fe78b941579ad6721da0c020535ccb476b8cfc23630789738457a234669d961449e53721ebe05a21265293e37cf1428615509fc71b3c6310d38313e4a02afc921b96df43b9054496cb6ec5f4d91dae3662cb38e2112b67462a002d75d40309c55a63fda6eab9983127786b832e02213021a5f037283e98e29908fdd4e6361912ebba60433ce9dd865c1ca3212530d2b6d4afd9b40f761f652dd3fd8594247af7351336d0a24f217485d1d75635d0dad5678e72967c954f6408c076e34ab41142d71462a1017ad37354de63165c29c4f37b3c3ff5aace7c200785782348212e03be34e6d0f5b5a946fbced985e8e7147556d61bf224bcfc0620eccc768e76e1a290adaee1e37947107e1d3094f36e451527111120792569065de8ea40fa7519b28fe96a417b1f3dc3af287680009da49739e22f103ed9f58738531346e22e771706884ad59dc9c131213aa93742f941b20bfff5770430c083ec53a23555296e574240ee7262d7e2b4085c3533f39a686751ca272496818a54ba6ff811fdd45215ea034865580c9b71cea5eab0f074ae13d99304e7293915170570c0b6a9a87ae0da3f08365647e0310925e4223ad5df34eb42dc26e4175773556abb12097aa3821ea00c955a8f7316338f26149847035368385731b247c712166365f507f80574c440f3b1c3b3f556f592fcd58c0eb840c26edc3734626e2261b4f680a95c2f5292dcd877415ade800fc95290ff8d0b56817b7562be276cf1bf654cd5b251c0500b209a6457b8d515a6614a303ad3ddc43dbbca5255a16ff2f3632af3e136f7b1bac28495c1abd0a216b132d220723c35bb22fca39d889a2218d5fb759cf48392c8ed1f037ce0ef708a9ccd708ae737a56b710f86c970c902968a3d4197819ad2ab9225b701c00c655566f814d4f81a4205505ed42807df40f5770246d2f57584fd0adfa4601d81c070764bb44f2f5894559fb5f0f4bd22f6426de93251db9744c3707854ce6259a2fdaf00d2311d833252d999319cce5a15d3821846f8c8f6a25861d657103505a2646ed140bd54fd312d59d190f8e523c67b0487a645a47a066a80b962025535e010dd869096585e54debe11e522f792509d0b02377cfc6c01e185bf65d5dd2432f6db85044c134cc610eb9e26a8cb62c421eaed649ca35e911050d543a8bf1c26d5de9b400ee26c04343e6443883ca734727f51c1ff078a10157cd711c";

fn cap_from_hex(hex: &str) -> Vec<[u8; 32]> {
    let bytes: Vec<u8> = (0..hex.len() / 2).map(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap()).collect();
    bytes.chunks_exact(32).map(|c| c.try_into().unwrap()).collect()
}

fn cap_to_hex(cap: &[[u8; 32]]) -> String {
    cap.iter().flatten().map(|b| format!("{b:02x}")).collect()
}

/// The dev network's verifying keys (`tree_keys` with `NETWORK=dev`).
const DEV_WRAP_CAP: &str = "cc5a4f67868db3106fbbdb12bbba21134d972141214c922ba8c4e6141aed205d3ba5f715ccd06b6238d0a763dbf5ee571f1e6802edc23008fdab704c03cc086323ecd537cc80610813f144026da7a343591e180b23a6f93349cae16fbe08a85ef59d530e9fa472710623b067fe68d103437afa61b5c43c3ac2ca4c316674450a271bf70bbbfa541cb132c852afcf2c63ffec2249e51639521924b90884c02a5065c0cc6460ddbd589f3aad511d599d17040b8a08ec0a636f97824a1ff815c7187d504f5e3f824f7723295342d967bf26ac0e561bda4dbd53a21d9d7408776776240bc06a2c515566ea7eb77460bb592d3359f70ae10be809ee53802bbe417d05c0515d65c734c0276a1df72b7bae6c591d63a53129370d017eb3a468f214495801246b4579452a68983496547bf00d4ef553106874521f3510bd6c1584b895663214e62e4105e61d0980b675a155914012eded1f47652919b31218630cdb8e37cde1241096d89456269e6b3ded7b7f1a22f9bd089c74280711568747435e04413c1f1f37317f6c16553dec254f87b350b8012e6f7b576556a0ee6e43b7910c47b9d8e45a82def732f9601a606307455da76324546932f832b88ba20839271d6c5a720605274e436c17aa624745185e4d96dcd74bb9adb864924da676797ab57582738d527703864e81c1751563a41056fa2d913bc4c6750a4cfdb261bb7f880b8e1a8f0b06fe86404dccef1eb2ac5164aa79115485a54a08cc3c17760662dd07feb2a977b74f69222b352277091eb85d32215f70868b5f24a9b71710f5deba2b8413bd660f4458549267075cc9ac3b512e60a538a391890247c76d253382702febb8272992edaa0d62ba1520510d9e63329acd1e3e419c50986e052fb64de566baef411e63a4386643c0dd341d71440a50c61e043ff5fa28e3356a77b0d747618873df771ab3f20cec14fc44336474740366bd03a5fa5f68590b613bb03a92775d878361f4d30c66916a341868535f317199ce276b430d3d93b7d92828cdff5f2af090020f43db52ad8f62718466063ca8b78e2514986e0d94f0d96d54c48249e7d1472e79ff5f08fa201f1260782d348dca76469ffcf239ec346a15f32648468b6df033f30012323581b74915432f66accaa159651992327daa4024467bbd1f2358480da377c907c985e0055c224d723b8657116b8d66621154131505cd2502a1ac7526edd7853ccd4b8a0d03fed85802b029645ef0522cae27da138423073acd7f233c11b97c4c7126d818d9d3cb180120743dcab1743747be7b42067e1e3e1a6c4e0e6eef3826693d9474544e6026c773a14445caa4124e1e72485b74b80185cba271530d4c2228be48165f150c0c57269b17816c9f2aafd165593facaf4aa8b62c059bb9144e72267c5b8b9d401dbecb9c39e37019264bbb20501dea5a47";
const DEV_AGGREGATE_CAP: &str = "60cf2341168c566b039bfe469168ac4a4069d6446df10e0ffe1d27590fffbf6ccb72904222b17c776e7e756a933cc51989e8024d2dcb6119966b8b23ed7f1146237e88756c602b7652349107c5a6e8570ad99d143a442a66f9413d293cfa451ee558462b0a46467153777f42145d585c33a4d655bfe0f864d2bc3632a65eaa185473c8536300a32d94171a09737f9f43081a223ba7d9243947264e4e6009b127dbfa2d0cf152d55def59f43016d1626df690833d24020c1dcd91c969efd1e84067c2176751832f105ca7551007b8576dbaf6dd449206641fd4321f0803473c1692df832ff5435f15b415606e945eb842461de3176a22336e9403f8246205ef3c54a968332f37805d298c2321289a5c677c533b4ee6397726f847381106e3880031d93d3506d3cc67fe679409d3193f76ec9114526f9ede237c1e0c4bc11f297015cbd94f90198a5cc8273b33ee15584849899f37500ba95c8cf8b540b670a93a3489cc52eaa6896948aad83560472444eb8d732e0c64c61cd8025c062c777768e897e46e07aecf6fba0445449a119f772e1633651e817050af2d762fff06c4376e60573e580241444572ed73e6866b5eae8a5d216478c43ba65ee2548b71e4597eae465e7617a3052468cc5a77a8d96e9ba910662f1fdc4f789071629480213a09353a23bc9d5a4d05126152310fa60e71cbeb543bed9962fad287313d5e6f2d73434d6ca6bcb660f483df47322ef12782bf80585257f663db35d05420f55e0c822f273cf0303f0447ea6162ed357e078f9980299cdd1f6dabe0f2402b829d45398cbf54049a1b223c397d5259fdd5212b2b466289a2373f5903645dfca5c12301ed1a37f7bd4e744fb7463f5f0d917561696c27ec8a8e60c919b75cf5541e1f9216ab28050f2d250567aa3061b54633c8602f4d1a01921a70e05821df14e14837e7da684ae5202ba45aa020d5e7d82d5d886811adbb7365a6b2616fdf8ab64c9329244b4127f256791323506fc5950e86c02d670bf51356a9c8e45a8ff60a38c465a829624e78571cd69330fc5f7f6d886d811f17b3d15ef890b421f2d41607dfd87e021278cc077eae78258a888c6bb716e10b3d970a0964ff112b09375f62ab9d8a4fe234544d0f6f625cb7eb303d63409f0c816bfe3c094d530294c0693750f5863a907b4a68ac77932abd86c5644860521e70dda1238f2a225e27fcdf6262c66f397362b209d9512f564a70f1382f67220db872e50ebd3973109ea25f34c10d9700157a777473ba670198c5720928352b0d89ca9f0eac7f3f709f1aab6406cddc0614171202fe5d12189d35b423a9dd3e0e3048220238d6ce0872f64e2a1d5d8b75f6e62868473c9544e438522efce93d15f0c3ae10c56d64472a0d126d1b2d3a53cb82f6184f031e129f176d12df0d8c0257901d605e96106611756619";

/// This network's verifying key for tree proofs.
pub fn tree_verifying_key() -> VerifyingKey {
    let (wrap, aggregate) = match crate::network::current() {
        crate::network::Network::Main => (WRAP_CAP, AGGREGATE_CAP),
        crate::network::Network::Dev => (DEV_WRAP_CAP, DEV_AGGREGATE_CAP),
    };
    VerifyingKey {
        wrap_cap: cap_from_hex(wrap),
        aggregate_cap: cap_from_hex(aggregate),
        log_lde: tree_log_lde(),
        tree: tree(),
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

    /// Whether this is a tree proof (else garbage).
    pub fn is_tree(&self) -> bool {
        self.bytes.first() == Some(&KIND_TREE)
    }

    /// Which chunk each of the body's inputs and outputs is in -- the
    /// order the state applies them in (chunk by chunk) -- as each chunk's
    /// indices into the body's lists, body order within each. `None` if
    /// the proof's header doesn't parse for lists of these lengths.
    pub fn chunk_assignment(&self, inputs: usize, outputs: usize) -> Option<Vec<(Vec<usize>, Vec<usize>)>> {
        let (_, count, input_chunks, output_chunks, _) = parse_header_and_rest(&self.bytes, inputs, outputs)?;
        let mut chunks = vec![(Vec::new(), Vec::new()); count];
        for (i, &c) in input_chunks.iter().enumerate() {
            chunks[c as usize].0.push(i);
        }
        for (o, &c) in output_chunks.iter().enumerate() {
            chunks[c as usize].1.push(o);
        }
        Some(chunks)
    }

    /// An empty stand-in proof, for tests about everything *but* proofs
    /// (forks, retargeting, sync), whose chains skip proof checks.
    #[cfg(test)]
    pub fn placeholder() -> Self {
        Proof::default()
    }

    /// A proof with only a header -- the chunk each of the body's inputs
    /// and outputs is in -- and no STARK proof: for chains that skip
    /// proof checks (tests), so a block still says the order its outputs
    /// are appended in. Never valid.
    pub fn header_only(inputs: usize, outputs: usize, body_chunks: &[(Vec<usize>, Vec<usize>)]) -> Self {
        let (mut input_chunks, mut output_chunks) = (vec![0u16; inputs], vec![0u16; outputs]);
        for (k, (ins, outs)) in body_chunks.iter().enumerate() {
            for &i in ins {
                input_chunks[i] = k as u16;
            }
            for &o in outs {
                output_chunks[o] = k as u16;
            }
        }
        let mut bytes = vec![KIND_TREE];
        bytes.extend([0u8; 16]);
        bytes.extend((body_chunks.len() as u16).to_le_bytes());
        for c in input_chunks.iter().chain(&output_chunks) {
            bytes.extend(c.to_le_bytes());
        }
        Proof { bytes }
    }

    /// What `BlockBody::body_hash` folds in to commit to the proof.
    pub fn commitment_hash(&self) -> [u8; 32] {
        hash_bytes_32(&self.bytes)
    }

    /// Whether this proves the block statement for exactly these public
    /// commitment lists and outputs' recovery nonces (`nonces[i]` is
    /// `outputs[i]`'s), with the state moving as `state` says.
    pub fn verify(&self, inputs: &[[u8; 32]], outputs: &[[u8; 32]], nonces: &[[u8; NONCE_LEN]], state: &StateChange) -> bool {
        if !inputs.iter().chain(outputs).all(is_canonical) || nonces.len() != outputs.len() {
            return false;
        }
        verify_tree(&self.bytes, inputs, outputs, nonces, state)
    }
}

/// A tree proof's header: amounts, chunk count, every input's and every
/// output's chunk; and the root proof's bytes.
type Header<'a> = ((u64, u64), usize, Vec<u16>, Vec<u16>, &'a [u8]);

fn parse_header_and_rest(bytes: &[u8], inputs: usize, outputs: usize) -> Option<Header<'_>> {
    let mut r = Bytes(bytes);
    if r.take(1)? != [KIND_TREE] {
        return None;
    }
    let amounts = (r.u64()?, r.u64()?);
    let count = r.u16()? as usize;
    let input_chunks: Vec<u16> = (0..inputs).map(|_| r.u16()).collect::<Option<_>>()?;
    let output_chunks: Vec<u16> = (0..outputs).map(|_| r.u16()).collect::<Option<_>>()?;
    if count == 0 || input_chunks.iter().chain(&output_chunks).any(|&c| c as usize >= count) {
        return None;
    }
    Some((amounts, count, input_chunks, output_chunks, r.0))
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

/// A block proof's tree root, as a chain step verifies it
/// (`chain_step`): for this body and state change. `None` if the proof
/// doesn't parse; whether it verifies is `Proof::verify`'s question.
pub fn block_root(proof: &Proof, inputs: &[[u8; 32]], outputs: &[[u8; 32]], nonces: &[[u8; NONCE_LEN]], state: &StateChange) -> Option<aggregate::Node> {
    let (amounts, count, input_chunks, output_chunks, rest) = parse_header_and_rest(&proof.bytes, inputs.len(), outputs.len())?;
    let chunks = chunk_lists(count, &input_chunks, &output_chunks, inputs, outputs, nonces)?;
    let root = stark::Proof::from_bytes(rest)?;
    let airs: Vec<BlockAir> = chunks.iter().map(|(i, o, n)| chunk_air(i, o, n, (0, 0))).collect();
    tree_verifying_key().root(&airs, amounts, state, root)
}

fn verify_tree(bytes: &[u8], inputs: &[[u8; 32]], outputs: &[[u8; 32]], nonces: &[[u8; NONCE_LEN]], state: &StateChange) -> bool {
    let Some((amounts, count, input_chunks, output_chunks, rest)) = parse_header_and_rest(bytes, inputs.len(), outputs.len()) else {
        return false;
    };
    let Some(chunks) = chunk_lists(count, &input_chunks, &output_chunks, inputs, outputs, nonces) else {
        return false;
    };
    let Some(proof) = stark::Proof::from_bytes(rest) else {
        return false;
    };
    // A chunk's data leaves its amounts out, so any will do here.
    let airs: Vec<BlockAir> = chunks.iter().map(|(i, o, n)| chunk_air(i, o, n, (0, 0))).collect();
    tree_verifying_key().verify_block(&airs, amounts, REWARD, state, &proof)
}

/// How a block's transactions are proven: grouped, in order, into chunks
/// (`plan_chunks`), and each chunk's state transition -- what
/// `chain::Chain::build_block` works out against the parent's state.
#[derive(Clone, Debug)]
pub struct BlockPlan {
    /// Each chunk's transactions, as indices into the block's list.
    pub chunks: Vec<Vec<usize>>,
    /// Each chunk's commitments, as indices into the body's input and
    /// output lists (body order within each).
    pub body_chunks: Vec<(Vec<usize>, Vec<usize>)>,
    pub transitions: Vec<ChunkTransition>,
}

/// Group transactions, in order, into chunks that fit `CHUNK_SHAPE`, as
/// indices; `None` if one doesn't fit even alone (consensus: no
/// transaction may have more inputs or outputs than a chunk holds).
pub fn plan_chunks(transactions: &[Transaction]) -> Option<Vec<Vec<usize>>> {
    let mut chunks: Vec<Vec<usize>> = Vec::new();
    let (mut ins, mut outs) = (usize::MAX, usize::MAX);
    for (t, tx) in transactions.iter().enumerate() {
        let (i, o) = (tx.inputs.len(), tx.outputs.len());
        if i > CHUNK_SHAPE.inputs || o > CHUNK_SHAPE.outputs {
            return None;
        }
        if chunks.is_empty() || ins + i > CHUNK_SHAPE.inputs || outs + o > CHUNK_SHAPE.outputs {
            chunks.push(Vec::new());
            (ins, outs) = (0, 0);
        }
        chunks.last_mut().unwrap().push(t);
        (ins, outs) = (ins + i, outs + o);
    }
    Some(chunks)
}

/// The tree circuits' proving keys -- derived from the first block this
/// process proves (their fixed columns don't depend on which), then kept.
struct TreeKeys {
    wrap: Key,
    aggregate: Option<Key>,
}

static TREE_KEYS: std::sync::Mutex<Option<TreeKeys>> = std::sync::Mutex::new(None);

/// Prove the block whose body is `inputs`/`outputs`/`nonces`, from its
/// `transactions` (each fully signed) and `plan`: chunk proofs, wraps
/// (each applying its chunk to the state), aggregation. `seed` must be
/// fresh random bytes for every proof (it's what keeps chunk proofs
/// zero-knowledge). `None` if the transactions don't verify, don't
/// balance against `REWARD`, or don't match the body or the plan.
pub fn prove_block(
    inputs: &[[u8; 32]],
    outputs: &[[u8; 32]],
    nonces: &[[u8; NONCE_LEN]],
    transactions: &[Transaction],
    plan: &BlockPlan,
    seed: [u8; 32],
) -> Option<Proof> {
    prove_block_with_root(inputs, outputs, nonces, transactions, plan, seed).map(|(proof, _)| proof)
}

/// `prove_block`, also returning the tree's root proof itself -- what a
/// chain step (`chain_step`) verifies.
pub fn prove_block_with_root(
    inputs: &[[u8; 32]],
    outputs: &[[u8; 32]],
    nonces: &[[u8; NONCE_LEN]],
    transactions: &[Transaction],
    plan: &BlockPlan,
    seed: [u8; 32],
) -> Option<(Proof, aggregate::Node)> {
    if plan.chunks.len() != plan.transitions.len() || plan.chunks.is_empty() {
        return None;
    }
    let derive = |k: u16| {
        let mut s = seed;
        s[31] ^= k as u8;
        s[30] ^= 0x5a ^ (k >> 8) as u8;
        s
    };
    // Each chunk's net: what its outputs take beyond its inputs (a), or
    // the reverse (b) -- its share of reward and fees. All laid out (and
    // checked against the body) before any proving.
    let mut witnesses = Vec::with_capacity(plan.chunks.len());
    let mut totals = (0u128, 0u128);
    for indices in &plan.chunks {
        let txs: Vec<Transaction> = indices.iter().map(|&i| transactions.get(i).cloned()).collect::<Option<_>>()?;
        let spent: u128 = txs.iter().flat_map(|t| &t.inputs).map(|i| i.amount as u128).sum();
        let created: u128 = txs.iter().flat_map(|t| &t.outputs).map(|o| o.amount as u128).sum();
        let net = if created >= spent {
            (u64::try_from(created - spent).ok()?, 0)
        } else {
            (0, u64::try_from(spent - created).ok()?)
        };
        totals = (totals.0 + net.0 as u128, totals.1 + net.1 as u128);
        witnesses.push(block_air::build_chunk(&txs, net, CHUNK_SHAPE).ok()?);
    }
    // The block must claim exactly the reward (plus fees, which cancel).
    if totals.0.checked_sub(totals.1) != Some(REWARD as u128) {
        return None;
    }

    // Each body commitment's chunk.
    let mut chunk_of: std::collections::HashMap<[u8; 32], u16> = Default::default();
    for (k, w) in witnesses.iter().enumerate() {
        for c in w.air.public_inputs().iter().chain(w.air.public_outputs()) {
            chunk_of.insert(crate::poseidon2::digest_to_bytes(*c), k as u16);
        }
    }
    let input_chunks: Vec<u16> = inputs.iter().map(|c| chunk_of.get(c).copied()).collect::<Option<_>>()?;
    let output_chunks: Vec<u16> = outputs.iter().map(|c| chunk_of.get(c).copied()).collect::<Option<_>>()?;
    if chunk_of.len() != inputs.len() + outputs.len() {
        return None; // the transactions' commitments aren't exactly the body's
    }

    let mut chunks = Vec::with_capacity(witnesses.len());
    for (k, w) in witnesses.into_iter().enumerate() {
        let proof = stark::prove(&w.air, &w.trace, &chunk_params(), derive(k as u16)).ok()?;
        chunks.push((w.air, proof));
    }

    let mut keys = TREE_KEYS.lock().unwrap();
    if keys.is_none() {
        let (air, proof) = &chunks[0];
        let wrap = aggregate::wrap_key(air, proof, &plan.transitions[0], &chunk_params(), &tree()).ok()?;
        *keys = Some(TreeKeys { wrap, aggregate: None });
    }
    let keys = keys.as_mut().unwrap();
    let mut wraps = Vec::with_capacity(chunks.len());
    for (k, ((air, proof), transition)) in chunks.iter().zip(&plan.transitions).enumerate() {
        wraps.push(aggregate::wrap(&keys.wrap, air, proof, transition, &chunk_params(), &tree(), derive(0x8000 | k as u16)).ok()?);
    }
    let root = if wraps.len() == 1 {
        wraps.pop().unwrap()
    } else {
        if keys.aggregate.is_none() {
            keys.aggregate = Some(aggregate::aggregate_key([&wraps[0], &wraps[1]], &keys.wrap, &tree()).ok()?);
        }
        aggregate::aggregate_all(keys.aggregate.as_ref().unwrap(), &keys.wrap, wraps, &tree(), derive(0xffff)).ok()?
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
    // proof this miner publishes invalid.
    let proof = Proof { bytes };
    let state = StateChange {
        root_in: plan.transitions[0].change.root_in,
        count_in: plan.transitions[0].change.count_in,
        root_out: plan.transitions.last().unwrap().change.root_out,
        count_out: plan.transitions.last().unwrap().change.count_out,
    };
    proof.verify(inputs, outputs, nonces, &state).then_some((proof, root))
}

/// This network's tree circuits' verifying keys (`aggregate::vk_digest` of
/// each cap): `(wrap, aggregate)` -- what a chain step accepts a block's
/// root proof by.
pub fn tree_vks() -> (crate::circuit::Octet, crate::circuit::Octet) {
    let vk = tree_verifying_key();
    (aggregate::vk_digest(&vk.wrap_cap), aggregate::vk_digest(&vk.aggregate_cap))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block::BlockBody;
    use crate::output::Output;
    use crate::poseidon2::digest_from_bytes;
    use crate::stark::Air;
    use crate::wots;

    /// A block: its body's lists, its transactions, and how to prove it
    /// against a state that holds its inputs (with zero nonces) -- what
    /// `chain::Chain::build_block` works out against the real state.
    struct TestBlock {
        inputs: Vec<[u8; 32]>,
        outputs: Vec<[u8; 32]>,
        nonces: Vec<[u8; NONCE_LEN]>,
        txs: Vec<Transaction>,
        plan: BlockPlan,
        state: StateChange,
    }

    fn block(txs: Vec<Transaction>) -> TestBlock {
        use crate::state_circuit::MemTree;
        use crate::state_tree::compress_leaf;
        let body = BlockBody::from_transactions(&txs).unwrap();
        let chunks = plan_chunks(&txs).unwrap();
        let zero = [0; NONCE_LEN];
        let leaf = |c: &[u8; 32], n: &[u8; NONCE_LEN]| compress_leaf(&digest_from_bytes(c), &crate::output::nonce_limbs(n));
        let mut tree = MemTree::default();
        for c in &body.inputs {
            tree.append(leaf(c, &zero));
        }
        let (root_in, count_in) = (tree.root(), tree.count());
        let mut transitions = Vec::new();
        let mut body_chunks = Vec::new();
        for indices in &chunks {
            let mut ins: Vec<[u8; 32]> = indices.iter().flat_map(|&t| &txs[t].inputs).map(|i| Output::new(&i.pubkey, i.amount).commitment()).collect();
            let mut outs: Vec<([u8; 32], [u8; NONCE_LEN])> = indices.iter().flat_map(|&t| &txs[t].outputs).map(|o| (o.commitment(), o.nonce)).collect();
            ins.sort();
            outs.sort();
            body_chunks.push((
                ins.iter().map(|c| body.inputs.binary_search(c).unwrap()).collect(),
                outs.iter().map(|(c, _)| body.outputs.binary_search(c).unwrap()).collect(),
            ));
            let (root, count) = (tree.root(), tree.count());
            let mut t_inputs = Vec::new();
            for slot in 0..CHUNK_SHAPE.inputs {
                match ins.get(slot) {
                    Some(c) => {
                        let p = tree.position_of(&leaf(c, &zero)).unwrap();
                        t_inputs.push((p, zero, tree.path(p)));
                        tree.spend(&leaf(c, &zero));
                    }
                    None => t_inputs.push((tree.count(), zero, tree.path(tree.count()))),
                }
            }
            let mut t_outputs = Vec::new();
            for slot in 0..CHUNK_SHAPE.outputs {
                t_outputs.push(tree.path(tree.count()));
                if let Some((c, n)) = outs.get(slot) {
                    tree.append(leaf(c, n));
                }
            }
            transitions.push(ChunkTransition {
                change: StateChange { root_in: root, count_in: count, root_out: tree.root(), count_out: tree.count() },
                inputs: t_inputs,
                outputs: t_outputs,
            });
        }
        TestBlock {
            inputs: body.inputs.clone(),
            outputs: body.outputs,
            nonces: body.nonces,
            txs,
            plan: BlockPlan { body_chunks, chunks, transitions },
            state: StateChange { root_in, count_in, root_out: tree.root(), count_out: tree.count() },
        }
    }

    fn reward_tx(amount: u64) -> Transaction {
        let (_, pk) = wots::keygen(&[1; 32]);
        let mut tx = Transaction::new();
        tx.add_output(Output::new(&pk, amount)).unwrap();
        tx
    }

    /// `count` single-input spends (each paying a fee of 10) and the reward
    /// transaction claiming the reward plus all fees.
    fn spends(count: u8) -> Vec<Transaction> {
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
        txs
    }

    #[test]
    fn proving_refuses_lists_that_dont_match_the_transactions() {
        let mut b = block(vec![reward_tx(REWARD)]);
        b.outputs[0][0] ^= 1;
        assert!(prove_block(&b.inputs, &b.outputs, &b.nonces, &b.txs, &b.plan, [1; 32]).is_none());
    }

    #[test]
    fn proving_refuses_a_block_that_overclaims_the_reward() {
        let b = block(vec![reward_tx(REWARD + 1)]);
        assert!(prove_block(&b.inputs, &b.outputs, &b.nonces, &b.txs, &b.plan, [1; 32]).is_none());
    }

    #[test]
    fn garbage_and_placeholder_proofs_dont_verify() {
        let b = block(vec![reward_tx(REWARD)]);
        for proof in [Proof::placeholder(), Proof::from_bytes(vec![4, 0, 0, 0, 1, 2, 3]), Proof::from_bytes(vec![0, 0, 0, 0])] {
            assert!(!proof.verify(&b.inputs, &b.outputs, &b.nonces, &b.state));
        }
    }

    #[test]
    fn tree_proof_headers_are_checked_before_anything_expensive() {
        let b = block(vec![reward_tx(REWARD)]);
        // Truncated header, zero chunks, an out-of-range chunk index.
        let mut header = vec![KIND_TREE];
        header.extend(REWARD.to_le_bytes());
        header.extend(0u64.to_le_bytes());
        assert!(!Proof::from_bytes(header.clone()).verify(&b.inputs, &b.outputs, &b.nonces, &b.state));
        let mut zero = header.clone();
        zero.extend(0u16.to_le_bytes());
        zero.extend(0u16.to_le_bytes());
        assert!(!Proof::from_bytes(zero).verify(&b.inputs, &b.outputs, &b.nonces, &b.state));
        let mut out_of_range = header;
        out_of_range.extend(1u16.to_le_bytes());
        out_of_range.extend(5u16.to_le_bytes());
        assert!(!Proof::from_bytes(out_of_range).verify(&b.inputs, &b.outputs, &b.nonces, &b.state));
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

    #[test]
    fn transactions_plan_into_chunks_in_order() {
        let txs = spends(12);
        let chunks = plan_chunks(&txs).unwrap();
        assert_eq!(chunks.iter().map(|c| c.len()).collect::<Vec<_>>(), vec![8, 5]);
        assert_eq!(chunks[0][0], 0);
        let mut big = Transaction::new();
        for k in 0..=CHUNK_SHAPE.inputs as u8 {
            big.add_input(&wots::keygen(&[k; 32]).1, 1).unwrap();
        }
        assert!(plan_chunks(&[big]).is_none(), "more inputs than a chunk holds");
    }

    /// Prove an 11-input block (two chunks) with the consensus parameters,
    /// and print the tree circuits' verifying keys -- run after changing
    /// any circuit, then update `WRAP_CAP` / `AGGREGATE_CAP`. Then checks
    /// the proof verifies, and tampering is refused. Slow (minutes):
    /// `cargo test --release -- --ignored --nocapture tree_keys`.
    #[test]
    #[ignore]
    fn tree_keys() {
        let b = block(spends(11));
        let start = std::time::Instant::now();
        let proof = prove_block(&b.inputs, &b.outputs, &b.nonces, &b.txs, &b.plan, [3; 32]);
        println!("proved in {:.2?}", start.elapsed());
        // (The lock is released at the end of this block: proving again
        // below takes it.)
        let (wrap, aggregate) = {
            let keys = TREE_KEYS.lock().unwrap();
            let keys = keys.as_ref().unwrap();
            assert_eq!(keys.wrap.preprocessed.log_lde, tree_log_lde());
            (
                cap_to_hex(&keys.wrap.preprocessed.cap),
                cap_to_hex(&keys.aggregate.as_ref().unwrap().preprocessed.cap),
            )
        };
        let dev = crate::network::current() == crate::network::Network::Dev;
        let (current_wrap, current_aggregate) = if dev { (DEV_WRAP_CAP, DEV_AGGREGATE_CAP) } else { (WRAP_CAP, AGGREGATE_CAP) };
        if wrap != current_wrap || aggregate != current_aggregate {
            let prefix = if dev { "DEV_" } else { "" };
            println!("const {prefix}WRAP_CAP: &str = \"{wrap}\";");
            println!("const {prefix}AGGREGATE_CAP: &str = \"{aggregate}\";");
            panic!("the verifying-key constants are stale: update them to the above");
        }
        let proof = proof.expect("a tree proof that verifies");
        println!("tree proof: {} KB", proof.len() / 1024);
        let start = std::time::Instant::now();
        assert!(proof.verify(&b.inputs, &b.outputs, &b.nonces, &b.state));
        println!("verified in {:.2?}", start.elapsed());
        // Other lists, a different claimed split of the totals, or another
        // state change.
        let mut other = b.outputs.clone();
        other.swap(0, 1);
        assert!(!proof.verify(&b.inputs, &other, &b.nonces, &b.state));
        let mut bytes = proof.as_bytes().to_vec();
        bytes[1] ^= 1; // A
        bytes[9] ^= 1; // B, keeping A - B
        assert!(!Proof::from_bytes(bytes).verify(&b.inputs, &b.outputs, &b.nonces, &b.state));
        let mut state = b.state;
        state.count_out += 1;
        assert!(!proof.verify(&b.inputs, &b.outputs, &b.nonces, &state));
        let mut nonces = b.nonces.clone();
        nonces[0][0] ^= 1;
        assert!(!proof.verify(&b.inputs, &b.outputs, &nonces, &b.state));
        // A one-chunk block: its root is the wrap.
        let small = block(vec![reward_tx(REWARD)]);
        let proof = prove_block(&small.inputs, &small.outputs, &small.nonces, &small.txs, &small.plan, [5; 32]).unwrap();
        assert!(proof.verify(&small.inputs, &small.outputs, &small.nonces, &small.state));
    }

    /// The wrap circuit's size for a full chunk (verifying its proof and
    /// applying its 28 state updates) against its 2^18 rows.
    /// `cargo test --release -- --ignored --nocapture wrap_rows`.
    #[test]
    #[ignore]
    fn wrap_rows() {
        let b = block(spends(3));
        let k = 0;
        let txs: Vec<Transaction> = b.plan.chunks[k].iter().map(|&i| b.txs[i].clone()).collect();
        let spent: u64 = txs.iter().flat_map(|t| &t.inputs).map(|i| i.amount).sum();
        let created: u64 = txs.iter().flat_map(|t| &t.outputs).map(|o| o.amount).sum();
        let chunk = block_air::build_chunk(&txs, (created - spent, 0), CHUNK_SHAPE).unwrap();
        let start = std::time::Instant::now();
        let proof = stark::prove(&chunk.air, &chunk.trace, &chunk_params(), [1; 32]).unwrap();
        println!("chunk proof: {:.2?}", start.elapsed());
        let rows = aggregate::wrap_rows(&chunk.air, &proof, &b.plan.transitions[k], &chunk_params()).unwrap();
        let t = tree();
        println!("wrap circuit: {rows} rows of {} ({:.0}%)", t.trace_len, 100.0 * rows as f64 / t.trace_len as f64);
    }

    /// Not a correctness test: proving costs. `COST=chunk`: one chunk
    /// proof (fixed shape, so any chunk costs the same). `COST=block
    /// INPUTS=n`: a whole block of `n` one-input spends plus the reward.
    /// Run with `COST=... cargo test --release -- --ignored --nocapture
    /// proof_costs` (under `/usr/bin/time -v` for peak memory).
    #[test]
    #[ignore]
    fn proof_costs() {
        let case = std::env::var("COST").unwrap_or_default();
        let count: u8 = std::env::var("INPUTS").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
        let b = block(spends(count));
        let time = std::time::Instant::now;
        match case.as_str() {
            "chunk" => {
                let chunk = block_air::build_chunk(&b.txs, (REWARD, 0), CHUNK_SHAPE).unwrap();
                let start = time();
                let proof = stark::prove(&chunk.air, &chunk.trace, &chunk_params(), [1; 32]).unwrap();
                println!(
                    "chunk: {} rows; prove {:.2?}; {:.1} KB",
                    chunk.air.trace_len(),
                    start.elapsed(),
                    proof.to_bytes().len() as f64 / 1024.0
                );
            }
            "block" => {
                let start = time();
                let proof = prove_block(&b.inputs, &b.outputs, &b.nonces, &b.txs, &b.plan, [1; 32]).unwrap();
                let proving = start.elapsed();
                let start = time();
                assert!(proof.verify(&b.inputs, &b.outputs, &b.nonces, &b.state));
                println!(
                    "{count} inputs, {} chunk(s): prove {proving:.2?} (keys included); {:.1} KB; verify {:.2?}",
                    b.plan.chunks.len(),
                    proof.len() as f64 / 1024.0,
                    start.elapsed()
                );
            }
            _ => panic!("set COST to chunk or block"),
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
