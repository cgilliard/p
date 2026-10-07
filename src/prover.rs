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
/// production): blowup 16 gives 4 bits per query, so 26 queries plus 24
/// bits of grinding come to 128 bits of (conjectured) soundness -- ~64
/// against Grover's search. Challenges themselves come from the ~124-bit
/// extension field.
pub const PARAMS: Params = Params {
    log_blowup: 4,
    num_queries: 26,
    grinding_bits: 24,
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
/// hiding` and `docs/RECURSION.md`). 2^19 rows: a circuit verifying two
/// proofs at 26 queries (an aggregation, the chain step) needs ~330,000.
pub const TREE: TreeParams = TreeParams {
    trace_len: 1 << 19,
    params: Params {
        log_blowup: 4,
        num_queries: 26,
        grinding_bits: 24,
        hiding: false,
    },
};


/// The verifying keys: the wrap and aggregation circuits' preprocessed
/// caps, as hex. Derived from the circuits (see the `tree_keys` test,
/// which regenerates them); any change to those circuits changes these.
const WRAP_CAP: &str = "4c4155299bfe5d756bd70f2e20243e4bb200706998bf265e326a955286be396417abc10b653848041e71a04ef8ae4f43c2e3282f4b3a116d099a4c6b853c51617aa3e447d4099f0c3983ac008216fc31a01eb933d769a049e742226745879e6886884139896c9d53e0df3a1fd9427148e44bb31642b02329ea2c7407e49e011b13c7032012d3c569b19754698ac55d09b9bae804d181a82e427c364916136440ea75be1a5d2f5b2634466460ffcf9927d333b90571924d1ab375b422f4095b3c91fdcd1309784e153cb8440d4bee4e2714f92d10bbb4bb5def1474029a47f22a31a6bf5d3eafc60b40b0fa2c4ae61a0c92cafc02ece26e5ce519896a660abe4631a5664e1b6d1c67c44a4f36102804045691d42f6605502fbdf191197cb76014373e364d298a7d5b7adac85965106f113f4fc71eb088c42e9f2c452fcb2f266f86ec631fd91f97430b6fa334b3007e599ed39c0f7b59c64927d0b86804e46b1db5fff85ee4f73a3a472c890fb8aed95228b549421c3ab51b5f4f87259a8ee568cd4dbd049a1335314cfb3a48ff53e16427384100c1a4852c5af3ba517ea42a4a45ded841ac898313ccea0d5944359071e80d2822e05d773a2a04ab657bcc791d1a514558ed7a1769ae48ee27a84f7e5cf24c822f190e362efa56dc157be0a77256d8e23ed9cf1a495c55b05096014c2ed81de11bc712d5314e5897560e0e1b6a934aa53a9cdf3f37ed976f4a4b88ab228b26fa016c0d2a60119031163f1e5205e18ef414472365168942f460d8060226c89cd63792a2a4036d3d23623a410f45cdd45b11b94de72b60ce3212aa54451a683b822029c3c5380f364d4c63360c1209dc9c20bbe97f0e351b163448e1542f25f0995a5253720e5bae730689a572592e76c567a6785a4625dd710769558f0f65c9575cadc0a66d0645e31dd99fd8743a41593fd7d23a3871ea0f73d14a6a6911826a5966859a340eaab766d5bedb0bb1e1de46c5397d6af4e90a4222f6906bc5b21123a66edb3024ab327654326b6239eac80ec513cb241e0e3e35a3eaac587db5111e3c046914671ebb1825a7bc340ee1a36720c98c6de849b43bc7701a33e19fea0f7dcecc3255e9e551115a7e18945d8512ae4a145a08749750d94d65758e8d8d187b086b5406852b04851f3369eadade4cf52dd1776e5cf717b791bd56a002b66a6f630d2c7835e5565b7a6307662ab33d7337ca06a1867e3d9a60743cf085aa601588283d92aa0d5df0126e08fdee5147c38d4863d5c73f24f7037e60e175be5209ce2a4faff9176d45da6e39534f5a0d3df43b4ee8457775198f0b151ffd643ec3faf5162b3288286728c77695cd432b6458ca5530930e679cdadb5b35fca93c46dd1757cfa18e714351b67506c72325c27df924cb759671a9fccd737ac5934122544069837e9137e3f1bd6b";
const AGGREGATE_CAP: &str = "8e1ea039f2c6b577d7ae932e1190e466a4f1cf2276338510b73fcf7736da812a4b49423378acf93eace1954069b7b34386ee502922c22c4e9ffd563de6eaa11fca6be3383f3fc340ad15e40468fe1b5a59dc992abb0a287766234c69b224b00b1ca0fa22da4a1a655cbf975a2032b31ec846e463dab3543de214c23525b4d848215ac148ecb618581d68132c3a4fcf1197a2ec270cf7d517d153ea04efa7d654525e0f4705a38e10b4e67c4c50ab0f56180a7f0ef375331dfaa6184c0d80095b7c65d60dc5c2bf66db2a1b2610dc1f3f2ce6fb0e513ce325885dc6606eddac274b92756e9764d744bee6124ee8ff0e022581842b78147c665068531bb5c11b3a5ceb4b0c484dad27b811721f03a5a35868707b196a10a2135a57c553c9290742f16617710c6ce8178f4f9d00eec91421feb0066b74c15138f1beff69326e112d8d2c493ac443ee66aeea4e6a9ab47939a80e654dbe660d2b096fb736a11a3f05209d4f459d23250567b1c95888760845860b4f5d83898f5fa1d3eb5c4aa4c62de0317c3ebe07d614712af54dc2223f36b600036adf9e182b18e0f35716a2f21b637b180f55c5096666c25518d9607c3d1ffb47115c98523e1f2d2f645fb8574e236ba56f98dace21188b81458b5c7963d17eaa5808277b1d7e37685e2eabe21be299a83c85444848edea8b32fed661384fcf5f090fcab64ec478be0acc93b56a9b5dd36e6dc2a43fffbc8c279201ab20d6723e4625f2b323738dc927ebda0a681e99c6423201291c980a660576eb19757ce8dd0bff5ed10e5cc9ad68b745513aae815711e2701e53a2f52a3eee64685eee95901b3bf6f85d7cca301de46a5275935df4305858f6683238b25bfad9c4208150a424c70af25023f1694c9965c60ec5d9650e1f03c6192ccc79001f0033608230be6b256f475b1156e519b239a33a0dbf2208d3d47e394c87ac27e8f1c84685cbbd5775378e2f4d660c697e5167668b373c37e74886148441286e724e6d3e06c3d10b55a4b85205240e2a433ad9101c27876e7aa89b69a78c683681c70430103d810fa4885171a6977937a5951d2a7a7d10166ff8ac25215a3b762a38596f3796f2531b0c390fcb393c6022c177514069fc4d00ce9a030767f30782fb7e3c00acb836254c3768d898026d0c763940dccc8d3bf115ff770b43cc37ff91bf630b5d451950a4884ce58e8f54c13ae92c9388ac5d7ad45e65a7be3a08db7a316762c77d1927a7800d7596384508dfc344457e8023e128d66012f93a72eedbff5f1b60357152e2923a0370fc4305311d3cc1b4c36ff8682f52f2fe132d52d0c86c002ae6233c515d7730c568505f83ce28eed8a2726fe1424ea5e65859786124196b2a5053aeaf886728391435602e540bb167fc14e304806fd0ed245ae380f527773ae729c7cd3859f137cc42f7116633";

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
    /// applying its 28 state updates) against the tree's trace length.
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
        crate::recursion::clear_profile();
        let rows = aggregate::wrap_rows(&chunk.air, &proof, &b.plan.transitions[k], &chunk_params()).unwrap();
        let t = tree();
        println!("wrap circuit: {rows} rows of {} ({:.0}%)", t.trace_len, 100.0 * rows as f64 / t.trace_len as f64);
        crate::recursion::print_profile(rows, 1, chunk_params().num_queries);
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
