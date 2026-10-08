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
use crate::aggregate::{self, ChunkTransition, Key, RootClaim, StateChange, TreeParams, VerifyingKey};
use crate::block_air::{self, ChunkShape};
use crate::poseidon2::{BabyBear, P, digest_from_bytes, hash_bytes_32};
use crate::stark::{self, Params};
use crate::transaction::Transaction;

/// The first era's block reward: 1,000,000,000 units. What a block may
/// claim at a height is `Schedule::reward`'s -- the proof enforces
/// `sum(inputs) + reward == sum(outputs)` exactly.
pub const REWARD: u64 = 1_000_000_000;

/// The block reward over the chain's life: `first` per block for the
/// first `first_blocks` blocks, then `then` per block; with an `end`, no
/// block at that height or after is valid, and the chain is over.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Schedule {
    pub first: u64,
    pub first_blocks: u64,
    pub then: u64,
    pub end: Option<u64>,
}

/// Blocks in a year of ten-minute blocks.
const YEAR: u64 = 144 * 365;

/// The main network's: 1,000,000,000 a block for seven years, then
/// 7,000,000 for a thousand -- each era issuing the same total,
/// 367,920,000,000,000 -- and then the chain ends.
pub const MAIN_SCHEDULE: Schedule = Schedule {
    first: REWARD,
    first_blocks: 7 * YEAR,
    then: 7_000_000,
    end: Some(1007 * YEAR),
};

/// The dev network's: `REWARD` at every height, without end.
pub const DEV_SCHEDULE: Schedule = Schedule {
    first: REWARD,
    first_blocks: 7 * YEAR,
    then: REWARD,
    end: None,
};

impl Schedule {
    /// The reward a block at `height` claims; `None` past the end.
    pub fn reward(&self, height: u64) -> Option<u64> {
        if self.end.is_some_and(|end| height >= end) {
            return None;
        }
        Some(if height < self.first_blocks { self.first } else { self.then })
    }
}

/// This network's schedule.
pub fn schedule() -> Schedule {
    match crate::network::current() {
        crate::network::Network::Main => MAIN_SCHEDULE,
        crate::network::Network::Dev => DEV_SCHEDULE,
    }
}

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
/// totals `A`, `B` (`u64`s; `A - B` must be `REWARD`), whether the root
/// is an aggregation (`1`, more than one chunk) or a wrap (`0`), the
/// root's `data` (32 bytes), and the root `stark::Proof`. Nothing says
/// which chunk holds which commitment (see `aggregate`'s docs).
///
/// It attests that the body's commitments are authorized and balance,
/// **and** that applying them -- inputs spent, outputs appended in body
/// order -- takes the parent's state (`state_tree` root and output count)
/// to the block's.
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
/// Signatures a chunk proves, at most -- and so a transaction (each about
/// 278 of a chunk's 4096 blocks; `docs/CONTRACTS.md`).
pub const CHUNK_SIGNATURES: usize = 12;

pub const CHUNK_SHAPE: ChunkShape = ChunkShape {
    num_blocks: 4096,
    inputs: 8,
    outputs: 20,
};

/// Chunk proofs use the block parameters (zero knowledge: their witness
/// is the transactions).
pub const CHUNK_PARAMS: Params = PARAMS;

/// The dev network's parameters (`network`): blowup 4, 4 queries, no
/// grinding -- about 8 bits of soundness. **Not secure**; for testing
/// only, where they make proving several times faster (and keep the wrap
/// within dev's 2^17 rows: each query is ~5,400 rows of its verifier).
pub const DEV_PARAMS: Params = Params {
    log_blowup: 2,
    num_queries: 4,
    grinding_bits: 0,
    hiding: true,
};

/// The dev network's tree proofs: the same lightening, and half the rows
/// (fewer queries make the verifier circuits small enough).
pub const DEV_TREE: TreeParams = TreeParams {
    trace_len: 1 << 17,
    params: Params {
        log_blowup: 2,
        num_queries: 4,
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
const WRAP_CAP: &str = "8483463ae08b054813b0736c9fdb783fb640d9416c9c841d006ddf74b0fc973aa2c86c41ae565755f1f6313a8c21cd6441625b77ebc10369a8650b753770b52d4edc2a4c35d0af674f691759f596d46d60a87b13ef82b855042f4c727aeb43112796c81cb510044c4dc8a46994638f260ebdba03436df270d4567004fd32cc33d75b341343dbf46043bdb0053cfb910709367242f4cf591eed6f1d602a80d13f27658a2b173baa1923968434f42fc8001d1daf2fa98a104f6e1ee8568d415b141d64700ff937e6686036176c9fcc4a58f8848c547518e4168a491d27cd6dcd5289fc435a3c24e256e709f428ac68ff6e4396c744b4b41c5fea70f953727c4530b26dc86063f7ca1699b0922f5b96380c778f1072cdb136582e37a8123d011b136a5c02029284e05aa269842485074602ad9e146c6f44954e8128943ed7beba20645e933d57a29663488fbf11b3e7b10447e4314ac993011758e137379173ec46569d310b403a451bed575a570ac6ae2c46373f717b6e707486788b40b010c538d598a866f61f681aca22910d990729067fc0594e74a815593509a421172d10421b5eb1505f41cf1070e089764f6a98530d176160f3903241ec9be715afa1262743d1ce364b41255044f64940f69d8a0bb493286b98212b3187f5d330327cd7439f2c5c606de30f39109f8d5da16885466f7a3347a2ec06488e12ee59f07c8a4c169a33762e9f141128880d3c7b1638427fab794165a83712f305ae4034eaa73c61f3f164db14583df968e07728160d4441df890624187e6b2229b277b7b2cc08fbde0250aabc635c0689971e67797202e03b2e52fa4be70d0bbc2260594c9510b6857c31e9775e47adbd33297b39a5030d16f94a05859170532ec45447fc075656981076f5f9b6239c839b40687658426cf1d754a925c52705df925a76c08757545cc90110a933558cfffd1f08d30d309bdcbd620572f83d59472b51abd4b619be714f55517d1b5156832c6845871e5c52194c630f65755eac614906d7744c49e1095a59d9a8981c3a49455a936eb23995c07762981de1103cd23a2d38d9df0c2cb2a21a5e8790123e720e5cd383053fb50de02ed81a484a6be1cb44719777298da096244576f23aaf0ffd5d6bad064da344a9389a94bb698b88134c71420052ee39d566cfc8b72d1473db64d3e9d0073292092640761366ab108f3eac8b5a01b1f2f349ade6e01765aca10f208a3438c0cd4a065aaa194eeda3c5715f08a10dadf1d914191ef439c42ee418cca07254c6758a51facf6649f1721441cc3c6e147858326c382d8924a7a2a51b0e4f621e05d8bc739f88a05c521f681055c8da337c2d877148e07331ea6c47107224d17513deab084144390766636e23517ace0ff2fdd16bc518e26176595766087ff74d1c12fe17f85e4619fe50ca498f330446";
const AGGREGATE_CAP: &str = "341f072a4bf59b044d04ae5cbab42b1ddefd3304547fac024f2c1753f36d3f6fab2966023bf73607c4e2061683df61415bcdd429a89b681125d457187f31502746253d2d6319333c06fd1c469290a036cab8800729530218d1af1269a3d19f4c77fa0912df9e73205ace82546cea6e0f16fc840d8c32a74dc8217349a0327710d7a84c44c914651e88094e1c2effa630097e64388878431138c7476d2a56862732cde26a6aae604f93ff442103953761e3a5cd0d8599f6060019805b5ff5e64041cceb250d6997303b67d51c4ec2ec31b1b3a65263f06677eb49d4698c32875426b5ad40f410e66a1bc2070666480a0ac6df06435d7d606f4f5f81209c1c9509b38e2e64f369891f0e40c630998b405493da8623512819394c88f975afe49a2196108512e00bcf2b9ddfcd04366bba43cfa0420c9ce13b65c0c6e76ce09cf818dceb3d6d38c9284ccbbfab6456fc19313b41b17142e2356cf6eae5056faabf74c301994db8fd1233223ce9749b9fae5e5e54a10e158d3e5dddf6a612553dd3514f250163f8777e332a378b21ac30d5543a5a972d35239e66871a237537718868ff3e74422f1fa23a92aa637309358b212740ca7540a52101b975cd16a3b96a6e03fcd96894e7c66acf7b360c12c9514a9a75120e8695055df83e103b77ecb422eb26c65d38fc6c3840398b7471dbc662901eb20712fa77175c363f3daa193e51e0fcd52891fea758693529525a4398703cd86136d1f1ec19c4499754c2ceba5201fce21a751853716b476421bafd2d240d835f45a413761799ba500e2768961570aa556bac005a688b21bf1e0874b55467b5a3345fe2fd4ef81cb83510fbcf31efb55623278c2a57dd0c1169c9cd14506df78435333dae5651867c4a5f8e4b114182851a9024c6311037880bfe8a6a2bf487191a4f247b5c84a70f25483b034da198c62837bec4736d5c2441159ba0267813770b3fc9946eeffda83bc33d3b2f24a6cc1dcb1299608bbd5430add34c02cdef1364aaf12e4fa293110f1d58c35ee246c52eb32b03180241c45cef4ae522d0c0f8035b61e257d505561fcf3fbd4ee32c5033a682675d9a0efd3ae6b67e4b7964f245ff5d956854390b088f4e3641f788e51885d8e550e99d372c8dc1b2599d733b14bc6da33f30088636ec1595715531a87122927071247afa3749331a0e0deb78435a2cbc2fff34ac38f8b8c807b5322047fbfe7220557eb9749dc4641790ba4e3667ad9b25545d5122b961e01d7c1ba8739e9f4c003c36a2055d43731a78461f4bb972ff75c5205148a10597681eaa5c63cd78d0166812570cbeea513b7dbe4f6ca0497d242c7b5c2699e2bd1b8ecf835fb80ca25f857a0a31852e0e4a48e8f543c4a8010787257f0aeeab90080859a920ed6e4a0191660103a22da13341cb2417126dbf1e6132461b07ac9f1d";

fn cap_from_hex(hex: &str) -> Vec<[u8; 32]> {
    let bytes: Vec<u8> = (0..hex.len() / 2).map(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap()).collect();
    bytes.chunks_exact(32).map(|c| c.try_into().unwrap()).collect()
}

fn cap_to_hex(cap: &[[u8; 32]]) -> String {
    cap.iter().flatten().map(|b| format!("{b:02x}")).collect()
}

/// The dev network's verifying keys (`tree_keys` with `NETWORK=dev`).
const DEV_WRAP_CAP: &str = "8c8f3047b02e2c5a47085c182fa25370dbe7a4218e14c33fc70dd477b3a5ef659e16962f29e0df3573b73c2ab8056a0629baa55158e08875ebd7c72778183d698d2db5184fe50728ae0b52693b712839bb97f0516d65fc3d34702635ca014d6d7f0436249f277a64c1206312e7c31f1db8634606755c1d52e9d89e16f8adcf5c20f8674badd30825b91a87111e2034079d5c791a865c114d351e3f55699f0663c89dd46aa107e5175b8127563fb2c50570429a709365a906d88b7a6a242f272c568c8d1affd4b355ae6ef907fb878f55d943da52c3ddcc59ebbd392b5cf7d46c5c99d30a88c73464b6db74172778305cf2f4722f6313583e365b1c59b5b7e0138aea932151d1c2362da10920abf56f45252e1e6e92dca45587b18b38155ec256bd002363a83f041540f00e15787dc51fa3ece577e9647c5805a68a50184da5170070e92e19ac141628a4674fe4c025579689e63192c2e26c8e384d2ee48c252424790a12506a6f0659f2853aa7c2a51a0a4c7d2eafad03101af216178ea0e540b5f99c5c4e2c0402f2ca091806b8271754c4422a8b22452ad8027d083940863c90028407016c942ffbb22f0dc8ed816c06e7b03352be9c1889dddb0f010a813153a2226b87a97165892ac42d36b7270bdb3c6422c065e20d10a0255060386867368ea060571c903a5a8bd80a93674225d78c3b0904c06e454510a0571419d51c08a76045d885164c5304df48e51f6423769e186e9eafa630ac882c1febd5dc1982f5270471b4d10896c0482436f7794875765b3689a07e3138682564cc790f4cac954009e0dceb10c1e3a23504a81f59dffeec49043b20145a81134146a3352e5cd0217493b3d326fc7d9a3129ef783ddeb7172df83f723dc78b7022d46f78493a235645a39eee650269e371595e6a75e5e96d16197118134e2a7115b35b8069d5256f6e1338215d33b71c69da58947489c2ee0a2a8a8511afefef6793b1e021004a9f5b134deb1a17dff603713d6870b4d8c93e3cc56428ffbd3109e4b376611bd4514fbd9fc43f29c6a06ac021b41bc47e2b04eda6b9088663cc19dfe54e4e7893fb2b968b786281dc5f5eb0376d0bafba241c4fee272f9930572c80504928d2325a60506435651fab6b6cc71978544be0af2a79d346640d744d171675be640aa8b02ce213724e048f4f4edab91d2fbf111660c3bdc3005b6f3051da8008145e7bd743ae714a20d1b0fb328f5fc7469e16747633b7f24e8521a07354c10f5c281f425798aa382b06a55c57e6d61e0a2c238a5593068366bf1db0729848080d0f174a5cbd78760b0096b4266ec73a12eda3c358910f890e66aa9f016190736c8547f060ec689b01f69ade1c9f76503a9cd2ce6c88106f1a1e61a025ef61da62b78063129adea81ad7a12d59af1c7603d2366b0805e79a0608c14646cbfd2338";
const DEV_AGGREGATE_CAP: &str = "545e8c2c2fb0a410321ef75df1d2107175b21b42b579034cec67790d9329c65340a7423d222cbd317b7a1d194fc6e84cbc5ece4ccda205614b9d5250e3940b505802181a4a78b83245ec143386d2130be685077721313d1007199140e34d296d7ef3e51ae8324a024f972a5344011d4480703b04aa03da744eeb75216513a21978361d175e6ac9536cdd43314b1c153aa881ca12f55eb6376f9fe50a94cd755ed16b230c4378346b8d713a51c51a99078ddedc35db019d683c2eb50f40a1d527af0f2a57b3610a2223996421a8a26610c0b29c42791be414704e111ecf67df69418f2652567bcf20f3614a568298e25343aaca2539900125e2e02f03de7a2f3c855e0618c1e1c15e3966066d8d06a02f9c360301481aa85d7651e21bc7631724ec0b692bdb0e874e04b7bc5073a20e02961a7b3ad21ac004279810532510485e6995061292930b56715bf5499c461a521fb4716dad105c6c439b8c203ce3883f53880f53604f3e0ed45a3e49b1ba5317ddb789680ddcbf0139575e1dd9464e0a2e850101581bf83af8c5a959da459628d262e43e9724955c40f8cb59ff2d533440e7811fb3b7396d3fa9e27099edde65d4e4af3913ac3d6cce589c39329e4628996e7c0ca3c07e506a1371386e3d3f2608e3b75c77db3e6b99307d12cd023c676283f55e430a4b2bdfd9e05cfbdf1941be4e5b659d95244fa73906042a4285723261de05c6c68e5b71fdad191e5a9b65dc331430bc3e9b3a7b90ee4fb2721c465632dc0454a7b75224ed4d5011125417ab847714bc22a3164cb1dc63b683575ad450360c3c885b157b223d4133aa8e12495c9e448596e557dd54426c70c4d525039d1237fcfef82fc9fd7719ea559d1ea308b045e0e12a478a634728ba96e837a0da8f74b786232ae4e23142ba292d507125555f4b64c3476907291875edf12be8b0a2625a5d1c3a4cc1ff0ab8171f6351b8aa1a65da0a6f32ea6948ac191b619fb47307f8a7d81a33bc8258834bdd5c2f4127755444cf4e8d8406170760874da5a485249a8dd834a9fd9c413a955518c66a4c00fc665a196859851ae2cc1054c04590137836d10408688719fd50ee4c4814ac2fb1dd517100ce4d3e867061350cd2155406c52c72c347bf4d6b42074df646403a035d3708b64164206b59c51b1dcb28476387de5ed40b966d106cb75cfd188b3a8e149059a5113725beedb829ccbf206176b43432564d54178b57120f245f5f0fff68095b4743651ba2232a641926e06aeb186925cff4a42c06074648bfdc106b013f1f226a80de0d3b12dc62a38a806291227d0aebeb181634fde14714b4b6761b85282661bce93fd7f12e7640eb4f4c0c6d5b471c0639183a4c533717acd55cf231c87188b3044108e5ef41cf82bb197bbbac50274ec66db6f7dc655579ee29ba497a31453eac7510e4b931";

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
    /// `outputs[i]`'s), claiming `reward`, with the state moving as
    /// `state` says for a block at `height`.
    pub fn verify(&self, inputs: &[[u8; 32]], outputs: &[[u8; 32]], nonces: &[[u8; NONCE_LEN]], state: &StateChange, height: u32, reward: u64) -> bool {
        if !inputs.iter().chain(outputs).all(is_canonical) || nonces.len() != outputs.len() {
            return false;
        }
        verify_tree(&self.bytes, inputs, outputs, nonces, state, height, reward)
    }
}

/// A tree proof's header -- amounts, whether its root aggregates, the
/// root's data -- and the root proof's bytes.
type Header<'a> = ((u64, u64), bool, [u8; 32], &'a [u8]);

fn parse_header_and_rest(bytes: &[u8]) -> Option<Header<'_>> {
    let mut r = Bytes(bytes);
    if r.take(1)? != [KIND_TREE] {
        return None;
    }
    let amounts = (r.u64()?, r.u64()?);
    let aggregated = match r.take(1)? {
        [0] => false,
        [1] => true,
        _ => return None,
    };
    let data: [u8; 32] = r.take(32)?.try_into().unwrap();
    is_canonical(&data).then_some((amounts, aggregated, data, r.0))
}

/// What a root proof is checked against, for this body, state change and
/// height; `None` if the proof's header doesn't parse.
fn claim(bytes: &[u8], inputs: &[[u8; 32]], outputs: &[[u8; 32]], nonces: &[[u8; NONCE_LEN]], state: &StateChange, height: u32) -> Option<(RootClaim, stark::Proof)> {
    let (amounts, aggregated, data, rest) = parse_header_and_rest(bytes)?;
    let claim = RootClaim {
        inputs: elements(inputs),
        outputs: elements(outputs).into_iter().zip(nonce_elements(nonces)).collect(),
        state: *state,
        height,
        aggregated,
        data: digest_from_bytes(&data),
        amounts,
    };
    Some((claim, stark::Proof::from_bytes(rest)?))
}

/// A block proof's tree root, as a chain step verifies it
/// (`chain_step`): for this body, state change and height. `None` if the
/// proof doesn't parse; whether it verifies is `Proof::verify`'s question.
pub fn block_root(proof: &Proof, inputs: &[[u8; 32]], outputs: &[[u8; 32]], nonces: &[[u8; NONCE_LEN]], state: &StateChange, height: u32) -> Option<aggregate::Node> {
    let (claim, root) = claim(&proof.bytes, inputs, outputs, nonces, state, height)?;
    Some(tree_verifying_key().root(&claim, root))
}

fn verify_tree(bytes: &[u8], inputs: &[[u8; 32]], outputs: &[[u8; 32]], nonces: &[[u8; NONCE_LEN]], state: &StateChange, height: u32, reward: u64) -> bool {
    if state.count_out.checked_sub(state.count_in) != Some(outputs.len() as u64) {
        return false;
    }
    match claim(bytes, inputs, outputs, nonces, state, height) {
        Some((claim, root)) => tree_verifying_key().verify_block(&claim, reward, &root),
        None => false,
    }
}

/// How a block's transactions are proven: grouped, in order, into chunks
/// (`plan_chunks`), and each chunk's state transition -- what
/// `chain::Chain::build_block` works out against the parent's state.
#[derive(Clone, Debug)]
pub struct BlockPlan {
    /// Each chunk's transactions, as indices into the block's list.
    pub chunks: Vec<Vec<usize>>,
    pub transitions: Vec<ChunkTransition>,
    /// The reward the block claims, at its height (`Schedule::reward`).
    pub reward: u64,
    /// The block's height and its inputs' creation heights.
    pub heights: block_air::Heights,
}

/// Group transactions, in order, into chunks that fit `CHUNK_SHAPE` and
/// `CHUNK_SIGNATURES`, as indices; `None` if one doesn't fit even alone
/// (consensus: no transaction may have more inputs, outputs or signatures
/// than a chunk holds).
pub fn plan_chunks(transactions: &[Transaction]) -> Option<Vec<Vec<usize>>> {
    let mut chunks: Vec<Vec<usize>> = Vec::new();
    let (mut ins, mut outs, mut sigs) = (usize::MAX, usize::MAX, usize::MAX);
    for (t, tx) in transactions.iter().enumerate() {
        let (i, o, s) = (tx.inputs.len(), tx.outputs.len(), tx.signature_count());
        if i > CHUNK_SHAPE.inputs || o > CHUNK_SHAPE.outputs || s > CHUNK_SIGNATURES {
            return None;
        }
        if chunks.is_empty() || ins + i > CHUNK_SHAPE.inputs || outs + o > CHUNK_SHAPE.outputs || sigs + s > CHUNK_SIGNATURES {
            chunks.push(Vec::new());
            (ins, outs, sigs) = (0, 0, 0);
        }
        chunks.last_mut().unwrap().push(t);
        (ins, outs, sigs) = (ins + i, outs + o, sigs + s);
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
/// balance against the plan's reward, or don't match the body or the
/// plan.
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
        witnesses.push(block_air::build_chunk(&txs, net, CHUNK_SHAPE, &plan.heights).ok()?);
    }
    // The block must claim exactly the reward (plus fees, which cancel).
    if totals.0.checked_sub(totals.1) != Some(plan.reward as u128) {
        return None;
    }

    // The chunks' commitments must be exactly the body's.
    let mut proven: Vec<[u8; 32]> = witnesses
        .iter()
        .flat_map(|w| w.air.public_inputs().iter().chain(w.air.public_outputs()))
        .map(|c| crate::poseidon2::digest_to_bytes(*c))
        .collect();
    let mut listed: Vec<[u8; 32]> = inputs.iter().chain(outputs).copied().collect();
    proven.sort_unstable();
    listed.sort_unstable();
    if proven != listed {
        return None;
    }

    // The binding (`aggregate`'s docs): each leaf's data under a fresh
    // salt, so the root's data -- and with it the challenge every wrap
    // takes -- is fixed before any wrap is proven.
    let salt = |k: usize| digest_from_bytes(&hash_bytes_32(&[&derive(0x4000 | k as u16)[..], b"salt"].concat()));
    let salts: Vec<crate::circuit::Octet> = (0..witnesses.len()).map(salt).collect();
    let leaves: Vec<_> = witnesses.iter().zip(&salts).map(|(w, &salt)| (aggregate::chunk_data(&w.air, salt), (0, 0))).collect();
    let (data, _) = aggregate::tree_data(&leaves)?;
    let body_outputs: Vec<_> = elements(outputs).into_iter().zip(nonce_elements(nonces)).collect();
    let challenge = aggregate::challenge(data, &elements(inputs), &body_outputs);

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
        let binding = aggregate::Binding { salt: salts[k], challenge };
        wraps.push(aggregate::wrap(&keys.wrap, air, proof, transition, &binding, &chunk_params(), &tree(), derive(0x8000 | k as u16)).ok()?);
    }
    let aggregated = wraps.len() > 1;
    let root = if aggregated {
        if keys.aggregate.is_none() {
            keys.aggregate = Some(aggregate::aggregate_key([&wraps[0], &wraps[1]], &keys.wrap, &tree()).ok()?);
        }
        aggregate::aggregate_all(keys.aggregate.as_ref().unwrap(), &keys.wrap, wraps, &tree(), derive(0xffff)).ok()?
    } else {
        wraps.pop().unwrap()
    };

    let mut bytes = vec![KIND_TREE];
    bytes.extend(root.amounts.0.to_le_bytes());
    bytes.extend(root.amounts.1.to_le_bytes());
    bytes.push(aggregated as u8);
    bytes.extend(crate::poseidon2::digest_to_bytes(root.data));
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
    proof.verify(inputs, outputs, nonces, &state, plan.transitions[0].height, plan.reward).then_some((proof, root))
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

    /// Main's two eras issue the same total, and the chain ends after
    /// the second; dev pays `REWARD` forever.
    #[test]
    fn the_schedule_has_two_equal_eras_then_ends() {
        let (first, end) = (MAIN_SCHEDULE.first_blocks, MAIN_SCHEDULE.end.unwrap());
        assert_eq!((first, end), (7 * 144 * 365, 1007 * 144 * 365));
        assert_eq!(MAIN_SCHEDULE.first * first, MAIN_SCHEDULE.then * (end - first));
        assert_eq!(MAIN_SCHEDULE.first * first, 367_920_000_000_000);
        let rewards: Vec<Option<u64>> = [0, first - 1, first, end - 1, end].iter().map(|&h| MAIN_SCHEDULE.reward(h)).collect();
        assert_eq!(rewards, [Some(REWARD), Some(REWARD), Some(7_000_000), Some(7_000_000), None]);
        assert_eq!(DEV_SCHEDULE.reward(u64::MAX >> 1), Some(REWARD));
    }
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
        height: u32,
    }

    /// The test blocks' height, and their inputs' creation height.
    const HEIGHT: u32 = 5;
    const CREATED: u32 = 2;

    /// `HEIGHT`, every input of `txs` created at `CREATED`.
    fn heights_of(txs: &[Transaction]) -> block_air::Heights {
        let created = txs.iter().flat_map(|t| &t.inputs).map(|i| (i.commitment(), CREATED)).collect();
        block_air::Heights { block: HEIGHT, created }
    }

    fn block(txs: Vec<Transaction>) -> TestBlock {
        use crate::state_circuit::MemTree;
        use crate::state_tree::compress_leaf;
        let body = BlockBody::from_transactions(&txs).unwrap();
        let chunks = plan_chunks(&txs).unwrap();
        let zero = [0; NONCE_LEN];
        let leaf = |c: &[u8; 32], n: &[u8; NONCE_LEN], h: u32| compress_leaf(&digest_from_bytes(c), &crate::output::nonce_limbs(n), h);
        let mut tree = MemTree::default();
        for c in &body.inputs {
            tree.append(leaf(c, &zero, CREATED));
        }
        let (root_in, base) = (tree.root(), tree.count());
        let end = base + body.outputs.len() as u64;
        let mut transitions = Vec::new();
        let mut count = base;
        for indices in &chunks {
            let mut ins: Vec<[u8; 32]> = indices.iter().flat_map(|&t| &txs[t].inputs).map(|i| i.commitment()).collect();
            let mut outs: Vec<[u8; 32]> = indices.iter().flat_map(|&t| &txs[t].outputs).map(|o| o.commitment()).collect();
            ins.sort();
            outs.sort();
            let (root, count_in) = (tree.root(), count);
            let mut t_inputs = Vec::new();
            for slot in 0..CHUNK_SHAPE.inputs {
                match ins.get(slot) {
                    Some(c) => {
                        let p = tree.position_of(&leaf(c, &zero, CREATED)).unwrap();
                        t_inputs.push((p, zero, CREATED, tree.path(p)));
                        tree.spend(&leaf(c, &zero, CREATED));
                    }
                    None => t_inputs.push((end, zero, 0, tree.path(end))),
                }
            }
            let mut t_outputs = Vec::new();
            for slot in 0..CHUNK_SHAPE.outputs {
                match outs.get(slot) {
                    Some(c) => {
                        let o = body.outputs.binary_search(c).unwrap();
                        let p = base + o as u64;
                        t_outputs.push((p, tree.path(p)));
                        tree.place(p, leaf(c, &body.nonces[o], HEIGHT));
                        count += 1;
                    }
                    None => t_outputs.push((end, tree.path(end))),
                }
            }
            transitions.push(ChunkTransition {
                change: StateChange { root_in: root, count_in, root_out: tree.root(), count_out: count },
                window: (base, end),
                height: HEIGHT,
                inputs: t_inputs,
                outputs: t_outputs,
            });
        }
        let heights = heights_of(&txs);
        TestBlock {
            inputs: body.inputs.clone(),
            outputs: body.outputs,
            nonces: body.nonces,
            txs,
            plan: BlockPlan { chunks, transitions, reward: REWARD, heights },
            state: StateChange { root_in, count_in: base, root_out: tree.root(), count_out: end },
            height: HEIGHT,
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
            assert!(!proof.verify(&b.inputs, &b.outputs, &b.nonces, &b.state, b.height, REWARD));
        }
    }

    #[test]
    fn tree_proof_headers_are_checked_before_anything_expensive() {
        let b = block(vec![reward_tx(REWARD)]);
        let mut header = vec![KIND_TREE];
        header.extend(REWARD.to_le_bytes());
        header.extend(0u64.to_le_bytes());
        // Truncated, an unknown root kind, non-canonical data.
        assert!(parse_header_and_rest(&header).is_none());
        let mut bad_kind = header.clone();
        bad_kind.push(2);
        bad_kind.extend([0; 32]);
        assert!(parse_header_and_rest(&bad_kind).is_none());
        let mut bad_data = header.clone();
        bad_data.push(0);
        bad_data.extend([0xff; 32]);
        assert!(parse_header_and_rest(&bad_data).is_none());
        let mut good = header;
        good.push(1);
        good.extend([0; 32]);
        assert!(parse_header_and_rest(&good).is_some());
        assert!(!Proof::from_bytes(good).verify(&b.inputs, &b.outputs, &b.nonces, &b.state, b.height, REWARD));
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
        assert!(proof.verify(&b.inputs, &b.outputs, &b.nonces, &b.state, b.height, REWARD));
        println!("verified in {:.2?}", start.elapsed());
        // Other lists, a different claimed split of the totals, or another
        // state change.
        let mut other = b.outputs.clone();
        other.swap(0, 1);
        assert!(!proof.verify(&b.inputs, &other, &b.nonces, &b.state, b.height, REWARD));
        let mut bytes = proof.as_bytes().to_vec();
        bytes[1] ^= 1; // A
        bytes[9] ^= 1; // B, keeping A - B
        assert!(!Proof::from_bytes(bytes).verify(&b.inputs, &b.outputs, &b.nonces, &b.state, b.height, REWARD));
        let mut state = b.state;
        state.count_out += 1;
        assert!(!proof.verify(&b.inputs, &b.outputs, &b.nonces, &state, b.height, REWARD));
        // Another height (its outputs' leaves would differ).
        assert!(!proof.verify(&b.inputs, &b.outputs, &b.nonces, &b.state, b.height + 1, REWARD));
        let mut nonces = b.nonces.clone();
        nonces[0][0] ^= 1;
        assert!(!proof.verify(&b.inputs, &b.outputs, &nonces, &b.state, b.height, REWARD));
        // A one-chunk block: its root is the wrap.
        let small = block(vec![reward_tx(REWARD)]);
        let proof = prove_block(&small.inputs, &small.outputs, &small.nonces, &small.txs, &small.plan, [5; 32]).unwrap();
        assert!(proof.verify(&small.inputs, &small.outputs, &small.nonces, &small.state, small.height, REWARD));
    }

    /// A block spending a policy output -- by the 2-of-3, hash-locked
    /// branch of a two-branch policy -- proves and verifies with this
    /// network's parameters, through chunk, wrap and aggregation. Slow:
    /// `[NETWORK=dev] cargo test --release -- --ignored --nocapture
    /// a_policy_spend_proves`.
    #[test]
    #[ignore]
    fn a_policy_spend_proves() {
        use crate::policy::{Branch, Policy};
        use crate::poseidon2::digest_to_bytes;
        let key = |k: u8| digest_to_bytes(wots::keygen(&[k; 32]).1.hash());
        let preimage = digest_to_bytes([BabyBear::new(7); 8]);
        let pay = Branch { threshold: 2, keys: vec![key(11), key(12), key(13)], after_height: 0, after_age: 0, hashlock: crate::policy::hashlock(&preimage), rebind: None };
        let refund = Branch { threshold: 1, keys: vec![key(14)], after_height: 1_000, after_age: 0, hashlock: None, rebind: None };
        let policy = Policy { branches: vec![refund, pay.clone()] };
        let mut spend = Transaction::new();
        let path = policy.path(1).iter().map(|h| digest_to_bytes(*h)).collect();
        spend.add_policy_input(pay, 1, path, Some(preimage), 300).unwrap();
        spend.add_output(Output::new(&wots::keygen(&[15; 32]).1, 300)).unwrap();
        let commitment = Output::locked(policy.lock(), 300).commitment();
        for k in [0u8, 2] {
            let (sk, pk) = wots::keygen(&[11 + k; 32]);
            assert!(spend.sign_policy_input(&commitment, k, &pk, crate::keytree::KeyProof::one_time(), &sk));
        }
        assert!(spend.verify());
        // Two chunks (the spend's three signatures don't fit beside the
        // spends), so an aggregation too.
        let mut txs = spends(10);
        txs.push(spend);
        let b = block(txs);
        assert!(b.plan.chunks.len() > 1);
        let start = std::time::Instant::now();
        let proof = prove_block(&b.inputs, &b.outputs, &b.nonces, &b.txs, &b.plan, [7; 32]).expect("a policy spend proves");
        println!("proved in {:.2?}", start.elapsed());
        assert!(proof.verify(&b.inputs, &b.outputs, &b.nonces, &b.state, b.height, REWARD));
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
        let chunk = block_air::build_chunk(&txs, (created - spent, 0), CHUNK_SHAPE, &heights_of(&txs)).unwrap();
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
                let chunk = block_air::build_chunk(&b.txs, (REWARD, 0), CHUNK_SHAPE, &heights_of(&b.txs)).unwrap();
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
                assert!(proof.verify(&b.inputs, &b.outputs, &b.nonces, &b.state, b.height, REWARD));
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
