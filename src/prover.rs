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
const WRAP_CAP: &str = "e05fe047224021099c5129750516af15bad9ac268ff7514f483d1c0bb2ba4b219e2eee1a36b110772957516a73ab9542f76f4015c0840e49e96b9e602096d525271bc33dcc75440187b9ad091b2b5223b7a4715107c0783aa5f50d1cb773930acf8a150256a87b42016769068d09c919d10877460be19c1320b6697548f3661094694933c19b631437e3990de06c5a492ce5f55d31326113f7f80e433355842a464348211abd402d59cbc048683d2c2880f5b1553d131d165adb9d2fbe08a03ecf0cbb038ebbac28e61fd05f8d9a566a50296a176ad27a3396b8de2a5c26b755c486565d2092a45ba5e38f3e9dbc572f50852919c67a173d812f54227336806fd920091ec71cfc32cf19ae716f25092df053322d02b4911af6ec4225cabc3f4aec661554d6d502156391ce3b99a9251813005349cebc7e6ad260700954634363f23ae26ee2a5630bb2294a04739d5513703c8a2ccbefdc4b2efd1f0685687740c2576870dfe8a0436ead6e14e10bfe4f664a6d001caa36611234a44535c3215c3cc4775e24a7b72b5126776fb9c2b121399dc576ed551335bac0da74c7dd353def2cdf28505c9040aa4ba36f5fa1e772e454d269cbada01b63cf236135eee862f895a50a82055152b210eb48d2626761cc81ea6bd324cf4386932900b12223383f6ac006139ce610c5bca400ee8bff0d3577b123deb0da76efe6764ddb2d0449958be82604f1c034b26f2105bdbe990ef85c87117c4dcd0d5ac1030c9c27ec6e5356892ea3d4cb6c3d01f2416a72441960919943ce051c6f270efc4fed730d174f0a7d6a80c7f271d33f7d428d52eb3e1e085f6c7a43bc5f53a72642e68c391de799f56de03aa8629af1560763f8c72784ca266eee034f1a21ea2a59aaa85b29b3ec6a649487b036d015e6762d76264db8eaa81103b1e2242b9c3f09f6e877225c386c39ec36f8765c50d238ce8bc22ef047126a377c225789fa3d0fa5d10e1cb7432a0bcb29f265862b8e048950e26a46115b3958866c718789a034e21c4b2a817fce09ec55740a6a7101155bbe013dd0d64423fb26530208521616ce741572503f365d2f76aa37d2e6a85a32945c5f688ed003d5798c4f16a3616890cb31568b7878189db88133c06c861efd036772007ff54db1ac4c3bae33b6170c89673b89b665179c7134756adbe04609b2a05269d169195f7fbd6aa96da534edc47b02f079120323245819cc7f3a54ed9f1d105b94e55a320ff71738abbc747ffad55cb721bd12387dab72222c511767b8225cbe3884634f699d1ece6e6d0a901f21248ed996577ed817703384563085f3415971e77e268d85c826ddbff026dcb0423167ffac06738ca34bfe5ba002e47bc311e63233104277b840c507703a57b7f26e593e225669e2bc07fecf4d772759310ddbf090676305b377d5d6c256da6d9972";
const AGGREGATE_CAP: &str = "18274869ee271673e7c9b4260bac0a593a48d60ef21f173e88f28d1dac5fac3de7b2a863a85f7766b36afe6c51d3d00ba4e4ec3425f60d12458dd309a12ac076557e350b9ccbcd71a8cae14da6b0f726b498ea389d58ff30fb595b5c1c07ef4b5cfa396917c9221aa4c6a55dd223c13bf91daa5609e6af0b17a1d008c123f45cc9156a720a57654d8b8cbf424961f82451f0ae3f7718fb34d307842dae4cbe57a7d112620aa4756e8096d03bd76658380157a07636bca63e5071543cda9e7d5a42f77419ebdf673752eb94515f68db3d2f0c40217cf63d612562a804fee6da6e51841964560a5f339b5d400be2ce3a48d1c16259f391520d493e25638a6a2d0687cc9a5acc1e52508346bb34c403060db19fbb47e7fd8e1745683b4a1564092b29a2c80826e7d44780707d103f18c441fb67ba6679421600f5eaa1502f8c9e0960c4d656c55da4513ce1633b8ddf7a35b742912af5fa253a8cbbb86ec7abec4fc2d23917d62c8963e0836f66f97b44177a36860c685422725acbdc40c13b4d3c843a7857afa2f7573346a76ac3ef252888f190387ea4b710d6169c3fda38226fa9d6e662e9b0a50e52f71b579543b61ea5c3fb33e9bfb644abd1954aab94e63ca43aaf52424125729252ad56d9a35960c6acae53ec0ea563871ff25b454f8e5fbc2a7f0f56ff8e411674932a7b1c633d02a9097724cbdb2ca5a5943d60687f64d8ed6811d779c1776ef83541c9f13d51f841f7350cc37412ecf772291fa6c1356f4ca13f47b4c56e71523e135284b672204ddd1ac363c63d0bbf5a0bceb1fc6160c1311450799676f233c20165b0664d25d9f450e596aa3859c19431305f2a4779308809b428a5425739e41db0a8386952517e4c1998d163aa759b1794472a4635cd8e1cc09ed67304b5f0450baae420083a0774e9cfbe710b599e4ebe156f29cdd8b26ce5ed071d3a57b8018442bd5fc6019d66d2d7f96c36692926dab93968a4ccbf2a0ffb692db7cf4510dd54926737046542f4bbc571ebce2d7666c308771392051ca621ca274a12204ecc4eb96d4a4055672c12f75467024d753e87360258d4a84489875200fecc8c6731d9ee5b4fa7163e5ab1801d863e1d12d5c69a6b282a082f738c72123064a10073f151603585470ea3a41b11ffeb7c7439dc373e6c847b75e153af66f7221244dd2d25411ab504479f04143253cd1d52b5cd6649f7c0f50527b66a74c055916d227176057676282698f0786d618a161d9857f76a5b2dc5227a03f802d73bf660106bee68d6b16b48d5c5d54ed0f34a114c5eb91576af2d2d886e1473be839a6728f775212798076488baff538784a50efc1bf0080a40f92545a7b40cc7b610065b57575a39e73007d6872f515568182925060d56fa7b474f909bd06b63eee654d5b2b03d553d8d4a391805354fe18d75847f3b38";

fn cap_from_hex(hex: &str) -> Vec<[u8; 32]> {
    let bytes: Vec<u8> = (0..hex.len() / 2).map(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap()).collect();
    bytes.chunks_exact(32).map(|c| c.try_into().unwrap()).collect()
}

fn cap_to_hex(cap: &[[u8; 32]]) -> String {
    cap.iter().flatten().map(|b| format!("{b:02x}")).collect()
}

/// The dev network's verifying keys (`tree_keys` with `NETWORK=dev`).
const DEV_WRAP_CAP: &str = "a37475460963475befa0991a2c074471d81aab23e43cef5fecdfa41ea2521a1871f0581d8c7283119638eb59602965309e7a893d10dfd620e5d9cc5bdbecc6483e034b1f05391006cea10e6ac037f319be87b15f69f0954a04d0025e5900ee1ef462c2038ac6b16c913daa683c108a4075d75a45822eed176a063f300d25d44d3e3de7530a42b41067659b054af2113f07dbb81bf9454876cac29e671921d76e11b4682d3e5e882fe424044197525765c8006b33b2691963ec3b866f72580028ec618209b82cf5578d0ac5628e4864753cc5de6d4aab115d9ce18350e933850896ddd52cce7e2b5aa21e590e226e7501d0e1250eb636c82c0d6aae066ff90477fc5db64c61e460770ba1bf6401162c74ba56e00299bcd716f7dcfe2a926ad5476d958a5bf2d015562ea0103048e2b115893bd80b83c3ac56fbe2bf3362d806628de8930ca3a7bb597490e06456e78666b86950079e253618ef0507374460f55a0cb3d75fa00c7a06a27d0420bd18bf47780d141811c86417b072a05c8e429e073a1f205d17508324fc116d0ccfa4c10068b33544389b8c4c836b90120c54ae4add4b1242fc8f2b226829a64ff43a3147e1954a5ca6c1e205736ad15f1e58e028b676130ff589ce2d32fb75553a51805807e1f271cd49722a4f929b69e8228409acda601d58e9815878a67d1a3891f53d643a973535aeae0898ddc96b995b175876186d6dde5c5d6046319669ac154461076bfb5206f3363d82c4dc60b08f2815e5c5760f7489176e1746711e18de0b6ccc61be50b168c00ef82530032fbc6100c25e832ceb59e90a52345712819182304e7a1c33fc417c541f55e631168f90047ba9a46bd7067b16bb7d1135ce6dc20bdd64ba1d3f3dc300bdfd1e73651dd91ff6ca425717d3360efe80f6263c3a74114331bf374c47f9434916822c8fc7122d07c38d6952cac861b2f18215cdf1e53ffec86024ed24ac2424421f598d453211d6af676d95404541a632646e6e747d26424d276d2fd9781117b05b1b8f47c2500a4a1026048e6318f4b9d224cc4df83da4e9df72278f0003c7470a595aa0ca0098b4bc21ff22ee4a99638b095ac7bc6dd7418055071d341bb046fc33754ee729706273025f9909691603de3c04a9295f4e42474f2dd0686869f39e107a88e30e7a99691490100e5be189c613c16cb04a67396d1104f93c2dd0304226f5c00e736e782a23c405cf17feff7c5c9492f26c0b4e0a722199054d321c8c018d42f57701359e136d5acb30f5cec918e0015137d82fbc6ee8d52a1b0b574101c5d12f2bb824b7375558492f431e321cbb960810654bb84699d8bd5ffc60df50e7eb70570b40b848dfcc8a2246199d1cc76b95765f701631ceb4eb073285782478589e4075bf106217412a25a4f1dc081b36110309ff0a679a266c188b0aea22f4319709";
const DEV_AGGREGATE_CAP: &str = "434c8d11d75dcb42c173095173a59e7657849a1cc4ecd71901ad0d3b5665f00ace3bc84005d68b40bc95fc554ca8735bdad5460c85bb5024669b270bb79dad4afa9db147ab47ac33b628d145cf6bca53cc7f5b2af41e940194edb30bd86d7960020e6469024e305fd7b93053bcc59b07d5f97a08c901fd0957171b226de39d2167cb8a6d117c83379f3e224515618558c9f53d3ffb0be30949446d60ed9650466a62b03bde84ec41a9ded60177b7095e41fd9403df53411e7f6de35cd89d0e27e6342712f859f02b0dd59802a4dd2f400b6bed5bef8ed162c90088767c54166f01db11387179e357359a8f5754208d7106700608564f607132c36b5ba86d4e718f223440465ae44545c12f4c04e6163eff591b53563dd237fe708454c0652f6895539653ada79f44eed4e8287373406b2db66f0acbb74700c8372e6fd1dfa95ff06b9f5a1f6c2b3ab96a640901463a13d88d8e05515f490db4ec680eb982bd50e64cbd478107a63b48d7f56ecda1af450bafe146b404eb25155bdc3eebbe084e4220be516a27a41e0f0f350366e6376ef92ae357b4f03b42d29923121cef214f0f9f522443988d437b57d15fe83c03258ef76773a418ba42d155432ef761af6a39c1426e1bf6c05ab32c0472325f9552d3d2691dfc48d34092ff8e046350f305ee218f3f5817695e160ad52a07c6914576cbba3986669e5c7350a334063f54154bddd500e6d0a0427833a170ff4fc910b396ef6340443d36f997ef69f370d042a807ac72ec84304d1dfe7a20262baf2bf428c41196989b48f36fcc411d077b6c71c5ec72578ffb2c972abf447b4fb20020d96d1c85bea6639a53a90b240bfe16ae8ca15701a52f38cac9c71903ee49645579862f8426de33a3595f21f32fc86380438b516168ab4cc2091045cb428e4adafd1541c6b6db412462cd69ef60922e7bc6af34d3982713be2cef6ba24c3c74bc075475c7669e2785711568ff84df2e90fe530551e70d5351f4c564f0d8dd737882ec61b572a26a04e8a6201abb924bf409d3620e64ee26888ad874ab7108082242c06775252b3699533b289c4fc40a2c33aa37ba967959f522fd36fe1ff836f9f0043043128b5ca6596451ccda386ab026a9074e7e2c49c6054e40c6a16e08c920d65604a8a22f642bda64c2b7935dd0beab2500cc060ad7936f6c444bd04b62f1765901c40d39f03af807e6a9e42ac66ca13a6ecb57371c696415d0d8d069f5f25659cb77fd5d2637b774cce3cd1374563b27dc098d600de8843a86c7da45b48cf1619b788250ce80043de3338f64806bb012b5390c38da11166acaddf819606619521c6b6261e2a65f01f030693ea25a7544e30acc411d8b3c4800be840504c4ff63b999916943d0e617f2bc9f0928e5ad515f7d7c0ba5ddff7345e07449a39a515bfefaf837861a675069512b26";

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
    /// `state` says.
    pub fn verify(&self, inputs: &[[u8; 32]], outputs: &[[u8; 32]], nonces: &[[u8; NONCE_LEN]], state: &StateChange, reward: u64) -> bool {
        if !inputs.iter().chain(outputs).all(is_canonical) || nonces.len() != outputs.len() {
            return false;
        }
        verify_tree(&self.bytes, inputs, outputs, nonces, state, reward)
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

/// What a root proof is checked against, for this body and state change;
/// `None` if the proof's header doesn't parse.
fn claim(bytes: &[u8], inputs: &[[u8; 32]], outputs: &[[u8; 32]], nonces: &[[u8; NONCE_LEN]], state: &StateChange) -> Option<(RootClaim, stark::Proof)> {
    let (amounts, aggregated, data, rest) = parse_header_and_rest(bytes)?;
    let claim = RootClaim {
        inputs: elements(inputs),
        outputs: elements(outputs).into_iter().zip(nonce_elements(nonces)).collect(),
        state: *state,
        aggregated,
        data: digest_from_bytes(&data),
        amounts,
    };
    Some((claim, stark::Proof::from_bytes(rest)?))
}

/// A block proof's tree root, as a chain step verifies it
/// (`chain_step`): for this body and state change. `None` if the proof
/// doesn't parse; whether it verifies is `Proof::verify`'s question.
pub fn block_root(proof: &Proof, inputs: &[[u8; 32]], outputs: &[[u8; 32]], nonces: &[[u8; NONCE_LEN]], state: &StateChange) -> Option<aggregate::Node> {
    let (claim, root) = claim(&proof.bytes, inputs, outputs, nonces, state)?;
    Some(tree_verifying_key().root(&claim, root))
}

fn verify_tree(bytes: &[u8], inputs: &[[u8; 32]], outputs: &[[u8; 32]], nonces: &[[u8; NONCE_LEN]], state: &StateChange, reward: u64) -> bool {
    if state.count_out.checked_sub(state.count_in) != Some(outputs.len() as u64) {
        return false;
    }
    match claim(bytes, inputs, outputs, nonces, state) {
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
        witnesses.push(block_air::build_chunk(&txs, net, CHUNK_SHAPE).ok()?);
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
    proof.verify(inputs, outputs, nonces, &state, plan.reward).then_some((proof, root))
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
        let (root_in, base) = (tree.root(), tree.count());
        let end = base + body.outputs.len() as u64;
        let mut transitions = Vec::new();
        let mut count = base;
        for indices in &chunks {
            let mut ins: Vec<[u8; 32]> = indices.iter().flat_map(|&t| &txs[t].inputs).map(|i| Output::new(&i.pubkey, i.amount).commitment()).collect();
            let mut outs: Vec<[u8; 32]> = indices.iter().flat_map(|&t| &txs[t].outputs).map(|o| o.commitment()).collect();
            ins.sort();
            outs.sort();
            let (root, count_in) = (tree.root(), count);
            let mut t_inputs = Vec::new();
            for slot in 0..CHUNK_SHAPE.inputs {
                match ins.get(slot) {
                    Some(c) => {
                        let p = tree.position_of(&leaf(c, &zero)).unwrap();
                        t_inputs.push((p, zero, tree.path(p)));
                        tree.spend(&leaf(c, &zero));
                    }
                    None => t_inputs.push((end, zero, tree.path(end))),
                }
            }
            let mut t_outputs = Vec::new();
            for slot in 0..CHUNK_SHAPE.outputs {
                match outs.get(slot) {
                    Some(c) => {
                        let o = body.outputs.binary_search(c).unwrap();
                        let p = base + o as u64;
                        t_outputs.push((p, tree.path(p)));
                        tree.place(p, leaf(c, &body.nonces[o]));
                        count += 1;
                    }
                    None => t_outputs.push((end, tree.path(end))),
                }
            }
            transitions.push(ChunkTransition {
                change: StateChange { root_in: root, count_in, root_out: tree.root(), count_out: count },
                window: (base, end),
                inputs: t_inputs,
                outputs: t_outputs,
            });
        }
        TestBlock {
            inputs: body.inputs.clone(),
            outputs: body.outputs,
            nonces: body.nonces,
            txs,
            plan: BlockPlan { chunks, transitions, reward: REWARD },
            state: StateChange { root_in, count_in: base, root_out: tree.root(), count_out: end },
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
            assert!(!proof.verify(&b.inputs, &b.outputs, &b.nonces, &b.state, REWARD));
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
        assert!(!Proof::from_bytes(good).verify(&b.inputs, &b.outputs, &b.nonces, &b.state, REWARD));
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
        assert!(proof.verify(&b.inputs, &b.outputs, &b.nonces, &b.state, REWARD));
        println!("verified in {:.2?}", start.elapsed());
        // Other lists, a different claimed split of the totals, or another
        // state change.
        let mut other = b.outputs.clone();
        other.swap(0, 1);
        assert!(!proof.verify(&b.inputs, &other, &b.nonces, &b.state, REWARD));
        let mut bytes = proof.as_bytes().to_vec();
        bytes[1] ^= 1; // A
        bytes[9] ^= 1; // B, keeping A - B
        assert!(!Proof::from_bytes(bytes).verify(&b.inputs, &b.outputs, &b.nonces, &b.state, REWARD));
        let mut state = b.state;
        state.count_out += 1;
        assert!(!proof.verify(&b.inputs, &b.outputs, &b.nonces, &state, REWARD));
        let mut nonces = b.nonces.clone();
        nonces[0][0] ^= 1;
        assert!(!proof.verify(&b.inputs, &b.outputs, &nonces, &b.state, REWARD));
        // A one-chunk block: its root is the wrap.
        let small = block(vec![reward_tx(REWARD)]);
        let proof = prove_block(&small.inputs, &small.outputs, &small.nonces, &small.txs, &small.plan, [5; 32]).unwrap();
        assert!(proof.verify(&small.inputs, &small.outputs, &small.nonces, &small.state, REWARD));
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
                assert!(proof.verify(&b.inputs, &b.outputs, &b.nonces, &b.state, REWARD));
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
