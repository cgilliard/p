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
const WRAP_CAP: &str = "d14a9c2d563fe773a5ced341ca7cc74793533537736f8311c9fe0f2017b3ea1fca4ee91cb087ef41170b181603a65d6421be0b2036463c0b816cce2a8ff1d420ed3299277c82c33cbba14b2b7a824d6991e39224d81b70364a7c034146db5d2bfaf5ea0482ebc634de5c253d97a7d5085ee3b63d3c4ae8326e29ba52c9a6b21fa0762c32e1d0526cb93c0d014b5f506dbf83ec07d3f55262fe7e0d2db3d592242829e93ae1aef07032e2b763ceb8605dae32d046e3b47b54ab56ee2f7529880077cc3c0cb189330248520313daac610d6a66b5415048d243f967d64813db8315bc41062eee6a5d28285134487f15a51fc04b0f24f76e7d3ff2213722320d44660b81ae49d89ac470ca579c2914f32455532f2018d4e71b2b9dd1c7045c16516ac497f81fe4dbb906ac3f7b41e93811307ea26a1e3698ba2c6e323f4084a878268894f030ff62370578b2be4051aaf76cd37c8e50ce38461fcc264101da99084916049e386702ba70fa248b17cb028f51d0a8fa249cdf4434e3af4524cbd79909bf11f3127700773c43df521a67d4c54d502f8b480c5d76286ccb663ba5a5a9651f1a584e57b8ff3777f2294f01336b3fec8420775be33160903d734ab665eb2ff760154410c9191ad7516e093e3e6134198af80dc8316f514e49f23c5d774b6dd00ab92284bbe275089fab73dd1e2f4f419b836f337a2168f2708b0f4c929c2c0c04920d6bd307692ba1ef17679fdf4acfc90d12f25c8f4ddff09b35ef104b5bc7563b55f9a6e3039ebd8c476f5e6a30d0336947717a900a9be27904e2fd2d2063304e541c266b6b8b5a8862a44b051ee7e91f2d14be2b37422d3664604d472dd27d9f6e07a5813eedffc3184fa5f12c7983e91604fbcd2b9146170e928f9750f1b9f23ba1f9fb0b0aa7c3335ce51b51b9146e15791470049ccea72db233fd28db6273490b12242c8aa647174e78bb51fe00fa3734174f7464999d150aac3d732856e7522966da70dd007b1845310d5c1053963eabe83b50b8e4586819d9c00d8d9dbb4353842b2488ca580da3edfc1433d8c101411a772e6f36924a91e0145c853908677d32cd64ace72523a086a31b49f27f2cc706553993c3c4724eec2f4d05890c55fd29ce54ded87e00fd680635ba7b903fb34cb065d55d6f384a568873f8611200cdf4c477f602880538de511b5e0edf41f5fb6558ad89296a40417f15f71a822d7b16f83851044f2d7631711f5054ca7261eb1e05a447bd3d0c18a85e0e0b37004547537212f900265231d15c6d02dd0ce2970349a303436af6049f01040d4e60c98e680f07be3d0a5de66911e6771636fe07b42a3a5dcc2165db26498c3bf401f3974b5b9368586cc935dd331cb51d1cf5a8fd437818460e34ded46556cca860d356042392cdb4488670bc7533a91e143c81055718add767cc069e56";
const AGGREGATE_CAP: &str = "b480ee0edae0de1926c2e9075823c1552b9af852843dd45c53a598383a8b770e12487841f720f267ab984135cba3ab5af171553ec461ca2d3ce41111d84970526fe94a0fa3c54561f820056461b8244d37f0ba65f4ebff474d65ad0ba9c73e689c14c965dd7c7f68ec81050f992af04a6270eb5c4b1eb3140f51ba10e1f08c751583da4bbaa02534a1ed890c848a8a241194c87735e975352435b50a86b3f94d31c61d6aa992d533947b304a1bd0be4f11fd423d85d16d6babba7e6f5105b86a2db67c47e7f3a361636a5116bef2d41557908d2b5292d916e5b7c1171055e418bf0b3e1f7ffb5563dd7688204b8959374076976e92d9f90cfcaa2f4f16df22577edab87300da6c555e31ab1fb1d9d64c206f066e05a0cc007fd19f1a337cac3768774912266f6076501f310c8612633782fea54ef25fad034c9d255e8ef24553639f692ba5b3564f070f270d8bfd344d68a783250cd1831edad2a7108a22ed0d47c1f759ff77ff033f7cb30cddc23f5963abb21770300d18e5378b141e6acf4bf3577e5a5bec6140f34c4956d1cc7841780aea3fc1f5886802e2a708ad1a0c413bedb65a2e8cea4d89b90b24b80c4f36f8f9910ea2ea2144abeff80d5ccc307738e4de2cbd27385f0506f1716191794cdb77c931fd91ed271f7c2218fc1fa85b20686a3da1cd510f0a4f325a154f9a518794c030e07fb03b59ee584b6d016e0c0388c7495774e441b4f160178113241bba77054a0c12de6b3a5ec3593c001e5d92d0a3489b62a5579acc4a0bcd0ea220c37f9c3c4353c4708f1f5520b2f7de6c4784855f7676ca3a4247415d2982c72c9282b652cf50d933eb39011d2ac8145d6c7cec6ea6db803bc2844104e903435fced4eb2fc3d867207806d00517327e3ed1897836de841d082432ba22b6e86b066b5efa71bd177673bbc70e2c1799dd61e3627444f393546218177b5c39c933435f67ba3496cf6e16f6073e2aec94b070744ba0137691343046a4b04cf989242468dfaa6c7c4d52220022e56acf136547ecc8e40092f9507494ae2d5fc382c572c443e935a26d042f1616244bb59a3f4ad861e256170c960ec32e6e418544bd3b10754462c354ec1166aded55632b0a6effb63e55cac86f20c680485f9bd8d434d7626b4ae50b8105f43d64096d7fa33cfbdbd10c6902e95c37c4fb441ed9053a0e547a1be44e8b22d658cb156be2705e8054bc2a6656ea57e7e63b54f1885858b91d732efce0c12b821d123cd0b3092c70ff772cbfd8155a35aecd0cee02cc45f21993482bad0320bf24c5665fb06d517d4bb82b1613e00d5b22635a2ec6df1816d8eb5140b858449783856cd1728f20524c3962cdd940329f6f036bcce4696a6cabc12ae1fa87034dc6994497514a391eaabf4d3ba3e41962a24630c2a6a008a5d24c12bab8435ede4355595f65b16a";

fn cap_from_hex(hex: &str) -> Vec<[u8; 32]> {
    let bytes: Vec<u8> = (0..hex.len() / 2).map(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap()).collect();
    bytes.chunks_exact(32).map(|c| c.try_into().unwrap()).collect()
}

fn cap_to_hex(cap: &[[u8; 32]]) -> String {
    cap.iter().flatten().map(|b| format!("{b:02x}")).collect()
}

/// The dev network's verifying keys (`tree_keys` with `NETWORK=dev`).
const DEV_WRAP_CAP: &str = "374d1b0313ac465759c9ae432439ea16edb83d58f82c3429cc71b71c5d666d2cac756148207507654876872b9be5cc0f4f418a155a3513097d734517a6615e60d6fa3c13f75b752ac9add07437d0ed1c79acb45a82b5d952a049f8189cc3cd6437290a65b10b676bb2385122892ffe2bda315b3507f4b410f4f9093a23ff0a2f3a14065a92b7de710500c00de316403f2c16d85efc63f63f34f1453008088923770d27495a3838474820ae101b11dd0f6d472d27365a4545aa9b846610c8f053532a0523a84a1a4ff6700b085f758d6aa1f3445dab98f406e84595046b5599176bddbc5cc4f93b6f192a643d6bd5613f1208ad1c07579b17d1a89c2dadd3603e8127b000b6676a70b92e30138632534e62794721de05742aa08fce66132296611bf1e840fbdeba4cb1411f4597692d6aaa4949498be7c026144f1d3d18b41e2fbd84b30fa458385eb18cbc36b0384d7503bf0a23206c8368ae39bb51a4e28e62c115460418ec706bd886570d08195d41868b4730618f956854d7e91c9c997050f0b5e6642d31694542b8121d88952a7359da145681f9064c5b9bbd30385eba319ae0a519da76192d2767780429e01072d27075288b6506057bc2474c76ae854ba2e5bc4640d19f75163d3224bc8e2e63bc9deb41489c9150b1791a5146816c5ef1f68422b262e72e763d843bae75c56d8c3e221c1f8757074bae56538ecad002fa3a6c74841d175fd9982503939d672389c4dc053fbb7a2dd4188c2793fede3b1b9a651d3dcde52ff859df53c0692b319456ad76c04bfb4e6093db0548325b5f417f0b50349b734d847ac23867fa3c1064c3a905cce4a465371d0f438ed55f0a4126324059e9732359dfb96d1b4c6a37669ab95faca8b757fbc5c5470b6af91aa70901053e31cb0a8b80475c3f4ab15fb43fb71215cb5d166d368e673fdd8311a610443d8f48a61c805b3b520984ac3dd46a8a1688822d331a1ae517ea2b0a077df11026668bce5b0dd6b356fa10b42cd00dde0b03c4bb042ee64663bb851b693873d91c8b0a8f04c7e1022f2692510a6166ef32e78ff912b7f8181752cdc5576f5715303ad297528da5421cc7139a4c4b563a013ae6dc2fcdc884736c3e336ee3df38342836b46dee40133c58f5db677961603176e78341ba334a23b5e8476f409c0e1b4f322a738a56cd4e05286f5ad6e291351eabac099d807a3aabd68047809c853fc897ca24079cc153afbaf909430b1f3de1d5ed7225949a157124eb736f96de38bbe2eb09b5608727b2964113893551632371602dbb3e0a6c2a84960d1d9f6d3b6a5f786a0d8734395d28e0455685266f19bf7a61c813be11ca19af4bee0a586df3d5bb6df95794258dacbc2e3306a77329572b1e97731419f5ec4d3a76389d17c77d146bbb91281c6ae3942d51f95c54b9b92227b43e0f6c53313049";
const DEV_AGGREGATE_CAP: &str = "eba092057f896c4008e1554f791b10616526766dd31966226db9e44ec6fbf91efbf28070194a30760475027426ff50134cea507545c3054d643f5510d62df50b50c7344b67457505e359a7543dd8f2515d64974711377a697bed354b67f49228c73d0d695263a5024f1e0d7275716b66a154866e1b71b9566cf98830f26286254fa4c042013166684450d94d06c4c01177ea0742a4706910d896f647192d6c2f6d875d0b7ff3cf3697ec3b1eedce6d5613932276ced61b5aaa0ba43703b09c18034276148abc6626e3e3df0d0502a406e464c80453ef95196a80166fb6c46c3ee22ac80cefc65a5c10edd46e86a1c76372fba21cb6345d304b71e9086cbffc61aa1d2d10950e6d672c530e14c0615c360fc76708e53211596cf52a736d86810bc2f802366634b85319768f702660953363432847f756a04d1fa048694ca48f61d624a31dd5a38d3d64907f0026312c0790334e5b21d49864c82ab935291e6a04cd03e53d82fce514e38e6f74407b6311ad63366902238041ace4bb53ae7c2a72e31a8c762c631f411fc28c4caa188239eacfb30de5157142d2d4eb4524d101465b809f7060879b13f74105639c4b0d1185534d4d2a8da9348cfdd92b267065392b2ace503f34196a61764b3b13031c734f924d1a5b0e6b3ff08b55619559a2230ad5245df8c77765b242695d1716ab5d99b49146c7ee1d5bbbdb2544f6781829e012bd018ee36059e0ceef0f7cddf8139d1636093e033a06770f8525c9f7483165e4466a388f833b85d9861fc3c7741f7804f72b6a5a9c070411db0bbf81c7141bc3a565b6837203b8406c754e22a443849a221645e78f49f04c920bae177012ca09af54b9387f399835f15d48a2fc60dd46133f99fd4136a4571d1529991d1efba698142dc35248856fd6249b56502a94d98617b994ba44185c61388a8fb93042fee15d7b14fb54ceeb144b39a9404f10aa583017c31c01cf3dc3713ce0e1378d8b784d1c73714525bf92192c54e643ddf6e94343ed662b9bf27c54537801357f1d7a53de47380703fc276029fd583c75f1cf61a80c1d349a30a1193ed9fd75e0a4711fc5ea3d5dc7a31e58645f9f53f37fa84c919a742cb970250e555e984b207c756291ef260f16e75f6b3cb1ec3c9f94844273fbaf27dfb85630e776222c52311d5282ac694d3670986a5514b952de36b7681499494a86d7327079a940369652f8261103e63bc7d5883839a62232a64dd05b5e3e9d628025111bfe9c2e6e5b82c83f3b3304376ca0912ba1382738ee0b556c82d29b68da73d120add0692b1e2d8152334c5f3a46386401629a4c22728f6154aaf5d504f8c4f32fbe4d47374989596b8626b172b509464643008d2c5d7fbf3053ee8a153d1dd443852de264cd090e2c4de19828f7f4b5598459c12559858b206d302141a98fbb366d73962e";

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
