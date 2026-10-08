//! A block: a header committing to a flat, canonically-ordered body of
//! spent inputs and created outputs, plus the proof attesting to them
//! (see `BlockBody`'s docs -- the proof lives there, not as a separate
//! field on `Block`). See `docs/BLOCK.md` for the full design
//! discussion; this module is its implementation.
//!
//! **Both inputs and outputs are bare 32-byte commitment hashes --
//! `H(H(pubkey) || amount)` -- never a plaintext pubkey or amount.** An
//! output publishes that hash when it's created; spending it later
//! republishes the exact same hash. Nobody outside the prover ever learns
//! what's behind it: not the owner, not the value. This is what makes
//! the state tree's leaves, this body, and the `utxo` index all the same kind of
//! opaque value everywhere -- there's no plaintext form of this data
//! anywhere on-chain to leak, by construction, not by discipline.
//!
//! **This module knows nothing about chain state.** `Block::validate`
//! checks only what's intrinsic to the block itself -- proof of work, and
//! that the header's `body_hash` actually matches the body -- with no
//! `StateTree` or `UtxoIndex` anywhere in sight. Resolving spends
//! against real chain state, catching double-spends, and applying the
//! resulting updates are all a different, separate concern:
//! `chain::Chain::apply_block` builds on top of this module to do that.
//! Balance is never checked anywhere in plaintext, there or here, now or
//! later -- see that module's docs for why. A real full node's job, in
//! the end state, is just: check proof of work, check that a ZK proof
//! verifies. The proof is what attests that every commitment was properly
//! authorized and that everything balances; nothing in plaintext needs to
//! duplicate that check once the proof exists.
//!
//! **`Transaction` is only ever used as an *ingestion* type here, never
//! stored.** `BlockBody::add_transaction` is the only way to put anything
//! into a body: it checks `tx.verify()` (a basic sanity filter at
//! assembly time -- did this transaction's own signatures check out),
//! computes each input's and output's commitment hash from the real
//! (pubkey, amount) data `transaction::Input`/`Output` carry, and folds
//! only those hashes into the body's flat, sorted lists. Everything else
//! -- the real pubkeys, the real amounts, the signatures -- is discarded
//! right here; nothing downstream of this function ever sees it again.
//!
//! There's no "coinbase transaction" to detect, either: a `Transaction`
//! with zero inputs verifies just fine (nothing in `transaction::verify`
//! checks balance at all -- see that module's docs), so a miner can build
//! their reward-plus-fees claim as an ordinary `Transaction` with no
//! inputs and feed it through `add_transaction` like anything else.
//! Nothing on the plaintext side ever constrains how much that's allowed
//! to total -- that's the future ZK proof's job, permanently (see
//! `chain`'s module docs).

#![allow(dead_code)]

use crate::poseidon2::hash_bytes_32;
use crate::pow;
use crate::prover::Proof;
use crate::recovery::NONCE_LEN;
use crate::transaction::Transaction;

/// Errors from decoding a `BlockBody`/`Block` from bytes. Encoding never
/// fails.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The buffer ended before a declared record count did, or had
    /// leftover bytes after the last record.
    Truncated,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Truncated => write!(f, "buffer ended before the declared record count did, or had trailing bytes"),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

/// The largest a block may be, encoded (`Block::to_bytes`) -- a consensus
/// rule, checked by `Block::validate`. Covers everything a block carries:
/// header, commitments, and the proof (whose bytes join `to_bytes` once
/// the real one exists -- the stub has none yet). Also what bounds how
/// much a peer can make this node download for one block (`transfer`).
pub const MAX_BLOCK_BYTES: usize = 2 * 1024 * 1024;

/// The proof-of-work target used for the very first retarget window,
/// before `chain::Chain` has adjusted anything: first byte zero, the
/// rest maxed out, so a candidate hash meets it iff its own first byte
/// is exactly zero -- true for a uniformly random hash with probability
/// 1/256. Not a fixed, chain-wide constant any more -- see `chain`'s
/// docs on difficulty retargeting -- so `pow_valid`/`validate`/
/// `mine_header`/`mine_block` all take the actual target to check
/// against as an explicit parameter, rather than assuming this one.
pub const INITIAL_MAX_HASH: [u8; 32] = {
    let mut b = [0xffu8; 32];
    b[0] = 0x00;
    b
};

/// `version` (4 bytes), `prev_hash`, `state_root`, `body_hash`,
/// `aux_hash` (32 bytes each), then `output_count`, `height`, `timestamp`
/// (8 bytes each), and `nonce` (32 bytes) -- `BlockHeader`'s fixed encoded
/// width.
///
/// `height` **is** a header field, deliberately -- a full node
/// replaying every block from genesis could always reconstruct it by
/// counting, but a light client verifying a single block (or a single
/// recursive proof) without downloading the rest of the chain has
/// nothing to count. Putting it here, covered by PoW like every other
/// field, is what lets anyone learn a block's height directly from the
/// block itself, without trusting an unverifiable claim or replaying
/// anything. See `chain::Chain`'s docs for how a full node still
/// double-checks a claimed height against what it already knows.
pub const HEADER_LEN: usize = 4 + 32 * 4 + 8 * 3 + 32;

/// The block version this node builds, and the least any block may carry
/// (consensus, proven by chain proofs too). A future change of the rules
/// raises it from some height on; until then a miner can set a higher
/// version to signal it's ready for the next one.
pub const BLOCK_VERSION: u32 = 1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockHeader {
    /// The rules this block follows: at least `BLOCK_VERSION`.
    pub version: u32,
    pub prev_hash: [u8; 32],
    /// The root of the chain's state tree after this block
    /// (`state_tree`): every output ever created, by position -- each
    /// unspent one's commitment, or spent.
    pub state_root: [u8; 32],
    pub body_hash: [u8; 32],
    /// Any 32 bytes the miner chooses, with no meaning to consensus: a
    /// standard place to commit to other data -- the root of a Merkle
    /// tree of documents being timestamped, say -- so nobody needs to
    /// make outputs for it. Covered by proof of work like every field,
    /// and so by the chain proof.
    pub aux_hash: [u8; 32],
    /// How many outputs the state tree holds after this block: the
    /// position the next output gets.
    pub output_count: u64,
    /// How many blocks precede this one (the first real block is height
    /// `0`). See `HEADER_LEN`'s docs for why this is a header field.
    pub height: u64,
    /// Unix time, in **milliseconds**, this header was assembled, as
    /// claimed by whoever built it. `chain::Chain` checks it two ways:
    /// strictly later than the parent's, and no more than
    /// `MAX_FUTURE_DRIFT_MS` ahead of the checking node's own clock.
    /// Committed to by PoW just like every other field, so it can't be
    /// altered after mining without invalidating the nonce.
    /// Milliseconds, not seconds, so a short
    /// retarget window (`chain::DifficultyConfig`) can target sub-
    /// second block times for fast tests without losing precision --
    /// `u64` milliseconds since the epoch doesn't overflow for about
    /// 584 million years, so there's no practical ceiling to worry
    /// about from the extra precision.
    pub timestamp: u64,
    pub nonce: pow::Nonce,
}

impl BlockHeader {
    /// Serialize to exactly `HEADER_LEN` bytes: the nine fields,
    /// concatenated in field-declaration order (the numbers big-endian).
    pub fn to_bytes(&self) -> [u8; HEADER_LEN] {
        let mut out = [0u8; HEADER_LEN];
        out[..HEADER_LEN - 32].copy_from_slice(&self.pow_preimage());
        out[HEADER_LEN - 32..].copy_from_slice(&self.nonce);
        out
    }

    /// Decode from bytes, the inverse of `to_bytes`. Every field is a
    /// fixed-width plain value, so the only way this can fail is `bytes`
    /// not being exactly `HEADER_LEN` long -- checked explicitly here
    /// (rather than taking a `[u8; HEADER_LEN]` and pushing that check
    /// onto every caller) so decoding a buffer of untrusted or
    /// attacker-controlled length can never panic, only return
    /// `Err(Error::Truncated)`.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != HEADER_LEN {
            return Err(Error::Truncated);
        }
        Ok(BlockHeader {
            version: u32::from_be_bytes(bytes[0..4].try_into().unwrap()),
            prev_hash: bytes[4..36].try_into().unwrap(),
            state_root: bytes[36..68].try_into().unwrap(),
            body_hash: bytes[68..100].try_into().unwrap(),
            aux_hash: bytes[100..132].try_into().unwrap(),
            output_count: u64::from_be_bytes(bytes[132..140].try_into().unwrap()),
            height: u64::from_be_bytes(bytes[140..148].try_into().unwrap()),
            timestamp: u64::from_be_bytes(bytes[148..156].try_into().unwrap()),
            nonce: bytes[156..188].try_into().unwrap(),
        })
    }

    /// Everything the header commits to except the nonce -- what
    /// `pow::verify`/`pow::mine` actually hash, re-hashed with a new
    /// nonce on every mining attempt. Includes `height` and `timestamp`
    /// (so neither can be altered post-mining without redoing the proof
    /// of work, same reasoning Bitcoin hashes its timestamp too).
    /// Doesn't need to separately mention the proof: `body_hash` already
    /// commits to it (see `BlockBody`'s docs), so PoW covers it
    /// transitively.
    pub(crate) fn pow_preimage(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(HEADER_LEN - 32);
        bytes.extend_from_slice(&self.version.to_be_bytes());
        bytes.extend_from_slice(&self.prev_hash);
        bytes.extend_from_slice(&self.state_root);
        bytes.extend_from_slice(&self.body_hash);
        bytes.extend_from_slice(&self.aux_hash);
        bytes.extend_from_slice(&self.output_count.to_be_bytes());
        bytes.extend_from_slice(&self.height.to_be_bytes());
        bytes.extend_from_slice(&self.timestamp.to_be_bytes());
        bytes
    }

    /// This header's id -- what a following block's `prev_hash` points
    /// to (`pow::header_id`: one permutation of the hashed header and the
    /// nonce, the same one every mining attempt computes).
    pub fn hash(&self) -> [u8; 32] {
        pow::header_id(&self.pow_preimage(), self.nonce)
    }

    /// Whether `nonce` actually satisfies `target` for this header, under
    /// proof-of-work parameters `pow` -- computing the dataset items it
    /// needs (no dataset). `target` is supplied by the caller rather than
    /// a fixed constant: the right target for a given height depends on
    /// chain history (see `chain`'s docs on difficulty retargeting).
    pub fn pow_valid(&self, target: &[u8; 32], pow: &pow::Params) -> bool {
        pow::verify(&self.pow_preimage(), self.nonce, target, pow)
    }
}

/// Insert `value` into `list`, keeping it sorted ascending -- an
/// insertion sort (`partition_point` finds where, `insert` shifts the
/// rest over), shared by both `BlockBody::push_input` and `push_output`
/// now that both lists hold the exact same kind of value.
fn insert_sorted(list: &mut Vec<[u8; 32]>, value: [u8; 32]) {
    let pos = list.partition_point(|existing| *existing < value);
    list.insert(pos, value);
}

/// A canonically-ordered, flat payload: every spent input and every
/// created output, across the whole block, as bare commitment hashes,
/// plus the proof attesting they're properly authorized and balance --
/// see the module docs for why there's nothing else here, `transaction`
/// for how a commitment hash actually gets computed, and `prover` for
/// what `proof` is (today, a stub -- see that module's docs). The proof
/// is treated as part of the body, not a separate sibling on `Block`:
/// `body_hash` commits to it right alongside `inputs`/`outputs`, one
/// hash covering everything below the header.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BlockBody {
    pub inputs: Vec<[u8; 32]>,
    pub outputs: Vec<[u8; 32]>,
    /// Each output's recovery nonce (`recovery`), in `outputs`' order:
    /// `nonces[i]` belongs to `outputs[i]`. Not covered by the proof --
    /// the owner checks it -- but covered by `body_hash`, so by the
    /// header's proof of work. `Block::validate` requires exactly one
    /// per output.
    pub nonces: Vec<[u8; NONCE_LEN]>,
    pub proof: Proof,
    /// The **parent's chain proof** (`chain_step`): that the parent block
    /// is the tip of a valid chain from genesis -- every block's proof,
    /// state transition, proof of work and retargeting, recursively. It
    /// can't be in the parent itself (it attests the parent's header,
    /// nonce and all). Empty for the genesis block. Encoded bytes of the
    /// proof; what it attests is checked against the chain
    /// (`chain::Chain`'s apply).
    pub chain_proof: Vec<u8>,
}

/// Which body layout `body_hash` commits to -- 3 since blocks carry their
/// parent's chain proof (2: outputs carry recovery nonces). Part of the
/// hashed bytes, so a chain stored under an older layout (whose genesis
/// hashes differently) is refused at startup rather than misread.
const BODY_VERSION: u8 = 3;

impl BlockBody {
    pub fn new() -> Self {
        BlockBody {
            inputs: Vec::new(),
            outputs: Vec::new(),
            nonces: Vec::new(),
            proof: Proof::default(),
            chain_proof: Vec::new(),
        }
    }

    /// Fold `tx`'s inputs and outputs into this body: compute each
    /// input's commitment from its real (pubkey, amount) and each
    /// output's commitment from its real (pubkey_hash, amount), then keep
    /// only those hashes -- `tx` itself, signatures included, is
    /// discarded once this returns. Returns `false` without modifying
    /// anything if `tx.verify()` fails (a sanity filter at assembly time,
    /// not a security property this module enforces -- see the module
    /// docs).
    pub fn add_transaction(&mut self, tx: &Transaction) -> bool {
        if !tx.verify() {
            return false;
        }
        for input in &tx.inputs {
            let commitment = input.commitment();
            self.push_input(commitment);
        }
        for output in &tx.outputs {
            self.push_output(output.commitment(), output.nonce);
        }
        true
    }

    /// Build a fresh body out of `transactions`, folding each in via
    /// `add_transaction` in order. The one place this assembly loop
    /// lives -- callers (block assembly for mining, `chain::Chain::
    /// build_block`) just hand over the list, rather than each
    /// reimplementing "loop, add, bail on the first one that doesn't
    /// verify." Returns the index of the first transaction that failed
    /// `add_transaction`, if any, with nothing from it (or anything
    /// after it) folded in.
    pub fn from_transactions(transactions: &[Transaction]) -> std::result::Result<Self, usize> {
        let mut body = BlockBody::new();
        for (i, tx) in transactions.iter().enumerate() {
            if !body.add_transaction(tx) {
                return Err(i);
            }
        }
        Ok(body)
    }

    /// Insert `commitment`, keeping `inputs` sorted ascending -- this is
    /// what lets two blocks assembled from the same transactions in a
    /// different order still produce the same `body_hash`.
    fn push_input(&mut self, commitment: [u8; 32]) {
        insert_sorted(&mut self.inputs, commitment);
    }

    /// Insert `commitment`, keeping `outputs` sorted ascending -- same
    /// reasoning as `push_input` -- and its nonce at the same position.
    fn push_output(&mut self, commitment: [u8; 32], nonce: [u8; NONCE_LEN]) {
        let pos = self.outputs.partition_point(|existing| *existing < commitment);
        self.outputs.insert(pos, commitment);
        self.nonces.insert(pos, nonce);
    }

    /// Hash of the complete body: every input commitment in sorted
    /// order, then every output commitment, also sorted, then the
    /// proof's own commitment -- one hash covering everything below the
    /// header, proof included (see the struct docs). What the header's
    /// `body_hash` commits to.
    ///
    /// Exactly: `BODY_VERSION`, then each list (inputs, outputs, nonces)
    /// prefixed by its length as a u32, then the proof's commitment. The
    /// lengths make the boundaries unambiguous.
    pub fn body_hash(&self) -> [u8; 32] {
        let mut bytes = Vec::with_capacity(13 + (self.inputs.len() + self.outputs.len()) * 32 + self.nonces.len() * NONCE_LEN + 32);
        bytes.push(BODY_VERSION);
        bytes.extend_from_slice(&(self.inputs.len() as u32).to_be_bytes());
        for commitment in &self.inputs {
            bytes.extend_from_slice(commitment);
        }
        bytes.extend_from_slice(&(self.outputs.len() as u32).to_be_bytes());
        for commitment in &self.outputs {
            bytes.extend_from_slice(commitment);
        }
        bytes.extend_from_slice(&(self.nonces.len() as u32).to_be_bytes());
        for nonce in &self.nonces {
            bytes.extend_from_slice(nonce);
        }
        bytes.extend_from_slice(&self.proof.commitment_hash());
        bytes.extend_from_slice(&hash_bytes_32(&self.chain_proof));
        hash_bytes_32(&bytes)
    }

    /// Whether `proof` actually attests to this body's `inputs`/
    /// `outputs`, and to the state moving as `state` says (from the
    /// parent's root and output count to the header's, its outputs at
    /// `height`) -- see `prover`'s docs -- claiming exactly `reward`. By
    /// far the most expensive check
    /// a block gets.
    pub fn proof_is_valid(&self, state: &crate::aggregate::StateChange, height: u32, reward: u64) -> bool {
        self.proof.verify(&self.inputs, &self.outputs, &self.nonces, state, height, reward)
    }

    /// `to_bytes().len()`, without building the bytes.
    pub fn encoded_len(&self) -> usize {
        4 + 32 * self.inputs.len() + 4 + 32 * self.outputs.len() + 4 + NONCE_LEN * self.nonces.len() + 4 + self.proof.len() + 4 + self.chain_proof.len()
    }

    /// Serialize: a 4-byte big-endian input count, that many 32-byte
    /// commitments, a 4-byte big-endian output count, that many 32-byte
    /// commitments, a 4-byte big-endian nonce count, that many 16-byte
    /// nonces, then a 4-byte big-endian proof length and the proof's
    /// bytes. Always produces canonically-ordered bytes, since `inputs`/
    /// `outputs` are only ever populated in that order in the first place
    /// (`push_input`/`push_output`).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&(self.inputs.len() as u32).to_be_bytes());
        for commitment in &self.inputs {
            out.extend_from_slice(commitment);
        }
        out.extend_from_slice(&(self.outputs.len() as u32).to_be_bytes());
        for commitment in &self.outputs {
            out.extend_from_slice(commitment);
        }
        out.extend_from_slice(&(self.nonces.len() as u32).to_be_bytes());
        for nonce in &self.nonces {
            out.extend_from_slice(nonce);
        }
        out.extend_from_slice(&(self.proof.len() as u32).to_be_bytes());
        out.extend_from_slice(self.proof.as_bytes());
        out.extend_from_slice(&(self.chain_proof.len() as u32).to_be_bytes());
        out.extend_from_slice(&self.chain_proof);
        out
    }

    /// Decode from bytes, the inverse of `to_bytes`. Purely about
    /// byte-level well-formedness -- a truncated buffer or trailing
    /// garbage after the last record are rejected, but this does **not**
    /// check that `inputs`/`outputs` end up canonically ordered. A
    /// well-formed-but-not-canonical result is a real, meaningful state
    /// this can produce; whether it's actually an acceptable block is
    /// `Block::validate`'s job (see `BlockBody::is_canonically_ordered`),
    /// not a decoding concern.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        fn read_u32(bytes: &[u8], offset: &mut usize) -> Result<u32> {
            let slice = bytes.get(*offset..*offset + 4).ok_or(Error::Truncated)?;
            *offset += 4;
            Ok(u32::from_be_bytes(slice.try_into().unwrap()))
        }

        fn read_records<const N: usize>(bytes: &[u8], offset: &mut usize, count: u32) -> Result<Vec<[u8; N]>> {
            // Never reserve more than the bytes actually present could
            // fill: `count` comes off the wire, and a lie there (four
            // billion, say) must fail as `Truncated`, not as an
            // allocation of hundreds of gigabytes.
            let room = bytes.len().saturating_sub(*offset) / N;
            let mut out = Vec::with_capacity((count as usize).min(room));
            for _ in 0..count {
                let slice = bytes.get(*offset..*offset + N).ok_or(Error::Truncated)?;
                *offset += N;
                out.push(slice.try_into().unwrap());
            }
            Ok(out)
        }

        let mut offset = 0;
        let input_count = read_u32(bytes, &mut offset)?;
        let inputs = read_records(bytes, &mut offset, input_count)?;
        let output_count = read_u32(bytes, &mut offset)?;
        let outputs = read_records(bytes, &mut offset, output_count)?;
        let nonce_count = read_u32(bytes, &mut offset)?;
        let nonces = read_records(bytes, &mut offset, nonce_count)?;
        let proof_len = read_u32(bytes, &mut offset)? as usize;
        let proof = bytes.get(offset..offset.saturating_add(proof_len)).ok_or(Error::Truncated)?;
        offset += proof_len;
        let chain_proof_len = read_u32(bytes, &mut offset)? as usize;
        let chain_proof = bytes.get(offset..offset.saturating_add(chain_proof_len)).ok_or(Error::Truncated)?;
        offset += chain_proof_len;

        if offset != bytes.len() {
            return Err(Error::Truncated); // trailing garbage
        }

        Ok(BlockBody {
            inputs,
            outputs,
            nonces,
            proof: Proof::from_bytes(proof.to_vec()),
            chain_proof: chain_proof.to_vec(),
        })
    }

    /// Whether both `inputs` and `outputs` are strictly increasing --
    /// sorted, with **no duplicates**. Under the commitment scheme (see
    /// the module docs), an exact repeat can only mean the same spend, or
    /// the same output, claimed twice: there's no longer a legitimate
    /// reason two honest, independent transactions would ever produce
    /// the identical 32-byte commitment, so this is rejected outright
    /// rather than deferred to chain-level resolution. `add_transaction`
    /// maintains this by construction, and so does `to_bytes`/
    /// `from_bytes` round-tripping a value that was already like this --
    /// but nothing stops a `BlockBody` from being built some other way
    /// (`inputs`/`outputs` are public fields), so `Block::validate`
    /// checks this explicitly rather than trusting it.
    pub fn is_canonically_ordered(&self) -> bool {
        self.inputs.is_sorted_by(|a, b| a < b) && self.outputs.is_sorted_by(|a, b| a < b)
    }

    /// Whether any commitment appears in both `inputs` and `outputs` --
    /// i.e. whether this block tries to spend an output it also creates,
    /// within the same block. Disallowed: an output only becomes
    /// spendable starting with the *next* block, which is what lets
    /// chain-level validation apply a block's spends and its new outputs
    /// as two independent passes against already-committed state,
    /// rather than needing to reason about speculative, not-yet-applied
    /// state partway through processing one block.
    pub fn spends_its_own_output(&self) -> bool {
        let outputs: std::collections::HashSet<&[u8; 32]> = self.outputs.iter().collect();
        self.inputs.iter().any(|commitment| outputs.contains(commitment))
    }
}

/// What `chain::Chain::build_block` actually produces: every chain-
/// state-dependent field resolved (`prev_hash`, `height`, `state_root`,
/// `output_count`, and the flat `inputs`/`outputs` lists), but no proof
/// yet, and so no `Block` yet either -- `BlockBody`/`Block` both require
/// a real `proof` (see `BlockBody`'s docs), and this type deliberately
/// doesn't carry one. `finish` is the only way to turn this into an
/// actual `Block`, and it needs a `Proof` to do it (from
/// `prover::prove_block`) -- which is what keeps `pow::mine_block` from
/// being callable on anything until proving has actually happened.
///
/// `target` isn't part of the eventual header -- it's not something a
/// block commits to, just the PoW difficulty `chain::Chain` currently
/// expects (see that module's docs on retargeting). It's carried here
/// purely so whoever's about to mine has it on hand without a separate
/// lookup; grab it before calling `finish` (which consumes `self`).
#[derive(Debug)]
pub struct UnprovenBlock {
    pub prev_hash: [u8; 32],
    pub height: u64,
    pub target: [u8; 32],
    /// The earliest `timestamp` this block may carry: one millisecond
    /// past its parent's, since timestamps must strictly increase (a
    /// consensus rule -- see `chain`'s docs). `0` for a first block.
    pub min_timestamp: u64,
    pub state_root: [u8; 32],
    pub output_count: u64,
    pub inputs: Vec<[u8; 32]>,
    pub outputs: Vec<[u8; 32]>,
    pub nonces: Vec<[u8; NONCE_LEN]>,
    /// The header's `aux_hash`: zeros unless the miner sets it.
    pub aux_hash: [u8; 32],
    /// How to prove it: its transactions' chunks and each chunk's state
    /// transition, worked out against the parent's state.
    pub plan: crate::prover::BlockPlan,
}

impl UnprovenBlock {
    /// Attach `proof` to assemble the real, still-unmined `Block`:
    /// `body_hash` is computed only now, since it commits to the proof
    /// alongside `inputs`/`outputs` (see `BlockBody::body_hash`).
    /// `timestamp` is stamped as "now," at assembly time -- later than
    /// `Chain::build_block` (which may have run well before proving
    /// finished, if proving is slow) and right before mining, which is
    /// the point at which this block is otherwise complete -- or as
    /// `min_timestamp`, if that's later (a parent stamped ahead of this
    /// node's clock). Anyone re-stamping it while mining must keep to
    /// `min_timestamp` too. `nonce` is
    /// left at `[0; 32]` -- `pow::mine_block` is the only thing that
    /// sets it, and only once this has already happened.
    pub fn finish(self, proof: Proof) -> Block {
        self.finish_with_chain_proof(proof, Vec::new())
    }

    /// `finish`, also carrying the parent's chain proof (`chain_step`) --
    /// what a block needs on a chain that requires chain proofs.
    pub fn finish_with_chain_proof(self, proof: Proof, chain_proof: Vec<u8>) -> Block {
        let body = BlockBody {
            inputs: self.inputs,
            outputs: self.outputs,
            nonces: self.nonces,
            proof,
            chain_proof,
        };
        let header = BlockHeader {
            prev_hash: self.prev_hash,
            state_root: self.state_root,
            output_count: self.output_count,
            body_hash: body.body_hash(),
            aux_hash: self.aux_hash,
            version: crate::block::BLOCK_VERSION,
            height: self.height,
            timestamp: now_millis().max(self.min_timestamp),
            nonce: [0u8; 32],
        };
        Block { header, body }
    }
}

/// The current Unix time, in **milliseconds** -- what
/// `UnprovenBlock::finish` stamps a new header with, and what
/// `chain::Chain::apply_block` reads again to bound how far into the
/// future a header's claimed `timestamp` is allowed to be.
pub(crate) fn now_millis() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock is before 1970")
        .as_millis() as u64
}

#[derive(Clone, Debug)]
pub struct Block {
    pub header: BlockHeader,
    pub body: BlockBody,
}

impl Block {
    /// Whether this block is sound *on its own*, given the proof-of-work
    /// `target` it's supposed to meet: proof of work checks out against
    /// `target`, the body is canonically ordered (sorted, no duplicates)
    /// and doesn't spend any output it also creates, the header's
    /// `body_hash` actually matches the body (proof included -- see
    /// `BlockBody`'s docs), and the proof itself checks out against the
    /// body's commitments.
    ///
    /// `target` is the one piece of this that isn't fully intrinsic to
    /// the block: the *right* target for a given height depends on
    /// chain history (see `chain`'s docs on difficulty retargeting), so
    /// the caller -- `chain::Chain::apply_block`, which has that
    /// history -- has to supply it. Everything else here is checked
    /// without touching any chain state at all. Resolving spends against
    /// real chain state, catching reuse across different blocks, and
    /// applying updates all live in `chain::Chain::apply_block` too --
    /// but duplicate-commitment, same-block-spend, and proof validity
    /// don't need any of that, since they're properties of the body (and
    /// the proof within it) alone.
    ///
    /// These checks matter here, specifically, rather than at decode
    /// time: `BlockBody::from_bytes` only checks that bytes are
    /// well-formed, not that they're canonical, and `inputs`/`outputs`
    /// are public fields a `BlockBody` could in principle be built
    /// through some other way entirely. Checking it here means
    /// `validate` is a complete answer to "is this block acceptable
    /// against this target" regardless of how the value in hand was
    /// constructed, rather than a check that's only honest if you also
    /// know it arrived via `from_bytes`.
    ///
    /// The proof also attests the state transition, so it's checked
    /// against the parent's state: `parent_state` is its `(state_root,
    /// output_count)`; and the reward, the schedule's at its height.
    pub fn validate(&self, target: &[u8; 32], pow: &pow::Params, parent_state: ([u8; 32], u64), reward: u64) -> bool {
        let Ok(height) = u32::try_from(self.header.height) else { return false };
        self.validate_structure(target, pow) && self.body.proof_is_valid(&self.state_change(parent_state), height, reward)
    }

    /// The state change this block claims, from its parent's state.
    pub fn state_change(&self, (root, count): ([u8; 32], u64)) -> crate::aggregate::StateChange {
        use crate::poseidon2::digest_from_bytes;
        crate::aggregate::StateChange {
            root_in: digest_from_bytes(&root),
            count_in: count,
            root_out: digest_from_bytes(&self.header.state_root),
            count_out: self.header.output_count,
        }
    }

    /// Everything `validate` checks *except* the proof -- every cheap,
    /// structural rule. Separate so a caller can run these first, or (in
    /// tests about other things) skip the proof entirely.
    pub fn validate_structure(&self, target: &[u8; 32], pow: &pow::Params) -> bool {
        if self.header.version < BLOCK_VERSION || !self.header.pow_valid(target, pow) {
            return false;
        }
        if !self.body.inputs.iter().chain(&self.body.outputs).all(crate::prover::is_canonical) {
            return false;
        }
        if self.encoded_len() > MAX_BLOCK_BYTES {
            return false;
        }
        if !self.body.is_canonically_ordered() {
            return false;
        }
        if self.body.nonces.len() != self.body.outputs.len() {
            return false;
        }
        if self.body.spends_its_own_output() {
            return false;
        }
        self.body.body_hash() == self.header.body_hash
    }

    /// Serialize: the header's fixed-width encoding, followed by the
    /// body's.
    /// `to_bytes().len()`, without building the bytes.
    pub fn encoded_len(&self) -> usize {
        HEADER_LEN + self.body.encoded_len()
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = self.header.to_bytes().to_vec();
        out.extend_from_slice(&self.body.to_bytes());
        out
    }

    /// Decode from bytes, the inverse of `to_bytes`. Purely structural --
    /// this checks the encoding is well-formed (right lengths,
    /// canonically-ordered body) but says nothing about whether the
    /// result is actually a *valid* block; call `validate` separately
    /// for that.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        let header_bytes = bytes.get(..HEADER_LEN).ok_or(Error::Truncated)?;
        let header = BlockHeader::from_bytes(header_bytes)?;
        let body = BlockBody::from_bytes(&bytes[HEADER_LEN..])?;
        Ok(Block { header, body })
    }
}

/// Mine `header` in place: search for a nonce satisfying `target`, up to
/// `max_attempts`, setting `header.nonce` and returning `true` on
/// success. Leaves `header` untouched and returns `false` if none of the
/// first `max_attempts` nonces satisfy it. Lives here, rather than in
/// `pow` itself, since `pow` is deliberately kept free of any dependency
/// on `block` (see that module's docs) -- this is just a thin,
/// `BlockHeader`-aware wrapper around `pow::mine`. `target` should be
/// whatever `chain::Chain` currently reports as the active target (see
/// that module's docs on difficulty retargeting) -- mining against
/// anything else just wastes work, since `apply_block` checks against
/// its own idea of the right target, not whatever was mined against.
pub fn mine_header(header: &mut BlockHeader, target: &[u8; 32], max_attempts: u64, pow: &pow::Params) -> bool {
    let preimage = header.pow_preimage();
    match pow::mine(&preimage, target, max_attempts, pow) {
        Some((nonce, _)) => {
            header.nonce = nonce;
            true
        }
        None => false,
    }
}

/// Mine `block.header` in place -- see `mine_header`. There's no `Block`
/// value to call this on until `prover::prove_block` has already run
/// (see `UnprovenBlock::finish`): that's what keeps mining from starting
/// before proving does.
pub fn mine_block(block: &mut Block, target: &[u8; 32], max_attempts: u64, pow: &pow::Params) -> bool {
    mine_header(&mut block.header, target, max_attempts, pow)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::output::Output;
    use crate::wots::{self, PublicKey, SecretKey};

    fn keypair(byte: u8) -> (SecretKey, PublicKey) {
        wots::keygen(&[byte; 32])
    }

    /// The commitment a real output/input for `(pubkey, amount)` would
    /// publish -- computed independently of `add_transaction`, so tests
    /// asserting against it are actually checking something.
    fn commitment_of(pubkey: &PublicKey, amount: u64) -> [u8; 32] {
        Output::new(pubkey, amount).commitment()
    }

    /// Mine a real nonce for `header` (with `nonce` still unset) against
    /// `INITIAL_MAX_HASH`, panicking if none is found within a generous
    /// attempt budget -- 1-in-256 odds per attempt, so this finishes in a
    /// handful of tries almost always.
    fn mined_header(mut header: BlockHeader) -> BlockHeader {
        assert!(mine_header(&mut header, &INITIAL_MAX_HASH, 100_000, &crate::pow::Params::TEST), "should find a nonce quickly");
        header
    }

    /// A nonce guaranteed *not* to satisfy `INITIAL_MAX_HASH` for the
    /// given header preimage -- used to test PoW rejection without any
    /// chance of test flakiness from accidentally picking a valid one.
    fn a_failing_nonce(preimage: &[u8]) -> pow::Nonce {
        for counter in 0u64..64 {
            let mut nonce = [0u8; 32];
            nonce[..8].copy_from_slice(&counter.to_le_bytes());
            if !pow::meets_target(&pow::pow_value_of(preimage, nonce, &pow::Params::TEST), &INITIAL_MAX_HASH) {
                return nonce;
            }
        }
        unreachable!("extraordinarily unlikely: 64 consecutive nonces all satisfied a 1/256 target")
    }

    #[test]
    fn empty_block_with_correct_pow_and_body_hash_validates() {
        let header = mined_header(BlockHeader {
            prev_hash: [1u8; 32],
            state_root: [2u8; 32],
            output_count: 3,
            body_hash: BlockBody::new().body_hash(),
            aux_hash: [0; 32],
            version: crate::block::BLOCK_VERSION,
            height: 0,
            timestamp: 0,
            nonce: [0u8; 32],
        });
        let block = Block {
            header,
            body: BlockBody::new(),
        };

        assert!(block.validate_structure(&INITIAL_MAX_HASH, &crate::pow::Params::TEST));
    }

    /// PoW is checked first -- an arbitrary (wrong) `body_hash` is fine
    /// here, since validation never gets far enough to look at it.
    #[test]
    fn wrong_pow_is_rejected() {
        let header = BlockHeader {
            prev_hash: [1u8; 32],
            state_root: [2u8; 32],
            output_count: 3,
            body_hash: [4u8; 32],
            aux_hash: [0; 32],
            version: crate::block::BLOCK_VERSION,
            height: 0,
            timestamp: 0,
            nonce: [0u8; 32],
        };
        let failing_nonce = a_failing_nonce(&header.pow_preimage());
        let block = Block {
            header: BlockHeader {
                nonce: failing_nonce,
                ..header
            },
            body: BlockBody::new(),
        };

        assert!(!block.validate_structure(&INITIAL_MAX_HASH, &crate::pow::Params::TEST));
    }

    /// A header whose `body_hash` doesn't match the actual body is
    /// rejected, even with otherwise-valid PoW (mined for this exact,
    /// wrong preimage -- PoW doesn't know or care whether `body_hash` is
    /// honest).
    #[test]
    fn wrong_body_hash_is_rejected() {
        let header = mined_header(BlockHeader {
            prev_hash: [1u8; 32],
            state_root: [2u8; 32],
            output_count: 3,
            body_hash: [0xABu8; 32], // does not match BlockBody::new()'s hash
            aux_hash: [0; 32],
            version: crate::block::BLOCK_VERSION,
            height: 0,
            timestamp: 0,
            nonce: [0u8; 32],
        });
        let block = Block {
            header,
            body: BlockBody::new(),
        };

        assert!(!block.validate_structure(&INITIAL_MAX_HASH, &crate::pow::Params::TEST));
    }

    /// A transaction that doesn't verify (unsigned) is rejected by
    /// `add_transaction` itself -- nothing is added to the body.
    #[test]
    fn add_transaction_rejects_a_transaction_that_does_not_verify() {
        let (_, pk_a) = keypair(1);
        let mut unsigned = Transaction::new();
        unsigned.add_input(&pk_a, 100).unwrap();
        unsigned.add_output(Output::new(&pk_a, 100)).unwrap();
        // Never signed.

        let mut body = BlockBody::new();
        assert!(!body.add_transaction(&unsigned));
        assert!(body.inputs.is_empty());
        assert!(body.outputs.is_empty());
    }

    /// A verifying transaction's inputs and outputs get folded in as
    /// their commitment hashes, in canonical sorted order -- not the
    /// plaintext pubkey/output at all.
    #[test]
    fn add_transaction_folds_in_a_verifying_transaction() {
        let (sk_a, pk_a) = keypair(1);
        let (_, pk_out) = keypair(2);

        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 100).unwrap();
        tx.add_output(Output::new(&pk_out, 100)).unwrap();
        assert!(tx.sign_input(&pk_a, &sk_a));
        assert!(tx.verify());

        let mut body = BlockBody::new();
        assert!(body.add_transaction(&tx));
        assert_eq!(body.inputs, vec![commitment_of(&pk_a, 100)]);
        assert_eq!(body.outputs, vec![commitment_of(&pk_out, 100)]);
    }

    #[test]
    fn header_round_trips_through_bytes() {
        let header = mined_header(BlockHeader {
            prev_hash: [1u8; 32],
            state_root: [2u8; 32],
            output_count: 3,
            body_hash: [4u8; 32],
            aux_hash: [0; 32],
            version: crate::block::BLOCK_VERSION,
            height: 0,
            timestamp: 1_700_000_000,
            nonce: [0u8; 32],
        });
        assert_eq!(BlockHeader::from_bytes(&header.to_bytes()).unwrap(), header);
        // The version leads, and counts.
        let signalling = BlockHeader { version: 7, ..header.clone() };
        assert_eq!(signalling.to_bytes()[..4], 7u32.to_be_bytes());
        assert_eq!(BlockHeader::from_bytes(&signalling.to_bytes()).unwrap().version, 7);
        assert_ne!(signalling.hash(), header.hash());
    }

    /// A block below `BLOCK_VERSION` is invalid; a higher version (a miner
    /// signalling for the next rules) is fine.
    #[test]
    fn a_block_needs_at_least_the_current_version() {
        let easy = INITIAL_MAX_HASH;
        let body = BlockBody::new();
        let block_at = |version: u32| {
            let header = mined_header(BlockHeader {
                prev_hash: [1u8; 32],
                state_root: [2u8; 32],
                output_count: 3,
                body_hash: body.body_hash(),
                aux_hash: [0; 32],
                version,
                height: 0,
                timestamp: 1_700_000_000,
                nonce: [0u8; 32],
            });
            Block { header, body: body.clone() }
        };
        assert!(!block_at(0).validate_structure(&easy, &pow::Params::TEST));
        assert!(block_at(BLOCK_VERSION).validate_structure(&easy, &pow::Params::TEST));
        assert!(block_at(BLOCK_VERSION + 1).validate_structure(&easy, &pow::Params::TEST));
    }

    /// `timestamp` is part of what PoW hashes over -- changing it after
    /// mining, without finding a new nonce, must invalidate the proof of
    /// work, the same way tampering any other committed field would.
    #[test]
    fn tampering_timestamp_after_mining_invalidates_pow() {
        let header = mined_header(BlockHeader {
            prev_hash: [1u8; 32],
            state_root: [2u8; 32],
            output_count: 3,
            body_hash: [4u8; 32],
            aux_hash: [0; 32],
            version: crate::block::BLOCK_VERSION,
            height: 0,
            timestamp: 1_700_000_000,
            nonce: [0u8; 32],
        });
        assert!(header.pow_valid(&INITIAL_MAX_HASH, &crate::pow::Params::TEST));

        let tampered = BlockHeader {
            height: 0,
            timestamp: header.timestamp + 1,
            ..header
        };
        assert!(!tampered.pow_valid(&INITIAL_MAX_HASH, &crate::pow::Params::TEST));
    }

    #[test]
    fn header_from_bytes_rejects_wrong_length() {
        let header = mined_header(BlockHeader {
            prev_hash: [1u8; 32],
            state_root: [2u8; 32],
            output_count: 3,
            body_hash: [4u8; 32],
            aux_hash: [0; 32],
            version: crate::block::BLOCK_VERSION,
            height: 0,
            timestamp: 0,
            nonce: [0u8; 32],
        });
        let bytes = header.to_bytes();
        assert_eq!(
            BlockHeader::from_bytes(&bytes[..bytes.len() - 1]).unwrap_err(),
            Error::Truncated
        );
        let mut too_long = bytes.to_vec();
        too_long.push(0);
        assert_eq!(BlockHeader::from_bytes(&too_long).unwrap_err(), Error::Truncated);
    }

    #[test]
    fn empty_body_round_trips_through_bytes() {
        let body = BlockBody::new();
        assert_eq!(BlockBody::from_bytes(&body.to_bytes()).unwrap(), body);
    }

    #[test]
    fn non_empty_body_round_trips_through_bytes() {
        let (sk_a, pk_a) = keypair(1);
        let (sk_b, pk_b) = keypair(2);
        let (_, pk_out_1) = keypair(3);
        let (_, pk_out_2) = keypair(4);

        let mut tx_a = Transaction::new();
        tx_a.add_input(&pk_a, 100).unwrap();
        tx_a.add_output(Output::new(&pk_out_1, 100)).unwrap();
        assert!(tx_a.sign_input(&pk_a, &sk_a));

        let mut tx_b = Transaction::new();
        tx_b.add_input(&pk_b, 200).unwrap();
        tx_b.add_output(Output::new(&pk_out_2, 200)).unwrap();
        assert!(tx_b.sign_input(&pk_b, &sk_b));

        let mut body = BlockBody::new();
        assert!(body.add_transaction(&tx_a));
        assert!(body.add_transaction(&tx_b));

        let decoded = BlockBody::from_bytes(&body.to_bytes()).unwrap();
        assert_eq!(decoded, body);
    }

    #[test]
    fn block_round_trips_through_bytes() {
        let (_, pk) = keypair(1);
        let mut body = BlockBody::new();
        body.add_transaction(&{
            let mut tx = Transaction::new();
            tx.add_output(Output::new(&pk, 50)).unwrap();
            tx
        });
        let header = mined_header(BlockHeader {
            prev_hash: [9u8; 32],
            state_root: [8u8; 32],
            output_count: 7,
            body_hash: body.body_hash(),
            aux_hash: [0; 32],
            version: crate::block::BLOCK_VERSION,
            height: 0,
            timestamp: 0,
            nonce: [0u8; 32],
        });
        let block = Block { header, body };

        let decoded = Block::from_bytes(&block.to_bytes()).unwrap();
        assert_eq!(decoded.header, block.header);
        assert_eq!(decoded.body, block.body);
        assert!(decoded.validate_structure(&INITIAL_MAX_HASH, &crate::pow::Params::TEST));
    }

    /// `BlockBody::from_bytes` only checks byte-level well-formedness --
    /// it happily decodes an out-of-order body unchanged. The ordering
    /// check lives in `is_canonically_ordered`/`Block::validate` instead;
    /// see `validate_rejects_a_block_whose_body_is_not_canonically_ordered`
    /// below for the end-to-end version of this.
    #[test]
    fn from_bytes_does_not_check_ordering() {
        let a = commitment_of(&keypair(1).1, 10);
        let b = commitment_of(&keypair(2).1, 20);
        let (small, large) = if a < b { (a, b) } else { (b, a) };

        let body = BlockBody {
            inputs: vec![large, small], // deliberately out of order
            outputs: vec![],
            ..Default::default()
        };
        let decoded = BlockBody::from_bytes(&body.to_bytes()).unwrap();
        assert_eq!(decoded, body);
    }

    #[test]
    fn is_canonically_ordered_detects_out_of_order_inputs() {
        let a = commitment_of(&keypair(1).1, 10);
        let b = commitment_of(&keypair(2).1, 20);
        let (small, large) = if a < b { (a, b) } else { (b, a) };

        assert!(BlockBody { inputs: vec![small, large], outputs: vec![], ..Default::default() }.is_canonically_ordered());
        assert!(!BlockBody { inputs: vec![large, small], outputs: vec![], ..Default::default() }.is_canonically_ordered());
    }

    #[test]
    fn is_canonically_ordered_detects_out_of_order_outputs() {
        let a = commitment_of(&keypair(1).1, 10);
        let b = commitment_of(&keypair(2).1, 20);
        let (small, large) = if a < b { (a, b) } else { (b, a) };

        assert!(BlockBody { inputs: vec![], outputs: vec![small, large], ..Default::default() }.is_canonically_ordered());
        assert!(!BlockBody { inputs: vec![], outputs: vec![large, small], ..Default::default() }.is_canonically_ordered());
    }

    /// Duplicate adjacent commitments (the same value twice, in order)
    /// are rejected -- an exact repeat can only mean the same spend, or
    /// the same output, claimed twice, which is never legitimate under
    /// the commitment scheme (see `is_canonically_ordered`'s docs).
    #[test]
    fn is_canonically_ordered_rejects_duplicate_inputs() {
        let a = commitment_of(&keypair(1).1, 10);
        assert!(!BlockBody { inputs: vec![a, a], outputs: vec![], ..Default::default() }.is_canonically_ordered());
    }

    #[test]
    fn is_canonically_ordered_rejects_duplicate_outputs() {
        let a = commitment_of(&keypair(1).1, 10);
        assert!(!BlockBody { inputs: vec![], outputs: vec![a, a], ..Default::default() }.is_canonically_ordered());
    }

    #[test]
    fn spends_its_own_output_detects_overlap() {
        let a = commitment_of(&keypair(1).1, 10);
        let b = commitment_of(&keypair(2).1, 20);

        assert!(!BlockBody { inputs: vec![a], outputs: vec![b], ..Default::default() }.spends_its_own_output());
        assert!(BlockBody { inputs: vec![a], outputs: vec![a], ..Default::default() }.spends_its_own_output());
    }

    /// A block that tries to spend an output it also creates is rejected
    /// by `validate`, even though it's canonically ordered and the
    /// header's `body_hash` honestly matches.
    #[test]
    fn validate_rejects_a_block_that_spends_its_own_output() {
        let a = commitment_of(&keypair(1).1, 10);
        let body = BlockBody {
            inputs: vec![a],
            outputs: vec![a],
            ..Default::default()
        };
        assert!(body.is_canonically_ordered()); // not the thing being tested here
        assert!(body.spends_its_own_output());

        let header = mined_header(BlockHeader {
            prev_hash: [0u8; 32],
            state_root: [0u8; 32],
            output_count: 0,
            body_hash: body.body_hash(),
            aux_hash: [0; 32],
            version: crate::block::BLOCK_VERSION,
            height: 0,
            timestamp: 0,
            nonce: [0u8; 32],
        });
        let block = Block { header, body };

        assert!(!block.validate_structure(&INITIAL_MAX_HASH, &crate::pow::Params::TEST));
    }

    /// The end-to-end version of the point above: a block whose body is
    /// well-formed bytes but not canonically ordered decodes fine, but
    /// `validate` rejects it anyway -- the check doesn't depend on
    /// whether the `Block` arrived via `from_bytes` or was built some
    /// other way.
    #[test]
    fn validate_rejects_a_block_whose_body_is_not_canonically_ordered() {
        let a = commitment_of(&keypair(1).1, 10);
        let b = commitment_of(&keypair(2).1, 20);
        let (small, large) = if a < b { (a, b) } else { (b, a) };

        let body = BlockBody {
            inputs: vec![large, small], // deliberately out of order
            outputs: vec![],
            ..Default::default()
        };
        assert!(!body.is_canonically_ordered());

        let header = mined_header(BlockHeader {
            prev_hash: [0u8; 32],
            state_root: [0u8; 32],
            output_count: 0,
            body_hash: body.body_hash(), // matches honestly, PoW is fine
            aux_hash: [0; 32],
            version: crate::block::BLOCK_VERSION,
            height: 0,
            timestamp: 0,
            nonce: [0u8; 32],
        });
        let block = Block { header, body };

        assert!(!block.validate_structure(&INITIAL_MAX_HASH, &crate::pow::Params::TEST));
    }

    #[test]
    fn body_from_bytes_rejects_truncated_input_record() {
        let a = commitment_of(&keypair(1).1, 10);
        let mut body = BlockBody::new();
        body.push_input(a);
        let mut bytes = body.to_bytes();
        bytes.truncate(bytes.len() - 1); // one byte short of a full record

        assert_eq!(BlockBody::from_bytes(&bytes).unwrap_err(), Error::Truncated);
    }

    #[test]
    fn body_from_bytes_rejects_trailing_garbage() {
        let body = BlockBody::new();
        let mut bytes = body.to_bytes();
        bytes.push(0xFF); // one byte more than the (empty) body needs

        assert_eq!(BlockBody::from_bytes(&bytes).unwrap_err(), Error::Truncated);
    }

    /// A body of `n` distinct, sorted output commitments.
    /// A body of `n` distinct, sorted, canonical output commitments: `i`
    /// big-endian in the first three bytes (sorting bytewise sorts by `i`),
    /// with the fourth zero so that group stays far below P.
    fn body_with_outputs(n: usize) -> BlockBody {
        let outputs = (0..n as u32)
            .map(|i| {
                let mut c = [0u8; 32];
                c[..3].copy_from_slice(&i.to_be_bytes()[1..]);
                c
            })
            .collect();
        BlockBody {
            nonces: vec![[0; NONCE_LEN]; n],
            outputs,
            ..Default::default()
        }
    }

    fn mined_block(body: BlockBody) -> Block {
        let header = mined_header(BlockHeader {
            prev_hash: [0u8; 32],
            state_root: [0u8; 32],
            output_count: 0,
            body_hash: body.body_hash(),
            aux_hash: [0; 32],
            version: crate::block::BLOCK_VERSION,
            height: 0,
            timestamp: 0,
            nonce: [0u8; 32],
        });
        Block { header, body }
    }

    /// Nonces round-trip with their outputs, count toward `body_hash`,
    /// and a body without exactly one per output is invalid.
    #[test]
    fn nonces_are_encoded_hashed_and_required() {
        let mut body = body_with_outputs(3);
        body.nonces = vec![[1; NONCE_LEN], [2; NONCE_LEN], [3; NONCE_LEN]];
        assert_eq!(BlockBody::from_bytes(&body.to_bytes()).unwrap(), body);
        let mut other = body.clone();
        other.nonces[1] = [4; NONCE_LEN];
        assert_ne!(other.body_hash(), body.body_hash(), "nonces are committed to");
        assert!(mined_block(body.clone()).validate_structure(&INITIAL_MAX_HASH, &crate::pow::Params::TEST));
        body.nonces.pop();
        assert!(!mined_block(body).validate_structure(&INITIAL_MAX_HASH, &crate::pow::Params::TEST));
    }

    /// Inputs and outputs can't trade places without changing the hash
    /// (the list lengths are hashed too).
    #[test]
    fn body_hash_separates_inputs_from_outputs() {
        let c = [5u8; 32];
        let as_input = BlockBody { inputs: vec![c], ..Default::default() };
        let as_output = BlockBody { outputs: vec![c], ..Default::default() };
        assert_ne!(as_input.body_hash(), as_output.body_hash());
    }

    #[test]
    fn encoded_len_matches_to_bytes() {
        for n in [0, 1, 7] {
            let block = mined_block(body_with_outputs(n));
            assert_eq!(block.encoded_len(), block.to_bytes().len());
        }
    }

    /// Exactly at `MAX_BLOCK_BYTES` is fine; one output more isn't.
    /// (Counts and proof length take 16 bytes; this proof is empty; each
    /// output is a commitment and a nonce.)
    #[test]
    fn validate_enforces_the_block_size_limit() {
        let fits = (MAX_BLOCK_BYTES - HEADER_LEN - 16) / (32 + NONCE_LEN);
        let at_limit = mined_block(body_with_outputs(fits));
        assert!(at_limit.encoded_len() <= MAX_BLOCK_BYTES);
        assert!(at_limit.validate_structure(&INITIAL_MAX_HASH, &crate::pow::Params::TEST));

        let over = mined_block(body_with_outputs(fits + 1));
        assert!(over.encoded_len() > MAX_BLOCK_BYTES);
        assert!(!over.validate_structure(&INITIAL_MAX_HASH, &crate::pow::Params::TEST));
    }

    /// A count that claims far more records than the bytes hold fails as
    /// `Truncated` -- without first trying to allocate room for them all.
    #[test]
    fn body_from_bytes_survives_a_huge_declared_count() {
        let mut bytes = u32::MAX.to_be_bytes().to_vec();
        bytes.extend_from_slice(&[0u8; 64]);
        assert_eq!(BlockBody::from_bytes(&bytes).unwrap_err(), Error::Truncated);
    }
}
