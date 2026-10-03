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
//! `pmmr`'s leaves, this body, and the `utxo` index all the same kind of
//! opaque value everywhere -- there's no plaintext form of this data
//! anywhere on-chain to leak, by construction, not by discipline.
//!
//! **This module knows nothing about chain state.** `Block::validate`
//! checks only what's intrinsic to the block itself -- proof of work, and
//! that the header's `body_hash` actually matches the body -- with no
//! `Pmmr`, `Bitmap`, or `UtxoIndex` anywhere in sight. Resolving spends
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

use crate::output::Output;
use crate::poseidon2::hash_bytes_32;
use crate::pow;
use crate::prover::Proof;
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

/// The fixed proof-of-work target: first byte zero, the rest maxed out, so
/// a candidate hash meets it iff its own first byte is exactly zero --
/// true for a uniformly random hash with probability 1/256. No difficulty
/// retargeting yet (that needs block height/timestamps first), so this is
/// one constant every block is mined against.
pub const FIXED_MAX_HASH: [u8; 32] = {
    let mut b = [0xffu8; 32];
    b[0] = 0x00;
    b
};

/// `prev_hash`, `pmmr_root`, `bitmap_root`, `body_hash` (32 bytes each),
/// then `nonce` (32 bytes) -- `BlockHeader`'s fixed encoded width.
pub const HEADER_LEN: usize = 32 * 5;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockHeader {
    pub prev_hash: [u8; 32],
    pub pmmr_root: [u8; 32],
    pub bitmap_root: [u8; 32],
    pub body_hash: [u8; 32],
    pub nonce: pow::Nonce,
}

impl BlockHeader {
    /// Serialize to exactly `HEADER_LEN` bytes: the five fields,
    /// concatenated in field-declaration order.
    pub fn to_bytes(&self) -> [u8; HEADER_LEN] {
        let mut out = [0u8; HEADER_LEN];
        out[0..32].copy_from_slice(&self.prev_hash);
        out[32..64].copy_from_slice(&self.pmmr_root);
        out[64..96].copy_from_slice(&self.bitmap_root);
        out[96..128].copy_from_slice(&self.body_hash);
        out[128..160].copy_from_slice(&self.nonce);
        out
    }

    /// Decode from bytes, the inverse of `to_bytes`. Every field is a
    /// plain 32-byte array, so the only way this can fail is `bytes` not
    /// being exactly `HEADER_LEN` long -- checked explicitly here
    /// (rather than taking a `[u8; HEADER_LEN]` and pushing that check
    /// onto every caller) so decoding a buffer of untrusted or
    /// attacker-controlled length can never panic, only return
    /// `Err(Error::Truncated)`.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != HEADER_LEN {
            return Err(Error::Truncated);
        }
        Ok(BlockHeader {
            prev_hash: bytes[0..32].try_into().unwrap(),
            pmmr_root: bytes[32..64].try_into().unwrap(),
            bitmap_root: bytes[64..96].try_into().unwrap(),
            body_hash: bytes[96..128].try_into().unwrap(),
            nonce: bytes[128..160].try_into().unwrap(),
        })
    }

    /// Everything the header commits to except the nonce -- what
    /// `pow::verify`/`pow::mine` actually hash, re-hashed with a new
    /// nonce on every mining attempt. Doesn't need to separately
    /// mention the proof: `body_hash` already commits to it (see
    /// `BlockBody`'s docs), so PoW covers it transitively.
    pub(crate) fn pow_preimage(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(32 * 4);
        bytes.extend_from_slice(&self.prev_hash);
        bytes.extend_from_slice(&self.pmmr_root);
        bytes.extend_from_slice(&self.bitmap_root);
        bytes.extend_from_slice(&self.body_hash);
        bytes
    }

    /// This header's own hash -- what a following block's `prev_hash`
    /// would point to. The same hash already computed while mining it.
    pub fn hash(&self) -> [u8; 32] {
        pow::pow_hash(&self.pow_preimage(), self.nonce)
    }

    pub fn pow_valid(&self) -> bool {
        pow::verify(&self.pow_preimage(), self.nonce, &FIXED_MAX_HASH)
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
    pub proof: Proof,
}

impl BlockBody {
    pub fn new() -> Self {
        BlockBody {
            inputs: Vec::new(),
            outputs: Vec::new(),
            proof: Proof,
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
            let commitment = hash_bytes_32(&Output::new(&input.pubkey, input.amount).to_bytes());
            self.push_input(commitment);
        }
        for output in &tx.outputs {
            self.push_output(hash_bytes_32(&output.to_bytes()));
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
    /// reasoning as `push_input`.
    fn push_output(&mut self, commitment: [u8; 32]) {
        insert_sorted(&mut self.outputs, commitment);
    }

    /// Hash of the complete body: every input commitment in sorted
    /// order, then every output commitment, also sorted, then the
    /// proof's own commitment -- one hash covering everything below the
    /// header, proof included (see the struct docs). What the header's
    /// `body_hash` commits to.
    pub fn body_hash(&self) -> [u8; 32] {
        let mut bytes = Vec::with_capacity((self.inputs.len() + self.outputs.len()) * 32 + 32);
        for commitment in &self.inputs {
            bytes.extend_from_slice(commitment);
        }
        for commitment in &self.outputs {
            bytes.extend_from_slice(commitment);
        }
        bytes.extend_from_slice(&self.proof.commitment_hash());
        hash_bytes_32(&bytes)
    }

    /// Whether `proof` actually attests to this body's `inputs`/
    /// `outputs` -- see `prover`'s docs for why this is a stub (always
    /// `true`) for now.
    pub fn proof_is_valid(&self) -> bool {
        self.proof.verify(&self.inputs, &self.outputs)
    }

    /// Serialize: a 4-byte big-endian input count, that many 32-byte
    /// commitments, then a 4-byte big-endian output count, that many
    /// 32-byte commitments. Always produces canonically-ordered bytes,
    /// since `inputs`/`outputs` are only ever populated in that order in
    /// the first place (`push_input`/`push_output`).
    ///
    /// **`proof` is not yet part of this wire format.** The stub type
    /// (see `prover`'s docs) has exactly one possible value, so there's
    /// nothing to lose by omitting it -- `from_bytes` just fills in that
    /// one value. This is a deliberate, temporary gap: once `Proof` has
    /// a real byte representation, encoding/decoding it becomes part of
    /// this format too.
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

        fn read_commitments(bytes: &[u8], offset: &mut usize, count: u32) -> Result<Vec<[u8; 32]>> {
            let mut out = Vec::with_capacity(count as usize);
            for _ in 0..count {
                let slice = bytes.get(*offset..*offset + 32).ok_or(Error::Truncated)?;
                *offset += 32;
                out.push(slice.try_into().unwrap());
            }
            Ok(out)
        }

        let mut offset = 0;
        let input_count = read_u32(bytes, &mut offset)?;
        let inputs = read_commitments(bytes, &mut offset, input_count)?;
        let output_count = read_u32(bytes, &mut offset)?;
        let outputs = read_commitments(bytes, &mut offset, output_count)?;

        if offset != bytes.len() {
            return Err(Error::Truncated); // trailing garbage
        }

        Ok(BlockBody {
            inputs,
            outputs,
            proof: Proof,
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
/// state-dependent field resolved (`prev_hash`, `pmmr_root`,
/// `bitmap_root`, and the flat `inputs`/`outputs` lists), but no proof
/// yet, and so no `Block` yet either -- `BlockBody`/`Block` both require
/// a real `proof` (see `BlockBody`'s docs), and this type deliberately
/// doesn't carry one. `finish` is the only way to turn this into an
/// actual `Block`, and it needs a `Proof` to do it (from
/// `prover::prove_block`) -- which is what keeps `pow::mine_block` from
/// being callable on anything until proving has actually happened.
#[derive(Debug)]
pub struct UnprovenBlock {
    pub prev_hash: [u8; 32],
    pub pmmr_root: [u8; 32],
    pub bitmap_root: [u8; 32],
    pub inputs: Vec<[u8; 32]>,
    pub outputs: Vec<[u8; 32]>,
}

impl UnprovenBlock {
    /// Attach `proof` to assemble the real, still-unmined `Block`:
    /// `body_hash` is computed only now, since it commits to the proof
    /// alongside `inputs`/`outputs` (see `BlockBody::body_hash`).
    /// `nonce` is left at `[0; 32]` -- `pow::mine_block` is the only
    /// thing that sets it, and only once this has already happened.
    pub fn finish(self, proof: Proof) -> Block {
        let body = BlockBody {
            inputs: self.inputs,
            outputs: self.outputs,
            proof,
        };
        let header = BlockHeader {
            prev_hash: self.prev_hash,
            pmmr_root: self.pmmr_root,
            bitmap_root: self.bitmap_root,
            body_hash: body.body_hash(),
            nonce: [0u8; 32],
        };
        Block { header, body }
    }
}

#[derive(Clone, Debug)]
pub struct Block {
    pub header: BlockHeader,
    pub body: BlockBody,
}

impl Block {
    /// Whether this block is sound *on its own*: proof of work checks
    /// out, the body is canonically ordered (sorted, no duplicates) and
    /// doesn't spend any output it also creates, the header's
    /// `body_hash` actually matches the body (proof included -- see
    /// `BlockBody`'s docs), and the proof itself checks out against the
    /// body's commitments. This is deliberately everything `Block` can
    /// check without touching any chain state -- see the module docs.
    /// Resolving spends against real chain state, catching reuse across
    /// different blocks, and applying updates all live in
    /// `chain::Chain::apply_block` instead -- but duplicate-commitment,
    /// same-block-spend, and proof validity don't need any of that,
    /// since they're properties of the body (and the proof within it)
    /// alone.
    ///
    /// These checks matter here, specifically, rather than at decode
    /// time: `BlockBody::from_bytes` only checks that bytes are
    /// well-formed, not that they're canonical, and `inputs`/`outputs`
    /// are public fields a `BlockBody` could in principle be built
    /// through some other way entirely. Checking it here means
    /// `validate` is a complete, self-contained answer to "is this
    /// block acceptable" regardless of how the value in hand was
    /// constructed, rather than a check that's only honest if you also
    /// know it arrived via `from_bytes`.
    pub fn validate(&self) -> bool {
        if !self.header.pow_valid() {
            return false;
        }
        if !self.body.is_canonically_ordered() {
            return false;
        }
        if self.body.spends_its_own_output() {
            return false;
        }
        if self.body.body_hash() != self.header.body_hash {
            return false;
        }
        if !self.body.proof_is_valid() {
            return false;
        }
        true
    }

    /// Serialize: the header's fixed-width encoding, followed by the
    /// body's.
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

/// Mine `header` in place: search for a nonce satisfying `FIXED_MAX_HASH`,
/// up to `max_attempts`, setting `header.nonce` and returning `true` on
/// success. Leaves `header` untouched and returns `false` if none of the
/// first `max_attempts` nonces satisfy it. Lives here, rather than in
/// `pow` itself, since `pow` is deliberately kept free of any dependency
/// on `block` (see that module's docs) -- this is just a thin,
/// `BlockHeader`-aware wrapper around `pow::mine`.
pub fn mine_header(header: &mut BlockHeader, max_attempts: u64) -> bool {
    let preimage = header.pow_preimage();
    match pow::mine(&preimage, &FIXED_MAX_HASH, max_attempts) {
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
pub fn mine_block(block: &mut Block, max_attempts: u64) -> bool {
    mine_header(&mut block.header, max_attempts)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wots::{self, PublicKey, SecretKey};

    fn keypair(byte: u8) -> (SecretKey, PublicKey) {
        wots::keygen(&[byte; 32])
    }

    /// The commitment a real output/input for `(pubkey, amount)` would
    /// publish -- computed independently of `add_transaction`, so tests
    /// asserting against it are actually checking something.
    fn commitment_of(pubkey: &PublicKey, amount: u64) -> [u8; 32] {
        hash_bytes_32(&Output::new(pubkey, amount).to_bytes())
    }

    /// Mine a real nonce for `header` (with `nonce` still unset) against
    /// `FIXED_MAX_HASH`, panicking if none is found within a generous
    /// attempt budget -- 1-in-256 odds per attempt, so this finishes in a
    /// handful of tries almost always.
    fn mined_header(mut header: BlockHeader) -> BlockHeader {
        assert!(mine_header(&mut header, 100_000), "should find a nonce quickly");
        header
    }

    /// A nonce guaranteed *not* to satisfy `FIXED_MAX_HASH` for the given
    /// header preimage -- used to test PoW rejection without any chance
    /// of test flakiness from accidentally picking a valid one.
    fn a_failing_nonce(preimage: &[u8]) -> pow::Nonce {
        for counter in 0u64..64 {
            let mut nonce = [0u8; 32];
            nonce[..8].copy_from_slice(&counter.to_le_bytes());
            if !pow::meets_target(&pow::pow_hash(preimage, nonce), &FIXED_MAX_HASH) {
                return nonce;
            }
        }
        unreachable!("extraordinarily unlikely: 64 consecutive nonces all satisfied a 1/256 target")
    }

    #[test]
    fn empty_block_with_correct_pow_and_body_hash_validates() {
        let header = mined_header(BlockHeader {
            prev_hash: [1u8; 32],
            pmmr_root: [2u8; 32],
            bitmap_root: [3u8; 32],
            body_hash: BlockBody::new().body_hash(),
            nonce: [0u8; 32],
        });
        let block = Block {
            header,
            body: BlockBody::new(),
        };

        assert!(block.validate());
    }

    /// PoW is checked first -- an arbitrary (wrong) `body_hash` is fine
    /// here, since validation never gets far enough to look at it.
    #[test]
    fn wrong_pow_is_rejected() {
        let header = BlockHeader {
            prev_hash: [1u8; 32],
            pmmr_root: [2u8; 32],
            bitmap_root: [3u8; 32],
            body_hash: [4u8; 32],
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

        assert!(!block.validate());
    }

    /// A header whose `body_hash` doesn't match the actual body is
    /// rejected, even with otherwise-valid PoW (mined for this exact,
    /// wrong preimage -- PoW doesn't know or care whether `body_hash` is
    /// honest).
    #[test]
    fn wrong_body_hash_is_rejected() {
        let header = mined_header(BlockHeader {
            prev_hash: [1u8; 32],
            pmmr_root: [2u8; 32],
            bitmap_root: [3u8; 32],
            body_hash: [0xABu8; 32], // does not match BlockBody::new()'s hash
            nonce: [0u8; 32],
        });
        let block = Block {
            header,
            body: BlockBody::new(),
        };

        assert!(!block.validate());
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
            pmmr_root: [2u8; 32],
            bitmap_root: [3u8; 32],
            body_hash: [4u8; 32],
            nonce: [0u8; 32],
        });
        assert_eq!(BlockHeader::from_bytes(&header.to_bytes()).unwrap(), header);
    }

    #[test]
    fn header_from_bytes_rejects_wrong_length() {
        let header = mined_header(BlockHeader {
            prev_hash: [1u8; 32],
            pmmr_root: [2u8; 32],
            bitmap_root: [3u8; 32],
            body_hash: [4u8; 32],
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
            pmmr_root: [8u8; 32],
            bitmap_root: [7u8; 32],
            body_hash: body.body_hash(),
            nonce: [0u8; 32],
        });
        let block = Block { header, body };

        let decoded = Block::from_bytes(&block.to_bytes()).unwrap();
        assert_eq!(decoded.header, block.header);
        assert_eq!(decoded.body, block.body);
        assert!(decoded.validate());
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
            pmmr_root: [0u8; 32],
            bitmap_root: [0u8; 32],
            body_hash: body.body_hash(),
            nonce: [0u8; 32],
        });
        let block = Block { header, body };

        assert!(!block.validate());
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
            pmmr_root: [0u8; 32],
            bitmap_root: [0u8; 32],
            body_hash: body.body_hash(), // matches honestly, PoW is fine
            nonce: [0u8; 32],
        });
        let block = Block { header, body };

        assert!(!block.validate());
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
}
