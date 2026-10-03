//! A block: a header committing to a flat, canonically-ordered body of
//! spent inputs and created outputs, plus (eventually) a proof. See
//! `docs/BLOCK.md` for the full design discussion; this module is its
//! implementation.
//!
//! **This module knows nothing about chain state.** `Block::validate`
//! checks only what's intrinsic to the block itself -- proof of work, and
//! that the header's `body_hash` actually matches the body -- with no
//! `Pmmr`, `Bitmap`, or `UtxoIndex` anywhere in sight. Resolving inputs
//! against real chain state, checking the block balances (which requires
//! knowing what each input is actually worth), catching double-spends,
//! and applying the resulting updates are all a different, separate
//! concern: `chain::validate_block` builds on top of this module to do
//! that. The split matters because those checks need mutable access to
//! on-disk state and this one deliberately never does.
//!
//! **`Transaction` is only ever used as an *ingestion* type here, never
//! stored.** `BlockBody::add_transaction` is the only way to put anything
//! into a body: it checks `tx.verify()` (a basic sanity filter at
//! assembly time -- did this transaction's own signatures check out),
//! then folds its inputs and outputs into the body's flat, sorted lists
//! and throws the `Transaction` -- signatures included -- away. Nothing
//! downstream re-checks any of that: once a body is built there are no
//! signatures left to check at all. Authorization is entirely the
//! (not-yet-built) proof's job; this ingestion-time check is a
//! convenience for whoever's assembling a block, not a security property
//! -- anyone could bypass it (there's no private way to enforce
//! otherwise), the actual guarantee is meant to come from the proof
//! later.
//!
//! There's no "coinbase transaction" to detect, either: a `Transaction`
//! with zero inputs verifies just fine (nothing in `transaction::verify`
//! checks balance at all anymore -- see that module's docs), so a miner
//! can build their reward-plus-fees claim as an ordinary `Transaction`
//! with no inputs and feed it through `add_transaction` like anything
//! else. `chain::validate_block`'s balance equation is what actually
//! constrains how much that's allowed to total.

#![allow(dead_code)]

use crate::output::{OUTPUT_LEN, Output};
use crate::poseidon2::hash_bytes_32;
use crate::pow;
use crate::transaction::Transaction;
use crate::wots::{PUBLIC_KEY_LEN, PublicKey};

/// Errors from decoding a `BlockBody`/`Block` from bytes. Encoding never
/// fails.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The buffer ended before a declared record count did, or had
    /// leftover bytes after the last record.
    Truncated,
    /// Inputs or outputs were not in the canonical sorted order
    /// `push_input`/`push_output` always produce (see the module docs).
    /// A raw byte buffer has no way to enforce that on its own, so
    /// decoding checks it explicitly -- this is what lets anything
    /// downstream (an eventual circuit, especially) rely on sortedness
    /// for cheap adjacent-pair checks instead of comparing every pair.
    NotCanonicallyOrdered,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Truncated => write!(f, "buffer ended before the declared record count did, or had trailing bytes"),
            Error::NotCanonicallyOrdered => write!(f, "inputs or outputs were not in canonical sorted order"),
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
    /// nonce on every mining attempt. Deliberately excludes the proof
    /// (not present on this type at all yet) -- see the module docs.
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

/// A canonically-ordered, flat payload: every spent input (just the
/// owner's public key -- no amount; see the module docs and
/// `transaction`'s) and every created output, across the whole block,
/// with no notion of which came from which off-chain transaction. See
/// `docs/BLOCK.md`.
#[derive(Clone, Debug, Default)]
pub struct BlockBody {
    pub inputs: Vec<PublicKey>,
    pub outputs: Vec<Output>,
}

impl BlockBody {
    pub fn new() -> Self {
        BlockBody {
            inputs: Vec::new(),
            outputs: Vec::new(),
        }
    }

    /// Fold `tx`'s inputs and outputs into this body, discarding its
    /// signatures entirely -- see the module docs for why that's fine.
    /// Returns `false` without modifying anything if `tx.verify()` fails
    /// (a sanity filter at assembly time, not a security property this
    /// module enforces -- see the module docs).
    pub fn add_transaction(&mut self, tx: &Transaction) -> bool {
        if !tx.verify() {
            return false;
        }
        for input in &tx.inputs {
            self.push_input(&input.pubkey);
        }
        for output in &tx.outputs {
            self.push_output(*output);
        }
        true
    }

    /// Insert `pubkey`, keeping `inputs` sorted ascending by its bytes --
    /// the same canonical-ordering convention `Transaction` already uses,
    /// for the same reason: two blocks assembled from the same
    /// transactions in a different order must still produce the same
    /// `body_hash`.
    fn push_input(&mut self, pubkey: &PublicKey) {
        let key_bytes = pubkey.to_bytes();
        let pos = self.inputs.partition_point(|pk| pk.to_bytes() < key_bytes);
        self.inputs.insert(pos, pubkey.clone());
    }

    /// Insert `output`, keeping `outputs` sorted ascending by its own
    /// encoded bytes -- same reasoning as `push_input`.
    fn push_output(&mut self, output: Output) {
        let bytes = output.to_bytes();
        let pos = self
            .outputs
            .partition_point(|existing| existing.to_bytes() < bytes);
        self.outputs.insert(pos, output);
    }

    /// Hash of the complete body: every input's public key in sorted
    /// order, then every output, also sorted. What the header's
    /// `body_hash` commits to.
    pub fn body_hash(&self) -> [u8; 32] {
        let mut bytes = Vec::new();
        for pubkey in &self.inputs {
            bytes.extend_from_slice(&pubkey.to_bytes());
        }
        for output in &self.outputs {
            bytes.extend_from_slice(&output.to_bytes());
        }
        hash_bytes_32(&bytes)
    }

    /// Total value created by this body's outputs. There is no
    /// corresponding `total_input_amount` here -- how much an input is
    /// actually worth isn't knowable without resolving it against real
    /// chain state; see `chain::validate_block`.
    pub fn total_output_amount(&self) -> u128 {
        self.outputs.iter().map(|o| o.amount as u128).sum()
    }

    /// Serialize: a 4-byte big-endian input count, that many fixed-width
    /// public keys, then a 4-byte big-endian output count, that many
    /// fixed-width outputs. Always produces canonically-ordered bytes,
    /// since `inputs`/`outputs` are only ever populated in that order in
    /// the first place (`push_input`/`push_output`).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&(self.inputs.len() as u32).to_be_bytes());
        for pubkey in &self.inputs {
            out.extend_from_slice(&pubkey.to_bytes());
        }
        out.extend_from_slice(&(self.outputs.len() as u32).to_be_bytes());
        for output in &self.outputs {
            out.extend_from_slice(&output.to_bytes());
        }
        out
    }

    /// Decode from bytes, the inverse of `to_bytes` -- but unlike it,
    /// this can fail: a truncated buffer, trailing garbage after the
    /// last record, or (critically) inputs or outputs that aren't in
    /// canonical sorted order are all rejected rather than silently
    /// accepted or silently re-sorted. See the module docs and `Error`.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        fn read_u32(bytes: &[u8], offset: &mut usize) -> Result<u32> {
            let slice = bytes.get(*offset..*offset + 4).ok_or(Error::Truncated)?;
            *offset += 4;
            Ok(u32::from_be_bytes(slice.try_into().unwrap()))
        }

        let mut offset = 0;

        let input_count = read_u32(bytes, &mut offset)?;
        let mut inputs = Vec::with_capacity(input_count as usize);
        let mut prev_key_bytes: Option<Vec<u8>> = None;
        for _ in 0..input_count {
            let slice = bytes
                .get(offset..offset + PUBLIC_KEY_LEN)
                .ok_or(Error::Truncated)?;
            offset += PUBLIC_KEY_LEN;
            let pubkey = PublicKey::from_bytes(slice).ok_or(Error::Truncated)?;
            let key_bytes = pubkey.to_bytes();
            if prev_key_bytes.is_some_and(|prev| key_bytes < prev) {
                return Err(Error::NotCanonicallyOrdered);
            }
            prev_key_bytes = Some(key_bytes);
            inputs.push(pubkey);
        }

        let output_count = read_u32(bytes, &mut offset)?;
        let mut outputs = Vec::with_capacity(output_count as usize);
        let mut prev_output_bytes: Option<[u8; OUTPUT_LEN]> = None;
        for _ in 0..output_count {
            let slice = bytes.get(offset..offset + OUTPUT_LEN).ok_or(Error::Truncated)?;
            offset += OUTPUT_LEN;
            let output_bytes: [u8; OUTPUT_LEN] = slice.try_into().unwrap();
            if prev_output_bytes.is_some_and(|prev| output_bytes < prev) {
                return Err(Error::NotCanonicallyOrdered);
            }
            prev_output_bytes = Some(output_bytes);
            outputs.push(Output::from_bytes(&output_bytes).ok_or(Error::Truncated)?);
        }

        if offset != bytes.len() {
            return Err(Error::Truncated); // trailing garbage
        }

        Ok(BlockBody { inputs, outputs })
    }
}

#[derive(Clone, Debug)]
pub struct Block {
    pub header: BlockHeader,
    pub body: BlockBody,
}

impl Block {
    /// Whether this block is sound *on its own*: proof of work checks
    /// out, and the header's `body_hash` actually matches the body. This
    /// is deliberately everything `Block` can check without touching any
    /// chain state -- see the module docs. Resolving inputs, checking
    /// balance, catching double-spends, and applying updates all live in
    /// `chain::validate_block` instead.
    pub fn validate(&self) -> bool {
        if !self.header.pow_valid() {
            return false;
        }
        if self.body.body_hash() != self.header.body_hash {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wots::{self, SecretKey};

    fn keypair(byte: u8) -> (SecretKey, PublicKey) {
        wots::keygen(&[byte; 32])
    }

    /// Mine a real nonce for `header` (with `nonce` still unset) against
    /// `FIXED_MAX_HASH`, panicking if none is found within a generous
    /// attempt budget -- 1-in-256 odds per attempt, so this finishes in a
    /// handful of tries almost always.
    fn mined_header(mut header: BlockHeader) -> BlockHeader {
        let preimage = header.pow_preimage();
        let (nonce, _) = pow::mine(&preimage, &FIXED_MAX_HASH, 100_000).expect("should find a nonce quickly");
        header.nonce = nonce;
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
        unsigned.add_input(&pk_a).unwrap();
        unsigned.add_output(Output::new(&pk_a, 100)).unwrap();
        // Never signed.

        let mut body = BlockBody::new();
        assert!(!body.add_transaction(&unsigned));
        assert!(body.inputs.is_empty());
        assert!(body.outputs.is_empty());
    }

    /// A verifying transaction's inputs and outputs get folded in, in
    /// canonical sorted order, regardless of the transaction's own
    /// internal order (which is already sorted the same way, but this
    /// confirms the body ends up with real, matching data, not just
    /// "some non-empty thing").
    #[test]
    fn add_transaction_folds_in_a_verifying_transaction() {
        let (sk_a, pk_a) = keypair(1);
        let (_, pk_out) = keypair(2);

        let mut tx = Transaction::new();
        tx.add_input(&pk_a).unwrap();
        tx.add_output(Output::new(&pk_out, 100)).unwrap();
        assert!(tx.sign_input(&pk_a, &sk_a));
        assert!(tx.verify());

        let mut body = BlockBody::new();
        assert!(body.add_transaction(&tx));
        assert_eq!(body.inputs, vec![pk_a]);
        assert_eq!(body.outputs, vec![Output::new(&pk_out, 100)]);
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
        assert_eq!(BlockBody::from_bytes(&body.to_bytes()).unwrap().inputs, body.inputs);
    }

    #[test]
    fn non_empty_body_round_trips_through_bytes() {
        let (sk_a, pk_a) = keypair(1);
        let (sk_b, pk_b) = keypair(2);
        let (_, pk_out_1) = keypair(3);
        let (_, pk_out_2) = keypair(4);

        let mut tx_a = Transaction::new();
        tx_a.add_input(&pk_a).unwrap();
        tx_a.add_output(Output::new(&pk_out_1, 100)).unwrap();
        assert!(tx_a.sign_input(&pk_a, &sk_a));

        let mut tx_b = Transaction::new();
        tx_b.add_input(&pk_b).unwrap();
        tx_b.add_output(Output::new(&pk_out_2, 200)).unwrap();
        assert!(tx_b.sign_input(&pk_b, &sk_b));

        let mut body = BlockBody::new();
        assert!(body.add_transaction(&tx_a));
        assert!(body.add_transaction(&tx_b));

        let decoded = BlockBody::from_bytes(&body.to_bytes()).unwrap();
        assert_eq!(decoded.inputs, body.inputs);
        assert_eq!(decoded.outputs, body.outputs);
        assert_eq!(decoded.body_hash(), body.body_hash());
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
        assert_eq!(decoded.body.inputs, block.body.inputs);
        assert_eq!(decoded.body.outputs, block.body.outputs);
        assert!(decoded.validate());
    }

    /// Two inputs encoded out of order (deliberately swapped from their
    /// canonical order) are rejected, not silently accepted or re-sorted.
    #[test]
    fn body_from_bytes_rejects_out_of_order_inputs() {
        let (_, pk_a) = keypair(1);
        let (_, pk_b) = keypair(2);

        let mut body = BlockBody::new();
        body.push_input(&pk_a);
        body.push_input(&pk_b);
        // body.inputs is now canonically sorted; swap it out of order.
        let mut bytes = body.to_bytes();
        let key_a = pk_a.to_bytes();
        let key_b = pk_b.to_bytes();
        let (first, second) = if key_a < key_b { (key_a, key_b) } else { (key_b, key_a) };
        // The two key records sit right after the 4-byte input count.
        bytes[4..4 + PUBLIC_KEY_LEN].copy_from_slice(&second);
        bytes[4 + PUBLIC_KEY_LEN..4 + 2 * PUBLIC_KEY_LEN].copy_from_slice(&first);

        assert_eq!(BlockBody::from_bytes(&bytes).unwrap_err(), Error::NotCanonicallyOrdered);
    }

    /// Two outputs encoded out of order are rejected the same way.
    #[test]
    fn body_from_bytes_rejects_out_of_order_outputs() {
        let (_, pk_a) = keypair(1);
        let (_, pk_b) = keypair(2);

        let mut body = BlockBody::new();
        body.push_output(Output::new(&pk_a, 10));
        body.push_output(Output::new(&pk_b, 20));
        let mut bytes = body.to_bytes();

        // Input section is empty (just a 4-byte zero count); the output
        // count (4 bytes) and the two output records follow.
        let out_start = 4 + 4;
        let out_a = bytes[out_start..out_start + OUTPUT_LEN].to_vec();
        let out_b = bytes[out_start + OUTPUT_LEN..out_start + 2 * OUTPUT_LEN].to_vec();
        bytes[out_start..out_start + OUTPUT_LEN].copy_from_slice(&out_b);
        bytes[out_start + OUTPUT_LEN..out_start + 2 * OUTPUT_LEN].copy_from_slice(&out_a);

        assert_eq!(BlockBody::from_bytes(&bytes).unwrap_err(), Error::NotCanonicallyOrdered);
    }

    /// Duplicate adjacent inputs (same public key twice, in order) are
    /// accepted -- `BlockBody` allows duplicates (double-spend detection
    /// is `chain::validate_block`'s job, not a decoding concern); only
    /// out-of-order data is rejected here.
    #[test]
    fn body_from_bytes_accepts_duplicate_adjacent_inputs() {
        let (_, pk_a) = keypair(1);
        let mut body = BlockBody::new();
        body.push_input(&pk_a);
        body.push_input(&pk_a);

        let decoded = BlockBody::from_bytes(&body.to_bytes()).unwrap();
        assert_eq!(decoded.inputs, vec![pk_a.clone(), pk_a]);
    }

    #[test]
    fn body_from_bytes_rejects_truncated_input_record() {
        let (_, pk_a) = keypair(1);
        let mut body = BlockBody::new();
        body.push_input(&pk_a);
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
