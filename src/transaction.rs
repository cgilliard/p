//! Transactions: just inputs (spent outputs, identified by their owner's
//! public key and the amount being spent) and outputs, nothing else -- no
//! scripts.
//!
//! This module has **no notion of the state tree, a block, or where in the chain an
//! output actually lives** -- deliberately so. `Transaction` is a small,
//! self-contained, reusable primitive: building, signing, and checking a
//! transaction's own internal correctness never needs to know anything
//! about how outputs are actually indexed, so this same type can be used
//! wherever a transaction needs handling -- a mempool, a wallet, a test,
//! block assembly -- without dragging any of those contexts' specifics in.
//! `transaction::Input` is a *private, off-chain* record a wallet and a
//! prover both need (the real public key and the real amount, so a
//! signature can be checked and a spend commitment can eventually be
//! computed); `block::BlockBody`'s notion of an input is a completely
//! different, much narrower type -- just the 32-byte commitment hash,
//! nothing else -- since that's all that's ever actually published. This
//! module never computes that hash itself; see `block::BlockBody::
//! add_transaction`, which is the only place `transaction::Input`'s
//! (pubkey, amount) pair ever gets turned into one.
//!
//! `amount` being back on `Input` is **not** for balance-checking -- this
//! module still doesn't do any (see below), and still has no way to
//! confirm a claimed input is real. It's here for two narrower reasons:
//! so the signature actually pins down *which* output is being
//! authorized (without it, two different real outputs owned by the same
//! key -- if that ever happened -- would be indistinguishable to a
//! signature that only covered the key), and so whoever folds this
//! transaction into a block has what it needs to compute that output's
//! commitment without a separate side channel.
//!
//! Both inputs and outputs are kept sorted automatically -- inputs
//! ascending by public key, outputs ascending by their own encoded bytes
//! -- by inserting each new one into its sorted position (an insertion
//! sort; `partition_point` finds where, `Vec::insert` shifts the rest
//! over) rather than just appending. That gives a transaction a single
//! canonical representation no matter what order, or which interleaving
//! of inputs and outputs, it was actually built in (see below), and it's
//! also what turns detecting a duplicate input (the same output claimed
//! twice) into a cheap adjacent-pair scan in `verify`, instead of
//! comparing every pair.
//!
//! Because inputs are addressed by public key rather than by position in
//! some list, that automatic re-sorting never invalidates anything a
//! caller is holding onto -- there's no index to go stale.
//!
//! # What a signature actually commits to
//!
//! Every signer signs the *same* message (`signing_message`): a hash over
//! the complete, current transaction -- every input's (pubkey, amount), in
//! canonical sorted order, followed by every output, also sorted. This is
//! the strong commitment, not a "just my own input" one: once anyone has
//! signed, changing the input set *or* the output set in any way --
//! adding, removing, or altering either -- invalidates *every* existing
//! signature, not just whichever part changed. That's intentional: it's
//! what makes "this transaction" a single, well-defined thing, rather
//! than a fixed output list that happens to be satisfiable by many
//! different, interchangeable combinations of inputs.
//!
//! (Real Mimblewimble gets this same whole-transaction binding by having
//! every participant contribute a partial Schnorr signature over one
//! shared aggregate challenge. WOTS can't be aggregated that way -- it's a
//! one-time hash-chain scheme, not a linear one -- so instead, every
//! signer here independently produces their own separate WOTS signature,
//! but all of them sign that identical shared message. Same end result,
//! the whole transaction gets pinned down, reached without needing an
//! interactive aggregation protocol.)
//!
//! # Building a transaction, with multiple independent parties
//!
//! Inputs *and* outputs can both be added by any number of independent
//! parties, in any interleaved order -- a recipient can add their output,
//! a sender can add an input, another recipient can add another output,
//! and so on, in whatever order is convenient, with no round-trip needed
//! to agree on ordering up front (the automatic sorting above is what
//! makes that safe). The one rule: **no one signs until every input and
//! output that belongs in the transaction has been added.** This is
//! enforced, not just documented: the moment the first signature is
//! collected, the transaction is finalized (`is_finalized`), and every
//! later `add_input`/`add_output` call returns `Err(Error::Finalized)`
//! instead of silently mutating `signing_message()` and invalidating
//! whatever's already been collected. It's still up to whoever's
//! coordinating to make sure every input and output is in place *before*
//! anyone signs -- `sign_input` has no way to know the transaction isn't
//! finished yet -- but a mistake there now fails loudly, on the next add
//! attempt, rather than silently, as an unexplained verification failure
//! much later.
//!
//! ```ignore
//! let mut tx = Transaction::new();
//! tx.add_output(output_for_bob).unwrap();
//! tx.add_input(&pubkey_a, 100).unwrap();
//! tx.add_output(output_for_carol).unwrap(); // adding more outputs and
//! tx.add_input(&pubkey_b, 50).unwrap();     // inputs, freely interleaved,
//!                                           // is fine -- until anyone signs.
//!
//! tx.sign_input(&pubkey_a, &secret_a);
//! tx.sign_input(&pubkey_b, &secret_b);
//! assert!(tx.verify());
//! ```
//!
//! One thing this module checks that's internal to the transaction, and
//! two things it deliberately leaves to the caller:
//!
//! - Checked here: every input is signed over the complete transaction,
//!   and no two inputs claim the same public key.
//! - Left to the caller: whether each claimed (pubkey, amount) input
//!   actually, currently corresponds to a real, unspent output somewhere,
//!   whether the whole thing balances, and whether the same output gets
//!   spent by more than one transaction (double-spending). All three are
//!   questions about a specific output set at a specific moment, or about
//!   a proof attesting to one, not about the transaction by itself -- a
//!   `Transaction` can be fully internally valid while every one of its
//!   claimed inputs turns out to be fabricated, already spent, or adding
//!   up to something that doesn't balance at all, and catching any of
//!   that is explicitly not this module's job.

// `main.rs` doesn't call into this module yet (it just prints "Hello
// world!"), so allow dead code here rather than suppressing warnings
// piecemeal -- this module exists to be exercised by its tests for now.
#![allow(dead_code)]

use crate::output::Output;
use crate::keytree::KeyProof;
use crate::policy::Branch;
use crate::poseidon2::{BabyBear, DOMAIN_REBIND, DOMAIN_SIGNING, digest_from_bytes, digest_to_bytes, hash_elements};
use crate::wots::{self, PublicKey, SecretKey, Signature};


/// Returned by `add_input`/`add_output` when the transaction has already
/// collected a signature.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// At least one input is already signed, so the input/output set is
    /// locked (see the module docs) -- adding more at this point would
    /// silently change `signing_message()` and invalidate every signature
    /// already collected.
    Finalized,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Finalized => write!(
                f,
                "transaction already has a signature; no more inputs or outputs can be added"
            ),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

/// One spent output: the amount being spent and what unlocks it, with
/// the signatures over the whole transaction's signing message once
/// they've been provided. See the module docs for why `amount` is here
/// even though this module still doesn't check balance.
#[derive(Clone, Debug)]
pub struct Input {
    pub amount: u64,
    pub spend: Spend,
}

/// What unlocks a spent output.
#[derive(Clone, Debug)]
pub enum Spend {
    /// An output locked to one key: the signing (leaf) key, its place in
    /// its key tree (`keytree`; empty for a one-time key), and its
    /// signature.
    Key { pubkey: PublicKey, proof: KeyProof, signature: Option<Signature> },
    /// An output locked to a spending policy (`policy`): one branch of it,
    /// and what satisfies it.
    Policy(PolicySpend),
}

/// A spend of a policy output by one branch.
#[derive(Clone, Debug)]
pub struct PolicySpend {
    pub branch: Branch,
    /// The branch's position in its policy's tree, and its path to the
    /// root (siblings, bottom first).
    pub index: u32,
    pub path: Vec<[u8; 32]>,
    /// The hash lock's preimage, if the branch has one.
    pub preimage: Option<[u8; 32]>,
    /// For a REBIND branch: the state declared (above the branch's), and
    /// the outputs its signatures name, by commitment, in increasing order
    /// (`rebind_message`). Zero and none otherwise.
    pub state: u32,
    pub named: Vec<[u8; 32]>,
    /// Who has signed, by key index, in increasing order.
    pub signers: Vec<Signer>,
}

/// What a REBIND signature signs: the declared `state`, and the outputs it
/// names (commitment and nonce, in increasing order of commitment) -- not
/// the input it spends, nor any other input or output (`docs/CONTRACTS.md`,
/// step 4). A sponge over `[m, state, 0 …]` and one block per output.
pub fn rebind_message(state: u32, named: &[([u8; 32], [u8; crate::recovery::NONCE_LEN])]) -> [BabyBear; 8] {
    let mut elements = vec![BabyBear::ZERO; 16];
    elements[0] = BabyBear::new(named.len() as u32);
    elements[1] = BabyBear::new(state);
    for (commitment, nonce) in named {
        elements.extend(digest_from_bytes(commitment));
        elements.extend(crate::output::nonce_limbs(nonce));
    }
    hash_elements(DOMAIN_REBIND, &elements)
}

/// One of a policy branch's keys: the signing (leaf) key, its place in
/// its key tree, and its signature.
#[derive(Clone, Debug)]
pub struct Signer {
    pub index: u8,
    pub pubkey: PublicKey,
    pub proof: KeyProof,
    pub signature: Option<Signature>,
}

impl Input {
    /// The lock of the output this spends: the key's hash, or the policy's
    /// root (the branch's leaf, up its path).
    pub fn lock(&self) -> [u8; 32] {
        match &self.spend {
            Spend::Key { pubkey, proof, .. } => proof.key_id(pubkey),
            Spend::Policy(p) => {
                let path: Vec<_> = p.path.iter().map(digest_from_bytes).collect();
                digest_to_bytes(crate::policy::root_from(p.branch.leaf(), p.index, &path))
            }
        }
    }

    /// The commitment of the output this spends.
    pub fn commitment(&self) -> [u8; 32] {
        Output::locked(self.lock(), self.amount).commitment()
    }

    /// The key, if this spends a single-key output.
    pub fn key(&self) -> Option<&PublicKey> {
        match &self.spend {
            Spend::Key { pubkey, .. } => Some(pubkey),
            Spend::Policy(_) => None,
        }
    }

    /// The signatures it carries: `(key, signature)` for each signer that
    /// has signed.
    pub fn signatures(&self) -> Vec<(&PublicKey, &Signature)> {
        match &self.spend {
            Spend::Key { pubkey, signature, .. } => signature.iter().map(|s| (pubkey, s)).collect(),
            Spend::Policy(p) => p.signers.iter().filter_map(|s| s.signature.as_ref().map(|sig| (&s.pubkey, sig))).collect(),
        }
    }

    /// Whether it signs REBIND (spends a REBIND branch).
    pub fn rebinds(&self) -> bool {
        matches!(&self.spend, Spend::Policy(p) if p.branch.rebind.is_some())
    }

    /// Whether it's fully authorized, its signatures over `message` (the
    /// transaction's, or its REBIND message): the key's signature, or a
    /// valid branch whose path, signers, preimage and declared state
    /// satisfy it. (Not its timelocks: those depend on the block,
    /// `locks_hold`.)
    fn authorized(&self, message: [BabyBear; 8]) -> bool {
        match &self.spend {
            Spend::Key { pubkey, proof, signature } => proof.is_valid() && signature.as_ref().is_some_and(|sig| wots::verify(pubkey, message, sig)),
            Spend::Policy(p) => {
                let b = &p.branch;
                let signers_ok = p.signers.len() == b.threshold as usize
                    && p.signers.windows(2).all(|w| w[0].index < w[1].index)
                    && p.signers.iter().all(|s| {
                        s.proof.is_valid()
                            && b.keys.get(s.index as usize) == Some(&s.proof.key_id(&s.pubkey))
                            && s.signature.as_ref().is_some_and(|sig| wots::verify(&s.pubkey, message, sig))
                    });
                let hash_ok = match (&b.hashlock, &p.preimage) {
                    (Some(x), Some(preimage)) => crate::policy::hashlock(preimage).as_ref() == Some(x),
                    (None, None) => true,
                    _ => false,
                };
                let state_ok = match b.rebind {
                    Some(s) => p.state > s && p.state < crate::policy::MAX_LOCK && !p.named.is_empty() && p.named.windows(2).all(|w| w[0] < w[1]),
                    None => p.state == 0 && p.named.is_empty(),
                };
                b.is_valid()
                    && state_ok
                    && p.path.len() <= crate::policy::MAX_DEPTH
                    && (p.index as u64) < 1u64 << p.path.len()
                    && p.path.iter().all(crate::prover::is_canonical)
                    && signers_ok
                    && hash_ok
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Transaction {
    pub inputs: Vec<Input>,
    pub outputs: Vec<Output>,
    finalized: bool,
}

impl Transaction {
    pub fn new() -> Self {
        Transaction {
            inputs: Vec::new(),
            outputs: Vec::new(),
            finalized: false,
        }
    }

    /// Whether this transaction has collected at least one signature, and
    /// so is locked against further `add_input`/`add_output` calls.
    pub fn is_finalized(&self) -> bool {
        self.finalized
    }

    /// Insert `input` at its sorted position (by commitment, see the module
    /// docs), unless the transaction is finalized.
    fn insert_input(&mut self, input: Input) -> Result<()> {
        if self.finalized {
            return Err(Error::Finalized);
        }
        let commitment = input.commitment();
        let pos = self.inputs.partition_point(|existing| existing.commitment() < commitment);
        self.inputs.insert(pos, input);
        Ok(())
    }

    /// Add an input spending `amount` from the output owned by `pubkey`,
    /// inserting it into its sorted position among the existing inputs
    /// (see the module docs) rather than just appending. Returns
    /// `Err(Error::Finalized)` without adding anything if the transaction
    /// has already collected a signature.
    pub fn add_input(&mut self, pubkey: &PublicKey, amount: u64) -> Result<()> {
        self.add_tree_input(pubkey, KeyProof::one_time(), amount)
    }

    /// `add_input` for an output locked to a multi-use key (`keytree`):
    /// `pubkey` the leaf key that will sign, at `proof` in its tree.
    pub fn add_tree_input(&mut self, pubkey: &PublicKey, proof: KeyProof, amount: u64) -> Result<()> {
        self.insert_input(Input {
            amount,
            spend: Spend::Key { pubkey: pubkey.clone(), proof, signature: None },
        })
    }

    /// Add an input spending `amount` from a policy output by `branch`, at
    /// `index` in its policy (`path` its siblings), revealing `preimage`
    /// for a hash lock. Its signers sign later (`sign_policy_input`).
    pub fn add_policy_input(&mut self, branch: Branch, index: u32, path: Vec<[u8; 32]>, preimage: Option<[u8; 32]>, amount: u64) -> Result<()> {
        self.add_rebind_input(branch, index, path, preimage, amount, 0, Vec::new())
    }

    /// `add_policy_input` for a REBIND branch: declaring `state`, its
    /// signatures naming the outputs `named` (by commitment).
    #[allow(clippy::too_many_arguments)]
    pub fn add_rebind_input(&mut self, branch: Branch, index: u32, path: Vec<[u8; 32]>, preimage: Option<[u8; 32]>, amount: u64, state: u32, mut named: Vec<[u8; 32]>) -> Result<()> {
        named.sort_unstable();
        self.insert_input(Input {
            amount,
            spend: Spend::Policy(PolicySpend { branch, index, path, preimage, state, named, signers: Vec::new() }),
        })
    }

    /// Point the REBIND input spending `commitment` at another output --
    /// `amount` locked to the policy whose branch `branch` sits at `index`
    /// by `path` -- keeping its signatures, which don't cover what it
    /// spends: how an eltoo update replaces whichever earlier update was
    /// published. `false` if there's no such REBIND input, or the
    /// transaction is finalized (an ordinary signature -- a fee input's,
    /// say -- covers what each input spends: re-point first, then add the
    /// fee).
    pub fn rebind(&mut self, commitment: &[u8; 32], branch: Branch, index: u32, path: Vec<[u8; 32]>, amount: u64) -> bool {
        if self.finalized {
            return false;
        }
        let Some(pos) = self.inputs.iter().position(|i| i.rebinds() && &i.commitment() == commitment) else {
            return false;
        };
        let mut input = self.inputs.remove(pos);
        let Spend::Policy(p) = &mut input.spend else { unreachable!() };
        (p.branch, p.index, p.path) = (branch, index, path);
        input.amount = amount;
        let commitment = input.commitment();
        let pos = self.inputs.partition_point(|existing| existing.commitment() < commitment);
        self.inputs.insert(pos, input);
        true
    }

    /// The message `input`'s signatures sign: its REBIND message (`None`
    /// if an output it names isn't here), or the transaction's.
    pub fn message_for(&self, input: &Input) -> Option<[BabyBear; 8]> {
        match &input.spend {
            Spend::Policy(p) if p.branch.rebind.is_some() => {
                let named = p
                    .named
                    .iter()
                    .map(|c| self.outputs.iter().find(|o| &o.commitment() == c).map(|o| (*c, o.nonce)))
                    .collect::<Option<Vec<_>>>()?;
                Some(rebind_message(p.state, &named))
            }
            _ => Some(self.signing_message()),
        }
    }

    /// Add `output`, inserting it into its sorted position among the
    /// existing outputs (same reasoning as `add_input`: this is what lets
    /// multiple independent parties add outputs in any order and still
    /// end up with an identical, canonical transaction). Returns
    /// `Err(Error::Finalized)` without adding anything if the transaction
    /// has already collected a signature.
    pub fn add_output(&mut self, output: Output) -> Result<()> {
        if self.finalized {
            return Err(Error::Finalized);
        }
        let bytes = output.to_bytes();
        let pos = self
            .outputs
            .partition_point(|existing| existing.to_bytes() < bytes);
        self.outputs.insert(pos, output);
        Ok(())
    }

    /// The single message every signer signs: a hash over the complete
    /// current transaction, laid out in whole 16-element sponge blocks --
    /// first the number of inputs (and padding), then one block per input
    /// (its commitment, then zeros), then one per output (its commitment,
    /// then its recovery nonce as eight 16-bit limbs). Inputs and outputs
    /// each in canonical order. Identical for every signer at any given
    /// moment; changes the instant anything about the transaction does.
    ///
    /// Over commitments rather than raw (lock, amount) pairs: each
    /// commitment binds its lock and amount just as firmly (it's a
    /// collision-resistant hash of them), and hashing a few field elements
    /// per entry -- instead of a whole public key, byte by byte -- is what
    /// a block's proof can afford to recompute. One item per block is
    /// what lets the proof receive each output's commitment and nonce
    /// together, so they can't be paired up differently. The input count
    /// keeps the boundary between inputs and outputs unambiguous.
    pub fn signing_message(&self) -> [BabyBear; 8] {
        let mut elements = vec![BabyBear::ZERO; 16];
        elements[0] = BabyBear::new(self.inputs.len() as u32);
        for input in &self.inputs {
            elements.extend(digest_from_bytes(&input.commitment()));
            elements.extend([BabyBear::ZERO; 8]);
        }
        for output in &self.outputs {
            elements.extend(digest_from_bytes(&output.commitment()));
            elements.extend(crate::output::nonce_limbs(&output.nonce));
        }
        hash_elements(DOMAIN_SIGNING, &elements)
    }

    /// Sign the input owned by `pubkey` with `secret_key`, over the
    /// transaction's current `signing_message()`. On success, this
    /// finalizes the transaction (see `is_finalized`). The caller is
    /// responsible for only ever calling this with the secret key that
    /// actually owns that input's public key -- if it doesn't,
    /// `sign_input` still succeeds mechanically (it has no way to check),
    /// but the resulting signature will simply fail `verify`. Returns
    /// `false` if no input for `pubkey` exists, or (astronomically
    /// unlikely) if the underlying WOTS signature fails to find a valid
    /// randomizer (see `wots::sign`).
    pub fn sign_input(&mut self, pubkey: &PublicKey, secret_key: &SecretKey) -> bool {
        if !self.inputs.iter().any(|i| i.key() == Some(pubkey)) {
            return false;
        }
        let message = self.signing_message();
        match wots::sign(secret_key, message) {
            Some(new) => {
                for input in &mut self.inputs {
                    if let Spend::Key { pubkey: key, signature, .. } = &mut input.spend
                        && key == pubkey
                    {
                        *signature = Some(new.clone());
                    }
                }
                self.finalized = true;
                true
            }
            None => false,
        }
    }

    /// Sign the policy input spending `commitment` as its branch's key
    /// `index` -- by `pubkey`, which at `proof` in its key tree must reach
    /// that key's id -- like `sign_input`. Returns `false` if there's no
    /// such input or key, or it already signed.
    pub fn sign_policy_input(&mut self, commitment: &[u8; 32], index: u8, pubkey: &PublicKey, proof: KeyProof, secret_key: &SecretKey) -> bool {
        let Some(message) = self.inputs.iter().find(|i| &i.commitment() == commitment).and_then(|i| self.message_for(i)) else {
            return false;
        };
        let Some(input) = self.inputs.iter_mut().find(|i| &i.commitment() == commitment) else {
            return false;
        };
        // (A REBIND signature leaves room to add inputs and outputs -- a fee
        // input and its change -- so it doesn't finalize the transaction.)
        let finalizes = !input.rebinds();
        let Spend::Policy(p) = &mut input.spend else {
            return false;
        };
        if p.branch.keys.get(index as usize) != Some(&proof.key_id(pubkey)) || p.signers.iter().any(|s| s.index == index) {
            return false;
        }
        let Some(signature) = wots::sign(secret_key, message) else {
            return false;
        };
        let pos = p.signers.partition_point(|s| s.index < index);
        p.signers.insert(pos, Signer { index, pubkey: pubkey.clone(), proof, signature: Some(signature) });
        self.finalized |= finalizes;
        true
    }

    /// Verify this transaction is internally sound and fully authorized --
    /// see the module docs for exactly what that does and doesn't cover.
    /// Notably, this says nothing about whether the transaction
    /// "balances" -- that requires knowing whether each claimed input is
    /// real, which requires chain state (or a proof about it) this type
    /// deliberately doesn't have access to -- nor about policy inputs'
    /// timelocks, which depend on the block (`locks_hold`).
    pub fn verify(&self) -> bool {
        // Inputs are always kept sorted by commitment (see `add_input`),
        // so a duplicate claim must sit in an adjacent pair -- no need to
        // compare every pair.
        if !self.inputs.windows(2).all(|w| w[0].commitment() < w[1].commitment()) {
            return false;
        }
        self.inputs.iter().all(|input| self.message_for(input).is_some_and(|message| input.authorized(message)))
    }

    /// Whether every policy input's timelocks hold in a block at `height`,
    /// each spent output having been created at `created(its commitment)`
    /// (`None`: unknown, so they don't).
    pub fn locks_hold(&self, height: u32, created: impl Fn(&[u8; 32]) -> Option<u32>) -> bool {
        self.inputs.iter().all(|input| match &input.spend {
            Spend::Key { .. } => true,
            Spend::Policy(p) => created(&input.commitment()).is_some_and(|c| p.branch.locks_hold(height, c)),
        })
    }

    /// How many of its signatures sign the transaction's message (not a
    /// REBIND message).
    pub fn all_signature_count(&self) -> usize {
        self.inputs
            .iter()
            .map(|i| match &i.spend {
                Spend::Key { .. } => 1,
                Spend::Policy(p) if p.branch.rebind.is_none() => p.branch.threshold as usize,
                Spend::Policy(_) => 0,
            })
            .sum()
    }

    /// How many signatures proving it takes: one per key input, the
    /// threshold per policy input.
    pub fn signature_count(&self) -> usize {
        self.inputs
            .iter()
            .map(|i| match &i.spend {
                Spend::Key { .. } => 1,
                Spend::Policy(p) => p.branch.threshold as usize,
            })
            .sum()
    }
}

impl Default for Transaction {
    fn default() -> Self {
        Self::new()
    }
}

/// The encoding's version byte.
const ENCODING_VERSION: u8 = 6;

/// Reads a byte encoding front to back.
struct Reader<'a>(&'a [u8]);

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let (head, tail) = (self.0.get(..n)?, self.0.get(n..)?);
        self.0 = tail;
        Some(head)
    }
    fn u8(&mut self) -> Option<u8> {
        Some(self.take(1)?[0])
    }
    fn u32(&mut self) -> Option<u32> {
        Some(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
    fn hash(&mut self) -> Option<[u8; 32]> {
        Some(self.take(32)?.try_into().unwrap())
    }
    fn optional<T>(&mut self, read: impl FnOnce(&mut Self) -> Option<T>) -> Option<Option<T>> {
        match self.u8()? {
            0 => Some(None),
            1 => Some(Some(read(self)?)),
            _ => None,
        }
    }
    fn signature(&mut self) -> Option<Option<Signature>> {
        self.optional(|r| wots::Signature::from_bytes(r.take(wots::SIGNATURE_LEN)?))
    }
    fn proof(&mut self) -> Option<KeyProof> {
        let index = self.u32()?;
        let path = (0..self.u8()?).map(|_| self.hash()).collect::<Option<_>>()?;
        Some(KeyProof { index, path })
    }
}

/// A key's place in its tree: its index (`u32`), and its path (a count
/// byte and hashes).
fn write_proof(out: &mut Vec<u8>, proof: &KeyProof) {
    out.extend(proof.index.to_le_bytes());
    out.push(proof.path.len() as u8);
    for sibling in &proof.path {
        out.extend(sibling);
    }
}

fn write_optional(out: &mut Vec<u8>, bytes: Option<Vec<u8>>) {
    match bytes {
        Some(b) => {
            out.push(1);
            out.extend(b);
        }
        None => out.push(0),
    }
}

impl Transaction {
    /// Byte encoding -- what's stored, written into files, and relayed:
    /// a version byte; the input count (`u16`) and each input -- its
    /// amount (`u64`), then `0` and a key spend (the public key, its place
    /// in its key tree -- an index (`u32`) and a path (a count byte and
    /// hashes) -- and an optional signature), or `1` and a policy spend (the branch: its
    /// threshold, key count, key hashes, `after_height`, `after_age`
    /// (`u32`s), optional hash lock and optional REBIND state (`u32`); its
    /// index (`u32`), path (a count byte and hashes), optional preimage,
    /// declared state (`u32`), named outputs (a count byte and
    /// commitments), and signers (a count byte, and
    /// each one's key index, public key, place in its key tree and
    /// optional signature)); the
    /// output count (`u16`) and each output. An optional field is a
    /// presence byte and then the field. Little-endian throughout.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = vec![ENCODING_VERSION];
        out.extend((self.inputs.len() as u16).to_le_bytes());
        for input in &self.inputs {
            out.extend(input.amount.to_le_bytes());
            match &input.spend {
                Spend::Key { pubkey, proof, signature } => {
                    out.push(0);
                    out.extend(pubkey.to_bytes());
                    write_proof(&mut out, proof);
                    write_optional(&mut out, signature.as_ref().map(|s| s.to_bytes()));
                }
                Spend::Policy(p) => {
                    out.push(1);
                    let b = &p.branch;
                    out.push(b.threshold);
                    out.push(b.keys.len() as u8);
                    for key in &b.keys {
                        out.extend(key);
                    }
                    out.extend(b.after_height.to_le_bytes());
                    out.extend(b.after_age.to_le_bytes());
                    write_optional(&mut out, b.hashlock.map(|x| x.to_vec()));
                    write_optional(&mut out, b.rebind.map(|s| s.to_le_bytes().to_vec()));
                    out.extend(p.index.to_le_bytes());
                    out.push(p.path.len() as u8);
                    for sibling in &p.path {
                        out.extend(sibling);
                    }
                    write_optional(&mut out, p.preimage.map(|x| x.to_vec()));
                    out.extend(p.state.to_le_bytes());
                    out.push(p.named.len() as u8);
                    for c in &p.named {
                        out.extend(c);
                    }
                    out.push(p.signers.len() as u8);
                    for s in &p.signers {
                        out.push(s.index);
                        out.extend(s.pubkey.to_bytes());
                        write_proof(&mut out, &s.proof);
                        write_optional(&mut out, s.signature.as_ref().map(|s| s.to_bytes()));
                    }
                }
            }
        }
        out.extend((self.outputs.len() as u16).to_le_bytes());
        for output in &self.outputs {
            out.extend(output.to_bytes());
        }
        out
    }

    /// Decode, the inverse of `to_bytes` -- strictly: nothing may be left
    /// over, and inputs, outputs and each policy input's signers must
    /// already be in canonical order (so every transaction has exactly one
    /// encoding). Says nothing about whether it's validly signed; that's
    /// `verify`.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut r = Reader(bytes);
        if r.u8()? != ENCODING_VERSION {
            return None;
        }
        let mut tx = Transaction::new();
        let inputs = u16::from_le_bytes(r.take(2)?.try_into().unwrap());
        for _ in 0..inputs {
            let amount = u64::from_le_bytes(r.take(8)?.try_into().unwrap());
            let spend = match r.u8()? {
                0 => {
                    let pubkey = PublicKey::from_bytes(r.take(wots::PUBLIC_KEY_LEN)?)?;
                    let proof = r.proof()?;
                    Spend::Key { pubkey, proof, signature: r.signature()? }
                }
                1 => {
                    let threshold = r.u8()?;
                    let keys = (0..r.u8()?).map(|_| r.hash()).collect::<Option<_>>()?;
                    let (after_height, after_age) = (r.u32()?, r.u32()?);
                    let hashlock = r.optional(|r| r.hash())?;
                    let rebind = r.optional(|r| r.u32())?;
                    let branch = Branch { threshold, keys, after_height, after_age, hashlock, rebind };
                    let index = r.u32()?;
                    let path = (0..r.u8()?).map(|_| r.hash()).collect::<Option<_>>()?;
                    let preimage = r.optional(|r| r.hash())?;
                    let state = r.u32()?;
                    let named: Vec<[u8; 32]> = (0..r.u8()?).map(|_| r.hash()).collect::<Option<_>>()?;
                    if !named.windows(2).all(|w| w[0] < w[1]) {
                        return None;
                    }
                    let mut signers = Vec::new();
                    for _ in 0..r.u8()? {
                        let index = r.u8()?;
                        let pubkey = PublicKey::from_bytes(r.take(wots::PUBLIC_KEY_LEN)?)?;
                        let proof = r.proof()?;
                        signers.push(Signer { index, pubkey, proof, signature: r.signature()? });
                    }
                    if !signers.windows(2).all(|w| w[0].index < w[1].index) {
                        return None;
                    }
                    Spend::Policy(PolicySpend { branch, index, path, preimage, state, named, signers })
                }
                _ => return None,
            };
            tx.inputs.push(Input { amount, spend });
        }
        let outputs = u16::from_le_bytes(r.take(2)?.try_into().unwrap());
        for _ in 0..outputs {
            tx.outputs.push(Output::from_bytes(r.take(crate::output::OUTPUT_LEN)?)?);
        }
        if !r.0.is_empty() {
            return None;
        }
        let inputs_sorted = tx.inputs.windows(2).all(|w| w[0].commitment() < w[1].commitment());
        let outputs_sorted = tx.outputs.windows(2).all(|w| w[0].to_bytes() <= w[1].to_bytes());
        if !inputs_sorted || !outputs_sorted {
            return None;
        }
        tx.finalized = tx.inputs.iter().any(|i| !i.rebinds() && !i.signatures().is_empty());
        Some(tx)
    }

    /// This transaction's id: a hash of its encoding.
    pub fn id(&self) -> [u8; 32] {
        crate::poseidon2::hash_bytes_32(&self.to_bytes())
    }

    /// The fee this transaction leaves for the miner: inputs minus
    /// outputs, or `None` if the outputs exceed the inputs (or a sum
    /// overflows).
    pub fn fee(&self) -> Option<u64> {
        let spent = self.inputs.iter().try_fold(0u64, |a, i| a.checked_add(i.amount))?;
        let created = self.outputs.iter().try_fold(0u64, |a, o| a.checked_add(o.amount))?;
        spent.checked_sub(created)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn keypair(byte: u8) -> (SecretKey, PublicKey) {
        wots::keygen(&[byte; 32])
    }

    fn new_output(byte: u8, amount: u64) -> Output {
        let (_, pk) = keypair(byte);
        Output::new(&pk, amount)
    }

    #[test]
    fn encoding_round_trips_and_is_strict() {
        let (sk_a, pk_a) = keypair(1);
        let (_, pk_b) = keypair(2);
        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 100).unwrap();
        tx.add_output(new_output(3, 60)).unwrap();
        tx.add_output(new_output(4, 30)).unwrap();
        // Unsigned, then signed.
        let unsigned = Transaction::from_bytes(&tx.to_bytes()).unwrap();
        assert!(!unsigned.is_finalized() && unsigned.to_bytes() == tx.to_bytes());
        assert!(tx.sign_input(&pk_a, &sk_a));
        let decoded = Transaction::from_bytes(&tx.to_bytes()).unwrap();
        assert!(decoded.verify() && decoded.is_finalized());
        assert_eq!(decoded.id(), tx.id());
        assert_eq!(decoded.fee(), Some(10));
        // Trailing bytes, truncation, an unknown version.
        let bytes = tx.to_bytes();
        assert!(Transaction::from_bytes(&[&bytes[..], &[0]].concat()).is_none());
        assert!(Transaction::from_bytes(&bytes[..bytes.len() - 1]).is_none());
        let mut versioned = bytes.clone();
        versioned[0] = 9;
        assert!(Transaction::from_bytes(&versioned).is_none());
        // Inputs out of canonical order.
        let mut two = Transaction::new();
        two.add_input(&pk_a, 1).unwrap();
        two.add_input(&pk_b, 2).unwrap();
        let mut swapped = two.clone();
        swapped.inputs.swap(0, 1);
        assert!(Transaction::from_bytes(&two.to_bytes()).is_some());
        assert!(Transaction::from_bytes(&swapped.to_bytes()).is_none());
    }

    #[test]
    fn valid_transaction_verifies() {
        let (sk_a, pk_a) = keypair(1);
        let (sk_b, pk_b) = keypair(2);

        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 100).unwrap();
        tx.add_input(&pk_b, 100).unwrap();
        tx.add_output(new_output(200, 200)).unwrap();

        assert!(tx.sign_input(&pk_a, &sk_a));
        assert!(tx.sign_input(&pk_b, &sk_b));
        assert!(tx.verify());
    }

    #[test]
    fn unsigned_input_rejected() {
        let (_, pk_a) = keypair(1);
        let (sk_b, pk_b) = keypair(2);

        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 100).unwrap();
        tx.add_input(&pk_b, 100).unwrap();
        tx.add_output(new_output(200, 200)).unwrap();

        // Only pk_b's input gets signed; pk_a's is left unsigned.
        assert!(tx.sign_input(&pk_b, &sk_b));
        assert!(!tx.verify());
    }

    #[test]
    fn tampered_output_rejected() {
        let (sk_a, pk_a) = keypair(1);

        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 200).unwrap();
        tx.add_output(new_output(200, 200)).unwrap();
        assert!(tx.sign_input(&pk_a, &sk_a));
        assert!(tx.verify());

        // Directly overwriting a committed output (bypassing add_output)
        // must still break the signature, since the signing message
        // commits to the exact output bytes.
        tx.outputs[0] = new_output(201, 200);
        assert!(!tx.verify());
    }

    #[test]
    fn tampered_signature_rejected() {
        let (sk_a, pk_a) = keypair(1);

        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 200).unwrap();
        tx.add_output(new_output(200, 200)).unwrap();
        tx.sign_input(&pk_a, &sk_a);

        let Spend::Key { signature: Some(sig), .. } = &mut tx.inputs[0].spend else { panic!("a signed key input") };
        sig.randomizer[0] = sig.randomizer[0] + BabyBear::new(1);
        assert!(!tx.verify());
    }

    #[test]
    fn wrong_secret_key_rejected() {
        let (_, pk_a) = keypair(1);
        let (sk_b, _) = keypair(2);

        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 200).unwrap();
        tx.add_output(new_output(200, 200)).unwrap();

        // Signing pk_a's input with an unrelated secret key succeeds
        // mechanically -- `sign_input` has no way to know the key is
        // wrong -- but the resulting signature doesn't verify against
        // pk_a.
        assert!(tx.sign_input(&pk_a, &sk_b));
        assert!(!tx.verify());
    }

    /// Two inputs claiming the same public key must be rejected. With
    /// inputs addressed by pubkey, there's no way to even aim a signature
    /// at "the second one specifically" -- which is fine, since `verify`
    /// catches the duplicate before signatures matter at all.
    #[test]
    fn duplicate_pubkey_rejected() {
        let (_, pk_a) = keypair(1);

        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 100).unwrap();
        tx.add_input(&pk_a, 100).unwrap();
        tx.add_output(new_output(200, 200)).unwrap();

        assert!(!tx.verify());
    }

    #[test]
    fn sign_input_rejects_unknown_pubkey() {
        let (sk_a, pk_a) = keypair(1);
        let mut tx = Transaction::new();
        assert!(!tx.sign_input(&pk_a, &sk_a));
    }

    #[test]
    fn empty_transaction_verifies() {
        // No inputs, no outputs, nothing to sign -- trivially valid on
        // its own. Whether an empty transaction makes sense is a
        // question for whatever's constructing one, not this module.
        let tx = Transaction::new();
        assert!(tx.verify());
    }

    /// Tampering with a claimed input amount after signing breaks the
    /// signature -- `amount` is part of what's signed, so the signer is
    /// pinned to a specific (pubkey, amount) pair, not just a pubkey.
    #[test]
    fn tampered_claimed_input_amount_rejected() {
        let (sk_a, pk_a) = keypair(1);
        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 200).unwrap();
        tx.add_output(new_output(200, 200)).unwrap();
        tx.sign_input(&pk_a, &sk_a);
        assert!(tx.verify());

        tx.inputs[0].amount += 1;
        assert!(!tx.verify());
    }

    /// Redistributing value between two outputs still has to break
    /// verification, since each output's bytes -- including its
    /// individual amount -- are part of what the shared signature
    /// commits to, not just the sum.
    #[test]
    fn redistributing_output_amounts_breaks_signatures() {
        let (sk_a, pk_a) = keypair(1);
        let (_, pk_out_1) = keypair(201);
        let (_, pk_out_2) = keypair(202);

        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 200).unwrap();
        tx.add_output(Output::new(&pk_out_1, 100)).unwrap();
        tx.add_output(Output::new(&pk_out_2, 100)).unwrap();
        tx.sign_input(&pk_a, &sk_a);
        assert!(tx.verify());

        // Same total (200), different split -- still breaks the signature.
        tx.outputs[0] = Output::new(&pk_out_1, 150);
        tx.outputs[1] = Output::new(&pk_out_2, 50);
        assert!(!tx.verify());
    }

    /// The core point of today's change: once any input is signed, the
    /// transaction is finalized -- `add_input`/`add_output` are rejected
    /// outright (`Error::Finalized`) rather than silently mutating the
    /// signing message. Nothing gets added, so the existing signature
    /// stays completely valid.
    #[test]
    fn adding_after_signing_is_rejected_and_leaves_signatures_intact() {
        let (sk_a, pk_a) = keypair(1);
        let (_, pk_b) = keypair(2);

        let mut tx = Transaction::new();
        tx.add_output(new_output(200, 100)).unwrap();
        tx.add_input(&pk_a, 100).unwrap();
        assert!(tx.sign_input(&pk_a, &sk_a));
        assert!(tx.verify());
        assert!(tx.is_finalized());

        // A second input shows up only after A already signed.
        assert_eq!(tx.add_input(&pk_b, 50), Err(Error::Finalized));
        assert_eq!(tx.inputs.len(), 1); // nothing was actually added
        assert!(tx.verify()); // A's signature is completely unaffected

        // Likewise for a new output.
        assert_eq!(tx.add_output(new_output(201, 50)), Err(Error::Finalized));
        assert_eq!(tx.outputs.len(), 1);
        assert!(tx.verify());
    }

    #[test]
    fn is_finalized_reflects_whether_any_input_has_been_signed() {
        let (sk_a, pk_a) = keypair(1);
        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 100).unwrap();
        tx.add_output(new_output(200, 100)).unwrap();
        assert!(!tx.is_finalized());

        assert!(tx.sign_input(&pk_a, &sk_a));
        assert!(tx.is_finalized());
    }

    /// Three independent parties, adding their inputs and outputs in an
    /// arbitrarily interleaved order -- including outputs interleaved
    /// with inputs, not just inputs with each other -- and only signing
    /// once every input and output is in place.
    #[test]
    fn multiple_parties_interleave_adds_then_sign_once_finalized() {
        let (sk_a, pk_a) = keypair(1);
        let (sk_b, pk_b) = keypair(2);
        let (sk_c, pk_c) = keypair(3);

        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 100).unwrap();
        tx.add_output(new_output(200, 150)).unwrap(); // a recipient's output arrives early
        tx.add_input(&pk_b, 100).unwrap();
        tx.add_input(&pk_c, 100).unwrap();
        tx.add_output(new_output(201, 150)).unwrap(); // a second recipient, added later

        // No one has signed yet, so signing in any order is fine.
        assert!(tx.sign_input(&pk_c, &sk_c));
        assert!(tx.sign_input(&pk_a, &sk_a));
        assert!(tx.sign_input(&pk_b, &sk_b));

        assert!(tx.verify());
    }

    /// The recipient-first, Grin-style flow: whoever is *receiving* funds
    /// generates their keypair and contributes the new output before the
    /// sender ever touches the transaction; the sender then adds their
    /// own input(s) and signs once everything is in place; finally either
    /// party -- or chain validation -- can check the result with no
    /// further input from either of them.
    #[test]
    fn recipient_first_grin_style_flow() {
        // Recipient's side: generate a keypair, decide the amount they're
        // meant to receive, hand only the resulting `Output` to the
        // sender. No signature, no secret key, ever leaves their hands.
        let (_recipient_secret, recipient_pubkey) = keypair(100);
        let recipient_output = Output::new(&recipient_pubkey, 200);

        let mut tx = Transaction::new();
        tx.add_output(recipient_output).unwrap();

        // Sender's side: add the input(s) they're spending, then sign
        // only once both are present.
        let (secret_a, pubkey_a) = keypair(1);
        let (secret_b, pubkey_b) = keypair(2);
        tx.add_input(&pubkey_a, 100).unwrap();
        tx.add_input(&pubkey_b, 100).unwrap();
        tx.sign_input(&pubkey_a, &secret_a);
        tx.sign_input(&pubkey_b, &secret_b);

        // Either the recipient or chain validation can now check it.
        assert!(tx.verify());
    }

    /// The actual point of the sorting change: inputs end up in the same
    /// canonical order (ascending by commitment) no matter what order they
    /// were added in.
    #[test]
    fn inputs_are_kept_sorted_by_commitment_regardless_of_insertion_order() {
        let (_, pk_a) = keypair(1);
        let (_, pk_b) = keypair(2);
        let (_, pk_c) = keypair(3);

        let mut forward = Transaction::new();
        forward.add_input(&pk_a, 1).unwrap();
        forward.add_input(&pk_b, 1).unwrap();
        forward.add_input(&pk_c, 1).unwrap();

        let mut backward = Transaction::new();
        backward.add_input(&pk_c, 1).unwrap();
        backward.add_input(&pk_b, 1).unwrap();
        backward.add_input(&pk_a, 1).unwrap();

        let forward_keys: Vec<[u8; 32]> = forward.inputs.iter().map(Input::commitment).collect();
        let backward_keys: Vec<[u8; 32]> = backward.inputs.iter().map(Input::commitment).collect();
        assert_eq!(forward_keys, backward_keys);

        let mut sorted = forward_keys.clone();
        sorted.sort();
        assert_eq!(forward_keys, sorted);
    }

    /// Outputs get the same canonical-ordering treatment as inputs, for
    /// the same reason: two transactions built by adding the same outputs
    /// in a different order must still produce the same signing message.
    #[test]
    fn outputs_are_kept_sorted_regardless_of_insertion_order() {
        let out_a = new_output(1, 10);
        let out_b = new_output(2, 20);
        let out_c = new_output(3, 30);

        let mut forward = Transaction::new();
        forward.add_output(out_a).unwrap();
        forward.add_output(out_b).unwrap();
        forward.add_output(out_c).unwrap();

        let mut backward = Transaction::new();
        backward.add_output(out_c).unwrap();
        backward.add_output(out_b).unwrap();
        backward.add_output(out_a).unwrap();

        assert_eq!(forward.outputs, backward.outputs);
        assert_eq!(forward.signing_message(), backward.signing_message());
    }

    /// Two transactions assembled by interleaving the same inputs and
    /// outputs in completely different orders must still agree on exactly
    /// what's being signed -- the whole point of sorting both lists.
    #[test]
    fn interleaving_order_does_not_affect_the_signing_message() {
        let (_, pk_a) = keypair(1);
        let (_, pk_b) = keypair(2);
        let out_1 = new_output(201, 100);
        let out_2 = new_output(202, 50);

        let mut one_order = Transaction::new();
        one_order.add_input(&pk_a, 100).unwrap();
        one_order.add_output(out_1).unwrap();
        one_order.add_input(&pk_b, 50).unwrap();
        one_order.add_output(out_2).unwrap();

        let mut other_order = Transaction::new();
        other_order.add_output(out_2).unwrap();
        other_order.add_output(out_1).unwrap();
        other_order.add_input(&pk_b, 50).unwrap();
        other_order.add_input(&pk_a, 100).unwrap();

        assert_eq!(one_order.signing_message(), other_order.signing_message());
    }
}
