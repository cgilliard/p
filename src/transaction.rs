//! Transactions: just inputs (spent outputs, identified by their owner's
//! revealed public key, plus the amount being spent) and outputs, nothing
//! else -- no scripts. Fees are implicit: if total input amount exceeds
//! total output amount, the difference is the fee. There's no separate fee
//! field or recipient for it (e.g. no block-reward-style payout to whoever
//! includes the transaction) -- that's a question for whatever assembles a
//! block out of transactions, not this module.
//!
//! This module has **no notion of `pmmr`, a block, or where in the chain an
//! output actually lives** -- deliberately so. An input is identified
//! purely by the public key of the output it spends (`Output::new` already
//! determines the output from a (pubkey, amount) pair, so there's nothing
//! else to reference) and nothing else. `Transaction` is a small,
//! self-contained, reusable primitive: building, signing, and checking a
//! transaction's own internal correctness never needs to know anything
//! about how outputs are actually indexed, so this same type can be used
//! wherever a transaction needs handling -- a mempool, a wallet, a test,
//! block assembly -- without dragging any of those contexts' specifics in.
//! Resolving an input against real chain state (does this (pubkey, amount)
//! correspond to a real, unspent output, and where) is entirely someone
//! else's problem, for later.
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
//! their canonical sorted order, followed by every output, also sorted.
//! This is the strong commitment, not a "just my own input" one: once
//! anyone has signed, changing the input set *or* the output set in any
//! way -- adding, removing, or altering either -- invalidates *every*
//! existing signature, not just whichever part changed. That's
//! intentional: it's what makes "this transaction" a single, well-defined
//! thing, rather than a fixed output list that happens to be satisfiable
//! by many different, interchangeable combinations of inputs.
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
//! tx.add_input(&pubkey_b, 100).unwrap();    // inputs, freely interleaved,
//!                                           // is fine -- until anyone signs.
//!
//! tx.sign_input(&pubkey_a, &secret_a);
//! tx.sign_input(&pubkey_b, &secret_b);
//! assert!(tx.verify());
//! ```
//!
//! Two things this module checks are internal to the transaction, and one
//! thing it deliberately leaves to the caller:
//!
//! - Checked here: every input is signed over the complete transaction, no
//!   two inputs claim the same public key, and total input amount is at
//!   least total output amount.
//! - Left to the caller: whether each claimed (pubkey, amount) input
//!   actually, currently corresponds to a real, unspent output somewhere,
//!   and whether the same output gets spent by more than one transaction
//!   (double-spending). Both are questions about a specific output set at
//!   a specific moment (i.e. block validation against a particular `pmmr`
//!   and bitmap), not about the transaction by itself -- a `Transaction`
//!   can be fully internally valid while every one of its claimed inputs
//!   turns out to be fabricated or already spent, and catching that is
//!   explicitly not this module's job.

// `main.rs` doesn't call into this module yet (it just prints "Hello
// world!"), so allow dead code here rather than suppressing warnings
// piecemeal -- this module exists to be exercised by its tests for now.
#![allow(dead_code)]

use crate::output::Output;
use crate::poseidon2::{BabyBear, hash_bytes};
use crate::wots::{self, PublicKey, SecretKey, Signature};

/// Domain separator for the transaction signing message. Bumped to `-v2`
/// because what gets signed changed shape (the whole transaction, not one
/// input's own slice of it) -- a `-v1` message could never collide with
/// one of these anyway (the byte layout differs), but a distinct version
/// tag keeps that obvious rather than relying on it.
const SIGNING_DOMAIN: &[u8] = b"transaction-v2";

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

/// One spent output: the owner's revealed public key, the claimed amount
/// being spent, and their signature over the whole transaction's signing
/// message once they've provided it.
#[derive(Clone, Debug)]
pub struct Input {
    pub pubkey: PublicKey,
    pub amount: u64,
    pub signature: Option<Signature>,
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

    /// Add an input spending `amount` from the output owned by `pubkey`,
    /// inserting it into its sorted position among the existing inputs
    /// (see the module docs) rather than just appending. Returns
    /// `Err(Error::Finalized)` without adding anything if the transaction
    /// has already collected a signature.
    pub fn add_input(&mut self, pubkey: &PublicKey, amount: u64) -> Result<()> {
        if self.finalized {
            return Err(Error::Finalized);
        }
        let key_bytes = pubkey.to_bytes();
        let pos = self
            .inputs
            .partition_point(|existing| existing.pubkey.to_bytes() < key_bytes);
        self.inputs.insert(
            pos,
            Input {
                pubkey: pubkey.clone(),
                amount,
                signature: None,
            },
        );
        Ok(())
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
    /// current transaction -- every input's (pubkey, amount) in their
    /// canonical sorted order, then every output, also sorted. Identical
    /// for every signer at any given moment; changes the instant the
    /// input or output set changes at all (see the module docs).
    pub fn signing_message(&self) -> [BabyBear; 8] {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(SIGNING_DOMAIN);
        for input in &self.inputs {
            bytes.extend_from_slice(&input.pubkey.to_bytes());
            bytes.extend_from_slice(&input.amount.to_le_bytes());
        }
        for output in &self.outputs {
            bytes.extend_from_slice(&output.to_bytes());
        }
        hash_bytes(&bytes)
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
        if !self.inputs.iter().any(|i| &i.pubkey == pubkey) {
            return false;
        }
        let message = self.signing_message();
        match wots::sign(secret_key, message) {
            Some(signature) => {
                let input = self
                    .inputs
                    .iter_mut()
                    .find(|i| &i.pubkey == pubkey)
                    .expect("existence just checked above");
                input.signature = Some(signature);
                self.finalized = true;
                true
            }
            None => false,
        }
    }

    /// Verify this transaction is internally sound and fully authorized --
    /// see the module docs for exactly what that does and doesn't cover.
    pub fn verify(&self) -> bool {
        // Inputs are always kept sorted by public key (see `add_input`),
        // so a duplicate claim must sit in an adjacent pair -- no need to
        // compare every pair.
        for i in 1..self.inputs.len() {
            if self.inputs[i].pubkey == self.inputs[i - 1].pubkey {
                return false;
            }
        }

        // Total claimed input value must be at least total output value;
        // any excess is an implicit fee (no separate fee field, and no
        // payee for it here -- that's for whoever assembles a block).
        // Accumulated in u128 so realistic u64 amounts can never overflow
        // this check.
        let input_total: u128 = self.inputs.iter().map(|i| i.amount as u128).sum();
        let output_total: u128 = self.outputs.iter().map(|o| o.amount as u128).sum();
        if input_total < output_total {
            return false;
        }

        let message = self.signing_message();
        for input in &self.inputs {
            let Some(signature) = &input.signature else {
                return false;
            };
            if !wots::verify(&input.pubkey, message, signature) {
                return false;
            }
        }

        true
    }
}

impl Default for Transaction {
    fn default() -> Self {
        Self::new()
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

        tx.inputs[0].signature.as_mut().unwrap().randomizer[0] =
            tx.inputs[0].signature.as_ref().unwrap().randomizer[0] + BabyBear::new(1);
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
        // No inputs, no outputs, nothing to sign, and 0 >= 0 -- trivially
        // valid on its own. Whether an empty transaction makes sense is a
        // question for whatever's constructing one, not this module.
        let tx = Transaction::new();
        assert!(tx.verify());
    }

    #[test]
    fn input_short_of_output_rejected() {
        let (sk_a, pk_a) = keypair(1);
        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 100).unwrap();
        tx.add_output(new_output(200, 200)).unwrap(); // claims more than is spent
        tx.sign_input(&pk_a, &sk_a);
        assert!(!tx.verify());
    }

    /// Spending more than the outputs create is allowed -- the difference
    /// is an implicit fee, not an error.
    #[test]
    fn input_exceeding_output_is_an_implicit_fee() {
        let (sk_a, pk_a) = keypair(1);
        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 300).unwrap();
        tx.add_output(new_output(200, 200)).unwrap(); // 100 goes unaccounted for -- the fee
        tx.sign_input(&pk_a, &sk_a);
        assert!(tx.verify());
    }

    #[test]
    fn tampered_claimed_input_amount_rejected() {
        let (sk_a, pk_a) = keypair(1);
        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 200).unwrap();
        tx.add_output(new_output(200, 200)).unwrap();
        tx.sign_input(&pk_a, &sk_a);
        assert!(tx.verify());

        // Bumping the claimed amount after signing (direct field access,
        // bypassing add_input) breaks the signature (the message commits
        // to it), independent of the balance check.
        tx.inputs[0].amount += 1;
        assert!(!tx.verify());
    }

    /// Redistributing value between two outputs keeps the *total* balanced
    /// but still has to break verification, since each output's bytes --
    /// including its individual amount -- are part of what the shared
    /// signature commits to, not just the sum.
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
    /// party -- or a block validator -- can check the result with no
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

        // Either the recipient or a block validator can now check it.
        assert!(tx.verify());
    }

    /// The actual point of the sorting change: inputs end up in the same
    /// canonical order (ascending by public key bytes) no matter what
    /// order they were added in.
    #[test]
    fn inputs_are_kept_sorted_by_pubkey_regardless_of_insertion_order() {
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

        let forward_keys: Vec<Vec<u8>> = forward.inputs.iter().map(|i| i.pubkey.to_bytes()).collect();
        let backward_keys: Vec<Vec<u8>> = backward.inputs.iter().map(|i| i.pubkey.to_bytes()).collect();
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
