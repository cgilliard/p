//! Transactions: just inputs (spent outputs, identified by their owner's
//! revealed public key, plus the amount being spent) and outputs, nothing
//! else -- no scripts. Fees are implicit: if total input amount exceeds
//! total output amount, the difference is the fee. There's no separate fee
//! field or recipient for it (e.g. no block-reward-style payout to whoever
//! includes the transaction) -- that's a question for whatever assembles a
//! block out of transactions, not this module.
//!
//! This module has **no dependency on `pmmr` or any other output-storage
//! scheme whatsoever** -- deliberately so. An input is identified purely by
//! the public key of the output it spends (`Output::new` already
//! determines the output from a (pubkey, amount) pair, so there's nothing
//! else to reference), not by a position or an inclusion proof. That makes
//! `Transaction` a small, self-contained, reusable primitive: building,
//! signing, and checking a transaction's own internal correctness never
//! needs to know anything about where or how outputs are actually indexed,
//! so this same type can be used wherever a transaction needs handling --
//! a mempool, a wallet, a test, block validation -- without dragging any of
//! those contexts' specifics in.
//!
//! Two things this module checks are internal to the transaction, and two
//! things it deliberately leaves to the caller:
//!
//! - Checked here: every input is signed, no two inputs claim the same
//!   public key, every signature is valid over its own signing message,
//!   and total input amount is at least total output amount.
//! - Left to the caller: whether each claimed (pubkey, amount) input
//!   actually, currently corresponds to a real, unspent output somewhere,
//!   and whether the same output gets spent by more than one transaction
//!   (double-spending). Both are questions about a specific output set at
//!   a specific moment (i.e. block validation against a particular `pmmr`,
//!   or whatever storage a given context uses), not about the transaction
//!   by itself -- a `Transaction` can be fully internally valid while every
//!   one of its claimed inputs turns out to be fabricated or already
//!   spent, and catching that is explicitly not this module's job.
//!
//! # Building a transaction, with multiple independent signers
//!
//! `Transaction` is built incrementally and mutably. The key design point,
//! and the thing that makes a genuine multi-party flow work: **each
//! input's signature covers only that input's own (pubkey, amount) plus
//! the outputs -- not any other input.** A signer is authorizing "I'm
//! contributing this much, toward these specific outputs," full stop; they
//! don't need to know or care who else contributes other inputs, or how
//! many there end up being. That means inputs can be added and signed by
//! any number of independent parties, interleaved in any order, and adding
//! one input's signature never invalidates another's.
//!
//! The one ordering rule that still matters: **outputs need to be finalized
//! before any input is signed.** Every input's signature covers the full
//! current output list, so adding or changing an output after some input
//! is already signed invalidates that signature (by design -- an input's
//! owner needs their authorization to actually depend on where the funds
//! are going). This is exactly the recipient-first flow: the recipient
//! decides the outputs and contributes them first; only then do one or
//! more senders add and sign their inputs, in whatever order suits them.
//!
//! ```ignore
//! let mut tx = Transaction::new();
//! tx.add_output(new_output); // outputs finalized first
//!
//! let i0 = tx.add_input(pubkey_a, 100);
//! tx.sign_input(i0, &secret_a);       // signer A signs
//! let i1 = tx.add_input(pubkey_b, 100); // signer B's input arrives later
//! tx.sign_input(i1, &secret_b);       // signer A's signature above is unaffected
//!
//! assert!(tx.verify());
//! ```

// `main.rs` doesn't call into this module yet (it just prints "Hello
// world!"), so allow dead code here rather than suppressing warnings
// piecemeal -- this module exists to be exercised by its tests for now.
#![allow(dead_code)]

use crate::output::Output;
use crate::poseidon2::{BabyBear, hash_bytes};
use crate::wots::{self, PublicKey, SecretKey, Signature};

/// Domain separator for the transaction signing message, so it can never be
/// confused with a hash produced for some other purpose that happens to
/// reuse the same (pubkey, amount, outputs) byte shape.
const SIGNING_DOMAIN: &[u8] = b"transaction-v1";

/// One spent output: the owner's revealed public key, the claimed amount
/// being spent, and their signature over that input's own signing message
/// once they've provided it.
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
}

impl Transaction {
    pub fn new() -> Self {
        Transaction {
            inputs: Vec::new(),
            outputs: Vec::new(),
        }
    }

    /// Add an input spending `amount` from the output owned by `pubkey`.
    /// Unsigned until `sign_input` is called for the returned index.
    pub fn add_input(&mut self, pubkey: PublicKey, amount: u64) -> usize {
        self.inputs.push(Input {
            pubkey,
            amount,
            signature: None,
        });
        self.inputs.len() - 1
    }

    pub fn add_output(&mut self, output: Output) {
        self.outputs.push(output);
    }

    /// The message a signature over `(pubkey, amount)` must cover, given
    /// this transaction's current outputs: a hash binding that one input's
    /// own data to every current output, deliberately *not* to any other
    /// input -- see the module docs for why.
    fn message_for(&self, pubkey: &PublicKey, amount: u64) -> [BabyBear; 8] {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(SIGNING_DOMAIN);
        bytes.extend_from_slice(&pubkey.to_bytes());
        bytes.extend_from_slice(&amount.to_le_bytes());
        for output in &self.outputs {
            bytes.extend_from_slice(&output.to_bytes());
        }
        hash_bytes(&bytes)
    }

    /// The message the input at `index` must be (or already is) signed
    /// over, or `None` if `index` is out of range.
    pub fn input_signing_message(&self, index: usize) -> Option<[BabyBear; 8]> {
        let input = self.inputs.get(index)?;
        Some(self.message_for(&input.pubkey, input.amount))
    }

    /// Sign the input at `index` with `secret_key`. The caller is
    /// responsible for only ever calling this with the secret key that
    /// actually owns that input's public key -- if it doesn't,
    /// `sign_input` still succeeds mechanically (it has no way to check),
    /// but the resulting signature will simply fail `verify`. Returns
    /// `false` if `index` is out of range, or (astronomically unlikely) if
    /// the underlying WOTS signature fails to find a valid randomizer (see
    /// `wots::sign`).
    pub fn sign_input(&mut self, index: usize, secret_key: &SecretKey) -> bool {
        let Some(message) = self.input_signing_message(index) else {
            return false;
        };
        match wots::sign(secret_key, message) {
            Some(signature) => {
                self.inputs[index].signature = Some(signature);
                true
            }
            None => false,
        }
    }

    /// Verify this transaction is internally sound and fully authorized --
    /// see the module docs for exactly what that does and doesn't cover.
    pub fn verify(&self) -> bool {
        for i in 0..self.inputs.len() {
            for j in (i + 1)..self.inputs.len() {
                if self.inputs[i].pubkey == self.inputs[j].pubkey {
                    return false;
                }
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

        for input in &self.inputs {
            let Some(signature) = &input.signature else {
                return false;
            };
            let message = self.message_for(&input.pubkey, input.amount);
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
        let i0 = tx.add_input(pk_a, 100);
        let i1 = tx.add_input(pk_b, 100);
        tx.add_output(new_output(200, 200));

        assert!(tx.sign_input(i0, &sk_a));
        assert!(tx.sign_input(i1, &sk_b));
        assert!(tx.verify());
    }

    #[test]
    fn unsigned_input_rejected() {
        let (_, pk_a) = keypair(1);
        let (sk_b, pk_b) = keypair(2);

        let mut tx = Transaction::new();
        tx.add_input(pk_a, 100);
        let i1 = tx.add_input(pk_b, 100);
        tx.add_output(new_output(200, 200));

        // Only input 1 gets signed; input 0 is left unsigned.
        assert!(tx.sign_input(i1, &sk_b));
        assert!(!tx.verify());
    }

    #[test]
    fn tampered_output_rejected() {
        let (sk_a, pk_a) = keypair(1);

        let mut tx = Transaction::new();
        let i0 = tx.add_input(pk_a, 200);
        tx.add_output(new_output(200, 200));
        assert!(tx.sign_input(i0, &sk_a));
        assert!(tx.verify());

        // Swapping in a different output after signing must break the
        // signature, since the signing message commits to the exact
        // output bytes.
        tx.outputs[0] = new_output(201, 200);
        assert!(!tx.verify());
    }

    #[test]
    fn tampered_signature_rejected() {
        let (sk_a, pk_a) = keypair(1);

        let mut tx = Transaction::new();
        let i0 = tx.add_input(pk_a, 200);
        tx.add_output(new_output(200, 200));
        tx.sign_input(i0, &sk_a);

        tx.inputs[0].signature.as_mut().unwrap().randomizer[0] =
            tx.inputs[0].signature.as_ref().unwrap().randomizer[0] + BabyBear::new(1);
        assert!(!tx.verify());
    }

    #[test]
    fn wrong_secret_key_rejected() {
        let (_, pk_a) = keypair(1);
        let (sk_b, _) = keypair(2);

        let mut tx = Transaction::new();
        let i0 = tx.add_input(pk_a, 200);
        tx.add_output(new_output(200, 200));

        // Signing input 0 (owned by pk_a) with an unrelated secret key
        // succeeds mechanically -- `sign_input` has no way to know the key
        // is wrong -- but the resulting signature doesn't verify against
        // pk_a.
        assert!(tx.sign_input(i0, &sk_b));
        assert!(!tx.verify());
    }

    #[test]
    fn duplicate_pubkey_rejected() {
        let (sk_a, pk_a) = keypair(1);

        let mut tx = Transaction::new();
        let i0 = tx.add_input(pk_a.clone(), 100);
        let i1 = tx.add_input(pk_a, 100);
        tx.add_output(new_output(200, 200));

        tx.sign_input(i0, &sk_a);
        // Re-derive the same secret key for the second (duplicate) input --
        // SecretKey has no Clone, by design.
        let (sk_a_again, _) = keypair(1);
        tx.sign_input(i1, &sk_a_again);

        assert!(!tx.verify());
    }

    #[test]
    fn sign_input_rejects_out_of_range_index() {
        let (sk_a, _) = keypair(1);
        let mut tx = Transaction::new();
        assert!(!tx.sign_input(0, &sk_a));
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
        let i0 = tx.add_input(pk_a, 100);
        tx.add_output(new_output(200, 200)); // claims to create more than is spent
        tx.sign_input(i0, &sk_a);
        assert!(!tx.verify());
    }

    /// Spending more than the outputs create is allowed -- the difference
    /// is an implicit fee, not an error.
    #[test]
    fn input_exceeding_output_is_an_implicit_fee() {
        let (sk_a, pk_a) = keypair(1);
        let mut tx = Transaction::new();
        let i0 = tx.add_input(pk_a, 300);
        tx.add_output(new_output(200, 200)); // 100 goes unaccounted for -- the fee
        tx.sign_input(i0, &sk_a);
        assert!(tx.verify());
    }

    #[test]
    fn tampered_claimed_input_amount_rejected() {
        let (sk_a, pk_a) = keypair(1);
        let mut tx = Transaction::new();
        let i0 = tx.add_input(pk_a, 200);
        tx.add_output(new_output(200, 200));
        tx.sign_input(i0, &sk_a);
        assert!(tx.verify());

        // Bumping the claimed amount after signing breaks the signature
        // (the message commits to it), independent of the balance check.
        tx.inputs[0].amount += 1;
        assert!(!tx.verify());
    }

    /// Redistributing value between two outputs keeps the *total* balanced
    /// but still has to break verification, since each output's bytes --
    /// including its individual amount -- are part of what every
    /// signature commits to, not just the sum.
    #[test]
    fn redistributing_output_amounts_breaks_signatures() {
        let (sk_a, pk_a) = keypair(1);
        let (_, pk_out_1) = keypair(201);
        let (_, pk_out_2) = keypair(202);

        let mut tx = Transaction::new();
        let i0 = tx.add_input(pk_a, 200);
        tx.add_output(Output::new(&pk_out_1, 100));
        tx.add_output(Output::new(&pk_out_2, 100));
        tx.sign_input(i0, &sk_a);
        assert!(tx.verify());

        // Same total (200), different split -- still breaks the signature.
        tx.outputs[0] = Output::new(&pk_out_1, 150);
        tx.outputs[1] = Output::new(&pk_out_2, 50);
        assert!(!tx.verify());
    }

    /// The bug this module used to have: a single shared signing message
    /// covering every input meant adding a *new* input retroactively
    /// invalidated every signature already collected. This is the direct
    /// regression test for the fix -- signer A signs, *then* a brand new
    /// input (signer B's) is added, and signer A's signature must still be
    /// intact.
    #[test]
    fn adding_a_later_input_does_not_invalidate_an_earlier_signature() {
        let (sk_a, pk_a) = keypair(1);
        let (sk_b, pk_b) = keypair(2);

        let mut tx = Transaction::new();
        tx.add_output(new_output(200, 200));

        let i0 = tx.add_input(pk_a.clone(), 100);
        assert!(tx.sign_input(i0, &sk_a));
        let message_a_before = tx.input_signing_message(i0).unwrap();

        // A second, independent input arrives and gets signed *after* A.
        let i1 = tx.add_input(pk_b, 100);
        assert!(tx.sign_input(i1, &sk_b));

        // A's signing message, and signature, are completely unaffected by
        // B's input having been added.
        assert_eq!(tx.input_signing_message(i0).unwrap(), message_a_before);
        assert!(wots::verify(
            &pk_a,
            message_a_before,
            tx.inputs[i0].signature.as_ref().unwrap()
        ));

        assert!(tx.verify());
    }

    /// Three independent parties, adding and signing their own inputs in
    /// an arbitrarily interleaved order -- not all added up front, not all
    /// signed at the end. Each only ever needs their own secret key.
    #[test]
    fn multiple_parties_interleaving_add_and_sign() {
        let (sk_a, pk_a) = keypair(1);
        let (sk_b, pk_b) = keypair(2);
        let (sk_c, pk_c) = keypair(3);

        let mut tx = Transaction::new();
        tx.add_output(new_output(200, 300)); // 3 x 100 in, 300 out, no fee

        let i_a = tx.add_input(pk_a, 100);
        assert!(tx.sign_input(i_a, &sk_a));

        let i_b = tx.add_input(pk_b, 100);
        // B signs only after C's input already exists.
        let i_c = tx.add_input(pk_c, 100);
        assert!(tx.sign_input(i_c, &sk_c));
        assert!(tx.sign_input(i_b, &sk_b));

        assert!(tx.verify());
    }

    /// The remaining ordering rule, now that inputs are independent of
    /// each other: outputs still have to be finalized before any input is
    /// signed, since every input's message covers the full output list.
    #[test]
    fn adding_an_output_after_signing_breaks_that_signature() {
        let (sk_a, pk_a) = keypair(1);
        let mut tx = Transaction::new();
        let i0 = tx.add_input(pk_a, 200);
        tx.add_output(new_output(200, 100));
        assert!(tx.sign_input(i0, &sk_a));

        // A second output shows up after A already signed.
        tx.add_output(new_output(201, 100));
        assert!(!tx.verify());
    }

    /// The recipient-first, Grin-style interactive flow: whoever is
    /// *receiving* funds generates their keypair and contributes the new
    /// output before the sender ever touches the transaction; the sender
    /// then adds their own input(s) (possibly from more than one of their
    /// own outputs, each needing its own key) and signs; finally either
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
        tx.add_output(recipient_output);

        // Sender's side: add the input(s) they're spending and sign them.
        let (secret_a, pubkey_a) = keypair(1);
        let (secret_b, pubkey_b) = keypair(2);
        let i0 = tx.add_input(pubkey_a, 100);
        let i1 = tx.add_input(pubkey_b, 100);
        tx.sign_input(i0, &secret_a);
        tx.sign_input(i1, &secret_b);

        // Either the recipient or a block validator can now check it.
        assert!(tx.verify());
    }
}
