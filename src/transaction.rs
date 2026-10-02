//! Transactions: just inputs (spent outputs, identified by their owner's
//! revealed public key, plus the amount being spent) and outputs, nothing
//! else -- no fees, no scripts.
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
//!   public key, every signature is valid over the shared message, and
//!   total input amount equals total output amount (no fee concept yet).
//! - Left to the caller: whether each claimed (pubkey, amount) input
//!   actually, currently corresponds to a real, unspent output somewhere.
//!   That's a question about a specific output set at a specific moment
//!   (i.e. block/mempool validation against a particular `pmmr`, or
//!   whatever storage a given context uses), not about the transaction by
//!   itself -- a `Transaction` can be fully internally valid while every
//!   one of its claimed inputs turns out to be fabricated, and catching
//!   that is explicitly not this module's job.
//!
//! # Building a transaction
//!
//! `Transaction` is built incrementally and mutably:
//!
//! ```ignore
//! let mut tx = Transaction::new();
//! let i0 = tx.add_input(pubkey_a, 100);
//! let i1 = tx.add_input(pubkey_b, 100);
//! tx.add_output(new_output); // worth 200
//! tx.sign_input(i0, &secret_a);
//! tx.sign_input(i1, &secret_b);
//! assert!(tx.verify());
//! ```
//!
//! Each `sign_input` call only ever needs the secret key for *that* input.
//! Different inputs can be signed by different owners who never share
//! secret keys with each other or with whoever is assembling the
//! transaction -- e.g. pass the same (partially-signed) `Transaction`
//! between parties, each calling `sign_input` for their own input before
//! passing it on, with `verify()` as the final check once every input is
//! signed.

// `main.rs` doesn't call into this module yet (it just prints "Hello
// world!"), so allow dead code here rather than suppressing warnings
// piecemeal -- this module exists to be exercised by its tests for now.
#![allow(dead_code)]

use crate::output::Output;
use crate::poseidon2::{BabyBear, hash_bytes};
use crate::wots::{self, PublicKey, SecretKey, Signature};

/// Domain separator for the transaction signing message, so it can never be
/// confused with a hash produced for some other purpose that happens to
/// reuse the same (pubkeys, amounts, outputs) byte shape.
const SIGNING_DOMAIN: &[u8] = b"transaction-v1";

/// One spent output: the owner's revealed public key, the claimed amount
/// being spent, and their signature over the transaction's signing message
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

    /// The message every input's signature must cover: a hash binding
    /// every input's revealed public key and claimed amount, and every
    /// output, together -- so nothing can be added, removed, or altered
    /// (including just the claimed amount of an input) after any input is
    /// signed without invalidating every signature already on it.
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

    /// Sign the input at `index` with `secret_key`. The caller is
    /// responsible for only ever calling this with the secret key that
    /// actually owns that input's public key -- if it doesn't,
    /// `sign_input` still succeeds mechanically (it has no way to check),
    /// but the resulting signature will simply fail `verify`. Returns
    /// `false` if `index` is out of range, or (astronomically unlikely) if
    /// the underlying WOTS signature fails to find a valid randomizer (see
    /// `wots::sign`).
    pub fn sign_input(&mut self, index: usize, secret_key: &SecretKey) -> bool {
        if index >= self.inputs.len() {
            return false;
        }
        let message = self.signing_message();
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

        // Total claimed input value must exactly equal total output value
        // -- there's no fee concept yet, so anything else means either a
        // mistake or an attempt to mint or destroy value. Accumulated in
        // u128 so realistic u64 amounts can never overflow this check.
        let input_total: u128 = self.inputs.iter().map(|i| i.amount as u128).sum();
        let output_total: u128 = self.outputs.iter().map(|o| o.amount as u128).sum();
        if input_total != output_total {
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
        // No inputs, no outputs, nothing to sign, and 0 == 0 -- trivially
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
        tx.add_output(new_output(200, 200)); // claims more than is spent
        tx.sign_input(i0, &sk_a);
        assert!(!tx.verify());
    }

    #[test]
    fn input_exceeding_output_rejected() {
        let (sk_a, pk_a) = keypair(1);
        let mut tx = Transaction::new();
        let i0 = tx.add_input(pk_a, 300);
        tx.add_output(new_output(200, 200)); // spends more than it creates
        tx.sign_input(i0, &sk_a);
        assert!(!tx.verify());
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
        // (the message commits to it) even before the balance check would
        // also now fail.
        tx.inputs[0].amount += 1;
        assert!(!tx.verify());
    }

    /// Redistributing value between two outputs keeps the *total* balanced
    /// but still has to break verification, since each output's bytes --
    /// including its individual amount -- are what the signature commits
    /// to, not just the sum.
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

    /// The actual multi-signer flow: two independent owners, neither of
    /// whom ever sees the other's secret key, each sign only their own
    /// input on a shared `Transaction` passed between them.
    #[test]
    fn multiple_independent_signers() {
        let (sk_a, pk_a) = keypair(10);
        let (sk_b, pk_b) = keypair(20);

        let mut tx = Transaction::new();
        let i_a = tx.add_input(pk_a, 100);
        let i_b = tx.add_input(pk_b, 100);
        tx.add_output(new_output(200, 200));

        // Signer A receives `tx`, signs only their own input, passes it on.
        assert!(tx.sign_input(i_a, &sk_a));
        // Signer B receives it next, signs only their own input.
        assert!(tx.sign_input(i_b, &sk_b));

        assert!(tx.verify());
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
