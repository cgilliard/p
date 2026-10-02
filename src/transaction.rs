//! Transactions: just inputs (spent outputs, identified by their owner's
//! revealed public key) and outputs, nothing else -- no amounts, no fees,
//! no scripts. `Output` carries no value field yet (see `output.rs`), so
//! there's nothing to balance between inputs and outputs; this is a pure
//! ownership-transfer model for now.
//!
//! This module has **no dependency on `pmmr` or any other output-storage
//! scheme whatsoever** -- deliberately so. An input is identified purely by
//! the public key of the output it spends (since `Output::from_pubkey`
//! already determines that output, there's nothing else to reference), not
//! by a position or an inclusion proof. That makes `Transaction` a small,
//! self-contained, reusable primitive: building, signing, and checking a
//! transaction's own internal correctness never needs to know anything
//! about where or how outputs are actually indexed, so this same type can
//! be used wherever a transaction needs handling -- a mempool, a wallet,
//! a test, block validation -- without dragging any of those contexts'
//! specifics in. Whether a given output actually, currently exists and is
//! unspent against some specific chain state is a question for whichever
//! of those contexts cares, answered separately with whatever
//! output-lookup mechanism *it* uses -- not something this module does or
//! could do.
//!
//! # Building a transaction
//!
//! `Transaction` is built incrementally and mutably:
//!
//! ```ignore
//! let mut tx = Transaction::new();
//! let i0 = tx.add_input(pubkey_a);
//! let i1 = tx.add_input(pubkey_b);
//! tx.add_output(new_output);
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
/// reuse the same (pubkeys, outputs) byte shape.
const SIGNING_DOMAIN: &[u8] = b"transaction-v1";

/// One spent output: the owner's revealed public key, and their signature
/// over the transaction's signing message once they've provided it.
#[derive(Clone, Debug)]
pub struct Input {
    pub pubkey: PublicKey,
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

    /// Add an input spending the output owned by `pubkey`. Unsigned until
    /// `sign_input` is called for the returned index.
    pub fn add_input(&mut self, pubkey: PublicKey) -> usize {
        self.inputs.push(Input {
            pubkey,
            signature: None,
        });
        self.inputs.len() - 1
    }

    pub fn add_output(&mut self, output: Output) {
        self.outputs.push(output);
    }

    /// The message every input's signature must cover: a hash binding
    /// every input's revealed public key and every output together, so
    /// nothing can be added, removed, or altered after any input is signed
    /// without invalidating every signature already on it.
    pub fn signing_message(&self) -> [BabyBear; 8] {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(SIGNING_DOMAIN);
        for input in &self.inputs {
            bytes.extend_from_slice(&input.pubkey.to_bytes());
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

    /// Verify this transaction is internally sound and fully authorized:
    /// every input is signed, no two inputs claim the same public key, and
    /// every signature is valid over the shared message. This is the
    /// entire check -- see the module docs for why it deliberately goes no
    /// further than this.
    pub fn verify(&self) -> bool {
        for i in 0..self.inputs.len() {
            for j in (i + 1)..self.inputs.len() {
                if self.inputs[i].pubkey == self.inputs[j].pubkey {
                    return false;
                }
            }
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

    fn new_output(byte: u8) -> Output {
        let (_, pk) = keypair(byte);
        Output::from_pubkey(&pk)
    }

    #[test]
    fn valid_transaction_verifies() {
        let (sk_a, pk_a) = keypair(1);
        let (sk_b, pk_b) = keypair(2);

        let mut tx = Transaction::new();
        let i0 = tx.add_input(pk_a);
        let i1 = tx.add_input(pk_b);
        tx.add_output(new_output(200));

        assert!(tx.sign_input(i0, &sk_a));
        assert!(tx.sign_input(i1, &sk_b));
        assert!(tx.verify());
    }

    #[test]
    fn unsigned_input_rejected() {
        let (_, pk_a) = keypair(1);
        let (sk_b, pk_b) = keypair(2);

        let mut tx = Transaction::new();
        tx.add_input(pk_a);
        let i1 = tx.add_input(pk_b);
        tx.add_output(new_output(200));

        // Only input 1 gets signed; input 0 is left unsigned.
        assert!(tx.sign_input(i1, &sk_b));
        assert!(!tx.verify());
    }

    #[test]
    fn tampered_output_rejected() {
        let (sk_a, pk_a) = keypair(1);

        let mut tx = Transaction::new();
        let i0 = tx.add_input(pk_a);
        tx.add_output(new_output(200));
        assert!(tx.sign_input(i0, &sk_a));
        assert!(tx.verify());

        // Swapping in a different output after signing must break the
        // signature, since the signing message commits to the exact
        // output bytes.
        tx.outputs[0] = new_output(201);
        assert!(!tx.verify());
    }

    #[test]
    fn tampered_signature_rejected() {
        let (sk_a, pk_a) = keypair(1);

        let mut tx = Transaction::new();
        let i0 = tx.add_input(pk_a);
        tx.add_output(new_output(200));
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
        let i0 = tx.add_input(pk_a);
        tx.add_output(new_output(200));

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
        let i0 = tx.add_input(pk_a.clone());
        let i1 = tx.add_input(pk_a);
        tx.add_output(new_output(200));

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
        // No inputs, no outputs, nothing to sign -- trivially valid on its
        // own. Whether an empty transaction makes sense is a question for
        // whatever's constructing one, not this module.
        let tx = Transaction::new();
        assert!(tx.verify());
    }

    /// The actual multi-signer flow: two independent owners, neither of
    /// whom ever sees the other's secret key, each sign only their own
    /// input on a shared `Transaction` passed between them.
    #[test]
    fn multiple_independent_signers() {
        let (sk_a, pk_a) = keypair(10);
        let (sk_b, pk_b) = keypair(20);

        let mut tx = Transaction::new();
        let i_a = tx.add_input(pk_a);
        let i_b = tx.add_input(pk_b);
        tx.add_output(new_output(200));

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
        // Recipient's side: generate a keypair, hand only the resulting
        // `Output` to the sender. No signature, no secret key, leaves
        // their hands at all.
        let (_recipient_secret, recipient_pubkey) = keypair(100);
        let recipient_output = Output::from_pubkey(&recipient_pubkey);

        let mut tx = Transaction::new();
        tx.add_output(recipient_output);

        // Sender's side: add the input(s) they're spending and sign them.
        let (secret_a, pubkey_a) = keypair(1);
        let (secret_b, pubkey_b) = keypair(2);
        let i0 = tx.add_input(pubkey_a);
        let i1 = tx.add_input(pubkey_b);
        tx.sign_input(i0, &secret_a);
        tx.sign_input(i1, &secret_b);

        // Either the recipient or a block validator can now check it.
        assert!(tx.verify());
    }
}
