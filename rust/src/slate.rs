//! Slates: a transaction under construction, passed between sender and
//! receiver (Grin's model, adapted).
//!
//! ```text
//! sender                          receiver
//! ------                          --------
//! send:     choose inputs, change,
//!           amount, fee  ── S1 ──▶ receive:  add one output paying
//!                                            `amount` to a fresh key
//! finalize: check S2, sign ◀─ S2 ──
//!           every input, submit
//! ```
//!
//! Why this shape fits this chain:
//!
//! - **The receiver makes their own output.** Amounts are hidden on chain
//!   (an output is `H(pubkey_hash ‖ amount)`), so a payment can only be
//!   found by someone who knows the exact output. Here the receiver
//!   creates it, so they always know it -- no invoices, no scanning.
//! - **Only the sender signs, and only at the end.** Every signature
//!   covers the whole transaction (`Transaction::signing_message`), so it
//!   can't happen until the outputs are final; and outputs need no
//!   signature, so the receiver signs nothing.
//! - **Signing is once.** Keys are one-time (`wots`): the sender's wallet
//!   must sign a given slate at most once and keep the result -- if
//!   finalize is run again, reuse it, never sign a different transaction.
//!   (That's the wallet's bookkeeping; `finalize` here just signs.)
//!
//! `finalize` signs whatever it's given, so the sender must first check the
//! returned slate against the one it sent (`check_response`): same id,
//! inputs, change, amount and fee, and exactly one new output, of exactly
//! the amount. A receiver can't redirect or inflate anything.
//!
//! Slates travel as files (`write_file` / `read_file`) in an armored text
//! form (`to_armored`): a readable summary, then the slate itself in hex.
//! The summary is checked against the slate on reading.

#![allow(dead_code)]

use std::path::Path;

use crate::output::{Output, format_amount};
use crate::prover::is_canonical;
use crate::transaction::Transaction;
use crate::wots::{self, PublicKey, SecretKey};

const MAGIC: &[u8; 4] = b"TSLT";
const VERSION: u16 = 2;
const BEGIN: &str = "-----BEGIN TABERNACLE SLATE-----";
const END: &str = "-----END TABERNACLE SLATE-----";

/// How far the exchange has got.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Stage {
    /// From the sender: inputs, change, amount, fee.
    Send = 1,
    /// Back from the receiver: plus the receiver's output.
    Receive = 2,
}

impl Stage {
    fn name(self) -> &'static str {
        match self {
            Stage::Send => "send",
            Stage::Receive => "receive",
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// Not a slate (bad encoding, version, or armor).
    Malformed(&'static str),
    /// The slate is at the wrong stage for this step.
    WrongStage(Stage),
    /// Inputs don't cover outputs, amount and fee exactly (or overflow).
    Unbalanced,
    /// The receiver's output doesn't pay exactly the slate's amount.
    AmountMismatch,
    /// The returned slate isn't the one we sent plus one output.
    Tampered(&'static str),
    /// We have no secret key for one of the inputs.
    UnknownKey,
    /// Signing failed (a WOTS randomizer wasn't found; astronomically rare).
    SigningFailed,
    Io(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::Malformed(what) => write!(f, "not a valid slate: {what}"),
            Error::WrongStage(stage) => write!(f, "the slate is at the wrong stage ({})", stage.name()),
            Error::Unbalanced => write!(f, "the slate's inputs don't exactly cover its outputs, amount and fee"),
            Error::AmountMismatch => write!(f, "the receiver's output doesn't pay exactly the slate's amount"),
            Error::Tampered(what) => write!(f, "the returned slate doesn't match the one sent: {what}"),
            Error::UnknownKey => write!(f, "no secret key for one of the slate's inputs"),
            Error::SigningFailed => write!(f, "signing failed"),
            Error::Io(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Slate {
    /// Random, chosen by the sender; ties the response to the request.
    pub id: [u8; 16],
    pub stage: Stage,
    /// What the receiver gets.
    pub amount: u64,
    /// What the miner gets (inputs minus outputs).
    pub fee: u64,
    /// The sender's spends: each output's owner key and amount (signed
    /// only at finalize).
    pub inputs: Vec<(PublicKey, u64)>,
    /// The sender's change outputs, then (from `Receive` on) the
    /// receiver's output, last.
    pub outputs: Vec<Output>,
}

fn sum(values: impl IntoIterator<Item = u64>) -> Option<u64> {
    values.into_iter().try_fold(0u64, |a, v| a.checked_add(v))
}

pub(crate) fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

pub(crate) fn unhex(text: &str) -> Option<Vec<u8>> {
    if !text.len().is_multiple_of(2) || !text.is_ascii() {
        return None;
    }
    (0..text.len() / 2).map(|i| u8::from_str_radix(&text[2 * i..2 * i + 2], 16).ok()).collect()
}

impl Slate {
    /// Start a payment of `amount` (plus `fee` to the miner) from
    /// `inputs`, returning the remainder in `change`. Inputs must exactly
    /// cover amount, fee and change.
    pub fn send(amount: u64, fee: u64, inputs: Vec<(PublicKey, u64)>, change: Vec<Output>) -> Result<Slate> {
        let mut id = [0u8; 16];
        id.copy_from_slice(&crate::keychain::random_bytes()[..16]);
        let slate = Slate {
            id,
            stage: Stage::Send,
            amount,
            fee,
            inputs,
            outputs: change,
        };
        slate.validate()?;
        Ok(slate)
    }

    /// The receiver's step: add `output`, which must pay exactly the
    /// slate's amount, returning the slate to send back.
    pub fn receive(&self, output: Output) -> Result<Slate> {
        if self.stage != Stage::Send {
            return Err(Error::WrongStage(self.stage));
        }
        self.validate()?;
        if output.amount != self.amount {
            return Err(Error::AmountMismatch);
        }
        let mut response = self.clone();
        response.stage = Stage::Receive;
        response.outputs.push(output);
        response.validate()?;
        Ok(response)
    }

    /// The sender's check of the receiver's `response` against this slate
    /// (the one it sent): returns the receiver's output if `response` is
    /// exactly this slate plus that one output.
    pub fn check_response(&self, response: &Slate) -> Result<Output> {
        if self.stage != Stage::Send {
            return Err(Error::WrongStage(self.stage));
        }
        if response.stage != Stage::Receive {
            return Err(Error::WrongStage(response.stage));
        }
        if response.id != self.id {
            return Err(Error::Tampered("a different slate id"));
        }
        if response.amount != self.amount || response.fee != self.fee {
            return Err(Error::Tampered("a different amount or fee"));
        }
        if response.inputs != self.inputs {
            return Err(Error::Tampered("different inputs"));
        }
        let (theirs, ours) = response.outputs.split_last().ok_or(Error::Tampered("no receiver output"))?;
        if ours != self.outputs.as_slice() {
            return Err(Error::Tampered("different change outputs"));
        }
        if theirs.amount != self.amount {
            return Err(Error::AmountMismatch);
        }
        response.validate()?;
        Ok(*theirs)
    }

    /// The (unsigned) transaction a `Receive`-stage slate describes.
    pub fn transaction(&self) -> Result<Transaction> {
        if self.stage != Stage::Receive {
            return Err(Error::WrongStage(self.stage));
        }
        self.validate()?;
        let mut tx = Transaction::new();
        for (pubkey, amount) in &self.inputs {
            tx.add_input(pubkey, *amount).map_err(|_| Error::Malformed("transaction"))?;
        }
        for output in &self.outputs {
            tx.add_output(*output).map_err(|_| Error::Malformed("transaction"))?;
        }
        Ok(tx)
    }

    /// The sender's last step: the transaction, with every input signed
    /// by the key `secret_key` returns for it. Check the slate first
    /// (`check_response`) -- this signs whatever it's given -- and sign a
    /// slate only once (see the module docs).
    pub fn finalize(&self, secret_key: impl Fn(&PublicKey) -> Option<SecretKey>) -> Result<Transaction> {
        let mut tx = self.transaction()?;
        for (pubkey, _) in &self.inputs {
            let sk = secret_key(pubkey).ok_or(Error::UnknownKey)?;
            if !tx.sign_input(pubkey, &sk) {
                return Err(Error::SigningFailed);
            }
        }
        if !tx.verify() {
            return Err(Error::SigningFailed);
        }
        Ok(tx)
    }

    /// Structural checks every slate must pass: inputs present and
    /// distinct, outputs well-formed, amounts balanced.
    fn validate(&self) -> Result<()> {
        if self.inputs.is_empty() {
            return Err(Error::Malformed("no inputs"));
        }
        if self.amount == 0 {
            return Err(Error::Malformed("zero amount"));
        }
        let mut keys: Vec<Vec<u8>> = self.inputs.iter().map(|(pk, _)| pk.to_bytes()).collect();
        keys.sort();
        if keys.windows(2).any(|w| w[0] == w[1]) {
            return Err(Error::Malformed("an input appears twice"));
        }
        if !self.outputs.iter().all(|o| is_canonical(&o.lock)) {
            return Err(Error::Malformed("an output's key hash isn't canonical"));
        }
        let spent = sum(self.inputs.iter().map(|(_, a)| *a)).ok_or(Error::Unbalanced)?;
        let created = sum(self.outputs.iter().map(|o| o.amount)).ok_or(Error::Unbalanced)?;
        // At `Send`, the receiver's output isn't there yet: it's `amount`.
        let pending = if self.stage == Stage::Send { self.amount } else { 0 };
        let needed = sum([created, pending, self.fee]).ok_or(Error::Unbalanced)?;
        if spent != needed {
            return Err(Error::Unbalanced);
        }
        Ok(())
    }

    // ---- encoding -------------------------------------------------------

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = MAGIC.to_vec();
        out.extend(VERSION.to_le_bytes());
        out.push(self.stage as u8);
        out.extend(self.id);
        out.extend(self.amount.to_le_bytes());
        out.extend(self.fee.to_le_bytes());
        out.extend((self.inputs.len() as u16).to_le_bytes());
        for (pubkey, amount) in &self.inputs {
            out.extend(pubkey.to_bytes());
            out.extend(amount.to_le_bytes());
        }
        out.extend((self.outputs.len() as u16).to_le_bytes());
        for output in &self.outputs {
            out.extend(output.to_bytes());
        }
        out
    }

    /// Decode strictly (nothing left over), and check the slate is
    /// well-formed.
    pub fn from_bytes(bytes: &[u8]) -> Result<Slate> {
        let mut r = bytes;
        let mut take = |n: usize| -> Result<&[u8]> {
            let (head, tail) = (r.get(..n).ok_or(Error::Malformed("truncated"))?, &r[n..]);
            r = tail;
            Ok(head)
        };
        if take(4)? != MAGIC {
            return Err(Error::Malformed("not a slate"));
        }
        if u16::from_le_bytes(take(2)?.try_into().unwrap()) != VERSION {
            return Err(Error::Malformed("unsupported version"));
        }
        let stage = match take(1)?[0] {
            1 => Stage::Send,
            2 => Stage::Receive,
            _ => return Err(Error::Malformed("unknown stage")),
        };
        let id: [u8; 16] = take(16)?.try_into().unwrap();
        let amount = u64::from_le_bytes(take(8)?.try_into().unwrap());
        let fee = u64::from_le_bytes(take(8)?.try_into().unwrap());
        let count = u16::from_le_bytes(take(2)?.try_into().unwrap());
        let mut inputs = Vec::new();
        for _ in 0..count {
            let pubkey = PublicKey::from_bytes(take(wots::PUBLIC_KEY_LEN)?).ok_or(Error::Malformed("public key"))?;
            inputs.push((pubkey, u64::from_le_bytes(take(8)?.try_into().unwrap())));
        }
        let count = u16::from_le_bytes(take(2)?.try_into().unwrap());
        let mut outputs = Vec::new();
        for _ in 0..count {
            outputs.push(Output::from_bytes(take(crate::output::OUTPUT_LEN)?).ok_or(Error::Malformed("output"))?);
        }
        if !r.is_empty() {
            return Err(Error::Malformed("trailing bytes"));
        }
        let slate = Slate {
            id,
            stage,
            amount,
            fee,
            inputs,
            outputs,
        };
        slate.validate()?;
        Ok(slate)
    }

    /// The text form: a summary a person can read, then the slate in hex.
    pub fn to_armored(&self) -> String {
        let mut out = format!(
            "{BEGIN}\nstage: {}\nid: {}\namount: {}\nfee: {}\n\n",
            self.stage.name(),
            hex(&self.id),
            format_amount(self.amount),
            format_amount(self.fee)
        );
        for line in hex(&self.to_bytes()).as_bytes().chunks(64) {
            out.push_str(std::str::from_utf8(line).unwrap());
            out.push('\n');
        }
        out.push_str(END);
        out.push('\n');
        out
    }

    /// Parse `to_armored`'s form; the summary must agree with the slate.
    pub fn from_armored(text: &str) -> Result<Slate> {
        let body = text
            .trim()
            .strip_prefix(BEGIN)
            .and_then(|t| t.strip_suffix(END))
            .ok_or(Error::Malformed("missing armor"))?;
        let (summary, data) = body.trim().split_once("\n\n").ok_or(Error::Malformed("missing summary"))?;
        let data: String = data.split_whitespace().collect();
        let slate = Slate::from_bytes(&unhex(&data).ok_or(Error::Malformed("bad hex"))?)?;
        let expected = format!(
            "stage: {}\nid: {}\namount: {}\nfee: {}",
            slate.stage.name(),
            hex(&slate.id),
            format_amount(slate.amount),
            format_amount(slate.fee)
        );
        if summary.trim() != expected {
            return Err(Error::Malformed("the summary doesn't match the slate"));
        }
        Ok(slate)
    }

    pub fn write_file(&self, path: &Path) -> Result<()> {
        std::fs::write(path, self.to_armored()).map_err(|e| Error::Io(format!("writing {}: {e}", path.display())))
    }

    pub fn read_file(path: &Path) -> Result<Slate> {
        let text = std::fs::read_to_string(path).map_err(|e| Error::Io(format!("reading {}: {e}", path.display())))?;
        Slate::from_armored(&text)
    }

    /// The id as hex, for display and file names.
    pub fn id_hex(&self) -> String {
        hex(&self.id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keychain::{KeyId, Keychain};

    /// Alice has outputs of 600 and 500 (keys 0/0 and 0/1); she pays Bob
    /// 900 with a fee of 10, change 190 to her key 0/2. Bob receives to
    /// his key 0/0.
    fn alice() -> Keychain {
        Keychain::test("slate alice")
    }

    fn bob() -> Keychain {
        Keychain::test("slate bob")
    }

    fn s1() -> Slate {
        let a = alice();
        let inputs = vec![(a.public_key(KeyId::new(0, 0)), 600), (a.public_key(KeyId::new(0, 1)), 500)];
        let change = vec![a.output(KeyId::new(0, 2), 190)];
        Slate::send(900, 10, inputs, change).unwrap()
    }

    /// Alice's signer: her keys for her inputs, nothing else.
    fn alice_signer(pubkey: &PublicKey) -> Option<SecretKey> {
        let a = alice();
        (0..2).map(|i| KeyId::new(0, i)).find(|&id| &a.public_key(id) == pubkey).map(|id| a.secret_key(id))
    }

    #[test]
    fn a_payment_goes_send_receive_finalize() {
        let s1 = s1();
        let bob_output = bob().output(KeyId::new(0, 0), 900);
        let s2 = s1.receive(bob_output).unwrap();
        assert_eq!(s1.check_response(&s2).unwrap(), bob_output);
        let tx = s2.finalize(alice_signer).unwrap();
        assert!(tx.verify());
        assert_eq!(tx.fee(), Some(10));
        assert_eq!(tx.inputs.len(), 2);
        assert!(tx.outputs.contains(&bob_output));
        // Bob's output is the commitment he can now watch for.
        assert!(tx.outputs.iter().any(|o| o.commitment() == bob_output.commitment()));
    }

    #[test]
    fn the_sender_must_balance() {
        let a = alice();
        let inputs = vec![(a.public_key(KeyId::new(0, 0)), 600)];
        assert_eq!(Slate::send(500, 10, inputs.clone(), vec![a.output(KeyId::new(0, 2), 91)]).err(), Some(Error::Unbalanced));
        assert_eq!(Slate::send(0, 0, inputs.clone(), vec![a.output(KeyId::new(0, 2), 600)]).err(), Some(Error::Malformed("zero amount")));
        assert_eq!(Slate::send(1, 0, vec![], vec![]).err(), Some(Error::Malformed("no inputs")));
        let twice = vec![inputs[0].clone(), inputs[0].clone()];
        assert_eq!(Slate::send(1100, 100, twice, vec![]).err(), Some(Error::Malformed("an input appears twice")));
        assert!(Slate::send(590, 10, inputs, vec![]).is_ok());
    }

    #[test]
    fn the_receiver_must_take_exactly_the_amount() {
        let s1 = s1();
        assert_eq!(s1.receive(bob().output(KeyId::new(0, 0), 901)).err(), Some(Error::AmountMismatch));
        let s2 = s1.receive(bob().output(KeyId::new(0, 0), 900)).unwrap();
        assert_eq!(s2.receive(bob().output(KeyId::new(0, 1), 900)).err(), Some(Error::WrongStage(Stage::Receive)));
    }

    /// Every way a receiver might alter the slate is caught before Alice
    /// signs.
    #[test]
    fn a_tampered_response_is_refused() {
        let s1 = s1();
        let honest = s1.receive(bob().output(KeyId::new(0, 0), 900)).unwrap();

        let mut other_id = honest.clone();
        other_id.id[0] ^= 1;
        assert_eq!(s1.check_response(&other_id).err(), Some(Error::Tampered("a different slate id")));

        // Redirecting Alice's change to Bob (keeping the balance).
        let mut stolen_change = honest.clone();
        stolen_change.outputs[0] = bob().output(KeyId::new(0, 5), 190);
        assert_eq!(s1.check_response(&stolen_change).err(), Some(Error::Tampered("different change outputs")));

        // A bigger payment, smaller change.
        let mut more = honest.clone();
        more.amount = 1000;
        more.outputs = vec![alice().output(KeyId::new(0, 2), 90), bob().output(KeyId::new(0, 0), 1000)];
        assert_eq!(s1.check_response(&more).err(), Some(Error::Tampered("a different amount or fee")));

        // A second receiver output squeezed out of the fee.
        let mut extra = honest.clone();
        extra.fee = 0;
        extra.outputs.insert(1, bob().output(KeyId::new(0, 6), 10));
        assert_eq!(s1.check_response(&extra).err(), Some(Error::Tampered("a different amount or fee")));

        // An input swapped for one of Bob's (so Alice would sign it).
        let mut swapped = honest.clone();
        swapped.inputs[1] = (bob().public_key(KeyId::new(0, 9)), 500);
        assert_eq!(s1.check_response(&swapped).err(), Some(Error::Tampered("different inputs")));

        // The original, unanswered.
        assert_eq!(s1.check_response(&s1).err(), Some(Error::WrongStage(Stage::Send)));
    }

    #[test]
    fn finalizing_needs_every_key_and_a_received_slate() {
        let s1 = s1();
        assert_eq!(s1.finalize(alice_signer).err(), Some(Error::WrongStage(Stage::Send)));
        let s2 = s1.receive(bob().output(KeyId::new(0, 0), 900)).unwrap();
        assert_eq!(s2.finalize(|_| None).err(), Some(Error::UnknownKey));
        // The wrong key "signs" but the result doesn't verify.
        assert_eq!(s2.finalize(|_| Some(bob().secret_key(KeyId::new(0, 0)))).err(), Some(Error::SigningFailed));
    }

    #[test]
    fn slates_round_trip_through_files_and_reject_garbage() {
        let s1 = s1();
        let s2 = s1.receive(bob().output(KeyId::new(0, 0), 900)).unwrap();
        for slate in [&s1, &s2] {
            assert_eq!(&Slate::from_bytes(&slate.to_bytes()).unwrap(), slate);
            assert_eq!(&Slate::from_armored(&slate.to_armored()).unwrap(), slate);
        }
        let text = s1.to_armored();
        assert!(text.starts_with(BEGIN) && text.contains("amount: 0.000000900") && text.contains("stage: send"));

        // A doctored summary, truncated data, trailing data, no armor.
        let doctored = text.replace("amount: 0.000000900", "amount: 9.000000000");
        assert_eq!(Slate::from_armored(&doctored).err(), Some(Error::Malformed("the summary doesn't match the slate")));
        let bytes = s1.to_bytes();
        assert!(Slate::from_bytes(&bytes[..bytes.len() - 1]).is_err());
        assert_eq!(Slate::from_bytes(&[&bytes[..], &[0]].concat()).err(), Some(Error::Malformed("trailing bytes")));
        assert!(Slate::from_armored("hello").is_err());

        let dir = std::env::temp_dir().join(format!("slate-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join(format!("{}.s1.slate", s1.id_hex()));
        s1.write_file(&path).unwrap();
        assert_eq!(Slate::read_file(&path).unwrap(), s1);
        let _ = std::fs::remove_dir_all(&dir);
    }
}
