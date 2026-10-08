//! Files for trying out spending policies from the command line
//! (`docs/CONTRACTS.md`): policies written as text, and transactions
//! passed between their signers as files, like slates. Deliberately thin:
//! no channel or routing logic, just enough to exercise the primitives --
//! threshold keys, timelocks, hash locks, key trees and REBIND.
//!
//! A policy file holds one branch per line (`#` starts a comment):
//!
//! ```text
//! branch threshold=2 keys=<key id>,<key id>,<key id> after_height=100 after_age=5 hashlock=<image> rebind=3
//! ```
//!
//! `threshold` and `keys` are required; the rest are optional. Key ids
//! come from `key`, hash lock images from `hashlock`, both as hex.
//!
//! A `salt <hex>` line adds a branch whose only key is the salt -- a key
//! nobody holds, so it never spends -- giving the policy a different lock:
//! how to pay one policy more than once in the same amount (a duplicate of
//! a live output is refused).

#![allow(dead_code)]

use std::path::Path;

use crate::output::format_amount;
use crate::policy::{Branch, Policy};
use crate::slate::{hex, unhex};
use crate::transaction::{Spend, Transaction};

/// 32 bytes from 64 hex characters.
pub fn parse_hash(text: &str) -> Result<[u8; 32], String> {
    unhex(text)
        .and_then(|b| b.try_into().ok())
        .ok_or_else(|| format!("not 32 bytes of hex: {text}"))
}

/// One branch line's `key=value` fields.
fn parse_branch(fields: &[&str]) -> Result<Branch, String> {
    let mut branch = Branch { threshold: 0, keys: Vec::new(), after_height: 0, after_age: 0, hashlock: None, rebind: None };
    let number = |v: &str| v.parse::<u32>().map_err(|_| format!("not a number: {v}"));
    for field in fields {
        let (key, value) = field.split_once('=').ok_or_else(|| format!("expected key=value: {field}"))?;
        match key {
            "threshold" => branch.threshold = u8::try_from(number(value)?).map_err(|_| format!("threshold too large: {value}"))?,
            "keys" => branch.keys = value.split(',').map(parse_hash).collect::<Result<_, _>>()?,
            "after_height" => branch.after_height = number(value)?,
            "after_age" => branch.after_age = number(value)?,
            "hashlock" => branch.hashlock = Some(parse_hash(value)?),
            "rebind" => branch.rebind = Some(number(value)?),
            _ => return Err(format!("unknown field: {key}")),
        }
    }
    if !branch.is_valid() {
        return Err("a branch needs 1 <= threshold <= keys <= 12, and heights, ages and states below 2^30".into());
    }
    Ok(branch)
}

/// Parse a policy file's text.
pub fn parse_policy(text: &str) -> Result<Policy, String> {
    let mut branches = Vec::new();
    for (n, line) in text.lines().enumerate() {
        let line = line.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        let words: Vec<&str> = line.split_whitespace().collect();
        match words.split_first() {
            Some((&"branch", fields)) => branches.push(parse_branch(fields).map_err(|e| format!("line {}: {e}", n + 1))?),
            Some((&"salt", [salt])) => {
                let salt = parse_hash(salt).map_err(|e| format!("line {}: {e}", n + 1))?;
                branches.push(parse_branch(&["threshold=1", &format!("keys={}", hex(&salt))]).map_err(|e| format!("line {}: salt: {e}", n + 1))?);
            }
            _ => return Err(format!("line {}: expected `branch ...` or `salt <hex>`", n + 1)),
        }
    }
    let policy = Policy { branches };
    if !policy.is_valid() {
        return Err("a policy needs 1 to 256 branches".into());
    }
    Ok(policy)
}

pub fn read_policy(path: &Path) -> Result<Policy, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("reading {}: {e}", path.display()))?;
    parse_policy(&text).map_err(|e| format!("{}: {e}", path.display()))
}

const BEGIN: &str = "-----BEGIN TRANSACTION-----";
const END: &str = "-----END TRANSACTION-----";

/// A transaction as a file: a readable summary (`describe`), then the
/// encoding in hex.
pub fn write_transaction(tx: &Transaction, path: &Path) -> Result<(), String> {
    let mut out = format!("{BEGIN}\n{}\n\n", describe(tx).trim_end());
    for line in hex(&tx.to_bytes()).as_bytes().chunks(64) {
        out.push_str(std::str::from_utf8(line).unwrap());
        out.push('\n');
    }
    out.push_str(END);
    out.push('\n');
    std::fs::write(path, out).map_err(|e| format!("writing {}: {e}", path.display()))
}

/// Read `write_transaction`'s file (the summary is for people; the hex is
/// what counts).
pub fn read_transaction(path: &Path) -> Result<Transaction, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("reading {}: {e}", path.display()))?;
    let body = text
        .trim()
        .strip_prefix(BEGIN)
        .and_then(|t| t.strip_suffix(END))
        .ok_or_else(|| format!("{}: not a transaction file", path.display()))?;
    let data: String = body.rsplit_once("\n\n").map_or(body, |(_, d)| d).split_whitespace().collect();
    unhex(&data)
        .and_then(|bytes| Transaction::from_bytes(&bytes))
        .ok_or_else(|| format!("{}: malformed transaction", path.display()))
}

/// A short commitment, for display.
fn short(hash: &[u8; 32]) -> String {
    hex(&hash[..8])
}

/// A readable summary: each input (what it spends, and how far its
/// signing has got), each output, the fee, and whether it verifies.
pub fn describe(tx: &Transaction) -> String {
    let mut out = String::new();
    for input in &tx.inputs {
        let c = short(&input.commitment());
        match &input.spend {
            Spend::Key { proof, signature, .. } => {
                let tree = if proof.path.is_empty() { String::new() } else { format!(", key tree leaf {}", proof.index) };
                out += &format!("input {c}: {} by key{tree} -- {}\n", format_amount(input.amount), if signature.is_some() { "signed" } else { "unsigned" });
            }
            Spend::Policy(p) => {
                let b = &p.branch;
                let mut conditions = vec![format!("{} of {} keys", b.threshold, b.keys.len())];
                if b.after_height > 0 {
                    conditions.push(format!("after height {}", b.after_height));
                }
                if b.after_age > 0 {
                    conditions.push(format!("after age {}", b.after_age));
                }
                if b.hashlock.is_some() {
                    conditions.push(format!("hash lock ({})", if p.preimage.is_some() { "preimage given" } else { "no preimage" }));
                }
                if let Some(s) = b.rebind {
                    conditions.push(format!("REBIND above state {s}, declaring {}", p.state));
                }
                let signed = p.signers.iter().filter(|s| s.signature.is_some()).count();
                out += &format!(
                    "input {c}: {} by policy branch {} ({}) -- {signed}/{} signed\n",
                    format_amount(input.amount),
                    p.index,
                    conditions.join(", "),
                    b.threshold
                );
            }
        }
    }
    for output in &tx.outputs {
        out += &format!("output {}: {}\n", short(&output.commitment()), format_amount(output.amount));
    }
    match tx.fee() {
        Some(fee) => out += &format!("fee: {}\n", format_amount(fee)),
        None => out += "fee: none (the outputs exceed the inputs)\n",
    }
    out += if tx.verify() { "status: fully signed (timelocks are checked when it's mined)\n" } else { "status: not yet fully signed\n" };
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(k: u8) -> String {
        hex(&crate::poseidon2::digest_to_bytes(crate::wots::keygen(&[k; 32]).1.hash()))
    }

    #[test]
    fn policies_parse_from_text() {
        let image = hex(&crate::policy::hashlock(&crate::poseidon2::digest_to_bytes([crate::poseidon2::BabyBear::new(3); 8])).unwrap());
        let text = format!(
            "# a refund, a claim, and an update\nbranch threshold=1 keys={} after_height=100\n\nbranch threshold=1 keys={} hashlock={image}  # claim\nbranch threshold=2 keys={},{} rebind=4 after_age=5\n",
            key(1),
            key(2),
            key(1),
            key(2)
        );
        let policy = parse_policy(&text).unwrap();
        assert_eq!(policy.branches.len(), 3);
        assert_eq!(policy.branches[0].after_height, 100);
        assert!(policy.branches[1].hashlock.is_some());
        assert_eq!((policy.branches[2].threshold, policy.branches[2].rebind, policy.branches[2].after_age), (2, Some(4), 5));
        // A salt: one more (unusable) branch, and another lock.
        let salted = parse_policy(&format!("{text}salt {}\n", key(9))).unwrap();
        assert_eq!(salted.branches.len(), 4);
        assert_ne!(salted.lock(), policy.lock());
        for bad in ["", "branch keys=00", "salt", "salt zz", &format!("branch threshold=2 keys={}", key(1)), "leaf threshold=1", &format!("branch threshold=1 keys={} colour=red", key(1))] {
            assert!(parse_policy(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn transaction_files_round_trip() {
        let dir = std::env::temp_dir().join(format!("contract-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("t.tx");
        let (_, pk) = crate::wots::keygen(&[5; 32]);
        let mut tx = Transaction::new();
        tx.add_input(&pk, 300).unwrap();
        tx.add_output(crate::output::Output::new(&pk, 250)).unwrap();
        write_transaction(&tx, &path).unwrap();
        let back = read_transaction(&path).unwrap();
        assert_eq!(back.to_bytes(), tx.to_bytes());
        assert!(std::fs::read_to_string(&path).unwrap().contains("fee: 0.000000050"));
        let _ = std::fs::remove_dir_all(&dir);
    }
}
