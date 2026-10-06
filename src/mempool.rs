//! The mempool: transactions waiting to be mined.
//!
//! A first, minimal version (`docs/TRANSACTION_TODO.md`, phase 6): it holds
//! transactions this node accepted -- for now, ones its own wallet
//! finalized -- until they're mined, and hands them to the block template.
//! Relaying them to peers comes later (phase 7).
//!
//! Admission only lets in what a block could actually include
//! (`admit`): fully signed; inputs unspent on chain and not already
//! claimed by another pool transaction (first seen wins -- no replacement,
//! which one-time keys make unsafe anyway); outputs that don't already
//! exist; and small enough for one chunk of a tree-proven block. Whenever
//! the chain changes the whole pool is re-checked (`revalidate`), which
//! drops transactions that were mined, or that conflict with what was.

#![allow(dead_code)]

use std::collections::HashSet;

use crate::output::Output;
use crate::prover::CHUNK_SHAPE;
use crate::transaction::Transaction;
use crate::wallet::ChainView;

/// The most transactions the pool holds.
pub const MAX_TRANSACTIONS: usize = 1000;

#[derive(Debug, PartialEq, Eq)]
pub enum Rejection {
    AlreadyKnown,
    /// Not validly signed, or malformed.
    Invalid(&'static str),
    /// Spends an output that's not unspent on chain, or that another
    /// pool transaction already spends.
    Conflict,
    Full,
}

impl std::fmt::Display for Rejection {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Rejection::AlreadyKnown => write!(f, "already in the mempool"),
            Rejection::Invalid(why) => write!(f, "invalid transaction: {why}"),
            Rejection::Conflict => write!(f, "spends an output that's already spent (or not on chain)"),
            Rejection::Full => write!(f, "the mempool is full"),
        }
    }
}

fn input_commitments(tx: &Transaction) -> Vec<[u8; 32]> {
    tx.inputs.iter().map(|i| Output::new(&i.pubkey, i.amount).commitment()).collect()
}

fn output_commitments(tx: &Transaction) -> Vec<[u8; 32]> {
    tx.outputs.iter().map(|o| o.commitment()).collect()
}

#[derive(Default)]
pub struct Mempool {
    /// In arrival order.
    transactions: Vec<([u8; 32], Transaction)>,
}

impl Mempool {
    pub fn new() -> Self {
        Mempool::default()
    }

    pub fn len(&self) -> usize {
        self.transactions.len()
    }

    pub fn is_empty(&self) -> bool {
        self.transactions.is_empty()
    }

    pub fn contains(&self, id: &[u8; 32]) -> bool {
        self.transactions.iter().any(|(i, _)| i == id)
    }

    /// Check `tx` against the chain and the pool; add it if it passes,
    /// returning its id.
    pub fn admit(&mut self, tx: Transaction, chain: &impl ChainView) -> Result<[u8; 32], Rejection> {
        let id = tx.id();
        if self.contains(&id) {
            return Err(Rejection::AlreadyKnown);
        }
        if self.transactions.len() >= MAX_TRANSACTIONS {
            return Err(Rejection::Full);
        }
        Self::check(&tx, chain, self.transactions.iter().map(|(_, t)| t))?;
        self.transactions.push((id, tx));
        Ok(id)
    }

    /// Whether `tx` could join a pool holding `others`, against `chain`.
    fn check<'a>(tx: &Transaction, chain: &impl ChainView, others: impl Iterator<Item = &'a Transaction>) -> Result<(), Rejection> {
        if tx.inputs.is_empty() {
            // Only a block's reward creates coins from nothing.
            return Err(Rejection::Invalid("no inputs"));
        }
        if tx.inputs.len() > CHUNK_SHAPE.inputs || tx.outputs.len() > CHUNK_SHAPE.outputs {
            return Err(Rejection::Invalid("too many inputs or outputs for one chunk"));
        }
        if tx.fee().is_none() {
            return Err(Rejection::Invalid("outputs exceed inputs"));
        }
        if !tx.verify() {
            return Err(Rejection::Invalid("bad signature"));
        }
        let inputs = input_commitments(tx);
        let outputs = output_commitments(tx);
        let mut seen = HashSet::new();
        if !outputs.iter().all(|o| seen.insert(*o)) || inputs.iter().any(|i| seen.contains(i)) {
            return Err(Rejection::Invalid("a repeated output, or one spent by its own transaction"));
        }
        if outputs.iter().any(|o| chain.is_unspent(o)) {
            return Err(Rejection::Invalid("creates an output that already exists"));
        }
        if !inputs.iter().all(|i| chain.is_unspent(i)) {
            return Err(Rejection::Conflict);
        }
        for other in others {
            let (their_inputs, their_outputs) = (input_commitments(other), output_commitments(other));
            if inputs.iter().any(|i| their_inputs.contains(i)) {
                return Err(Rejection::Conflict);
            }
            if outputs.iter().any(|o| their_outputs.contains(o)) {
                return Err(Rejection::Invalid("creates an output another pool transaction creates"));
            }
        }
        Ok(())
    }

    /// Re-check every transaction against a changed chain (in arrival
    /// order, so the earlier of two conflicting ones stays), dropping what
    /// no longer fits -- mined, or conflicting with what was. Returns the
    /// ids dropped.
    pub fn revalidate(&mut self, chain: &impl ChainView) -> Vec<[u8; 32]> {
        let mut kept: Vec<([u8; 32], Transaction)> = Vec::with_capacity(self.transactions.len());
        let mut dropped = Vec::new();
        for (id, tx) in std::mem::take(&mut self.transactions) {
            if Self::check(&tx, chain, kept.iter().map(|(_, t)| t)).is_ok() {
                kept.push((id, tx));
            } else {
                dropped.push(id);
            }
        }
        self.transactions = kept;
        dropped
    }

    /// Transactions for a block template, in arrival order, up to
    /// `max_bytes` of encoded transactions in all, and their total fees.
    pub fn select(&self, max_bytes: usize) -> (Vec<Transaction>, u64) {
        let mut out = Vec::new();
        let (mut bytes, mut fees) = (0usize, 0u64);
        for (_, tx) in &self.transactions {
            let size = tx.to_bytes().len();
            if bytes + size > max_bytes {
                break;
            }
            bytes += size;
            fees += tx.fee().unwrap_or(0);
            out.push(tx.clone());
        }
        (out, fees)
    }

    pub fn ids(&self) -> Vec<[u8; 32]> {
        self.transactions.iter().map(|(id, _)| *id).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keychain::{KeyId, Keychain};
    use std::collections::HashSet;

    struct FakeChain(HashSet<[u8; 32]>);

    impl ChainView for FakeChain {
        fn tip_height(&self) -> u64 {
            0
        }
        fn is_unspent(&self, commitment: &[u8; 32]) -> bool {
            self.0.contains(commitment)
        }
    }

    fn keys() -> Keychain {
        Keychain::test("mempool")
    }

    /// Spend the output at key `from` (amount 100) to key `to`, fee `fee`.
    fn spend(from: u32, to: u32, fee: u64) -> Transaction {
        let k = keys();
        let (sk, pk) = k.derive(KeyId::new(0, from));
        let mut tx = Transaction::new();
        tx.add_input(&pk, 100).unwrap();
        tx.add_output(k.output(KeyId::new(0, to), 100 - fee)).unwrap();
        assert!(tx.sign_input(&pk, &sk));
        tx
    }

    fn chain_with(keys_at: &[u32]) -> FakeChain {
        FakeChain(keys_at.iter().map(|&i| keys().output(KeyId::new(0, i), 100).commitment()).collect())
    }

    #[test]
    fn valid_transactions_get_in_once() {
        let chain = chain_with(&[0, 1]);
        let mut pool = Mempool::new();
        let id = pool.admit(spend(0, 10, 5), &chain).unwrap();
        assert!(pool.contains(&id));
        assert_eq!(pool.admit(spend(0, 10, 5), &chain), Err(Rejection::AlreadyKnown));
        pool.admit(spend(1, 11, 7), &chain).unwrap();
        let (txs, fees) = pool.select(usize::MAX);
        assert_eq!((txs.len(), fees), (2, 12));
        assert_eq!(pool.select(1).0.len(), 0, "nothing fits in one byte");
    }

    #[test]
    fn double_spends_and_unknown_inputs_are_refused() {
        let chain = chain_with(&[0]);
        let mut pool = Mempool::new();
        pool.admit(spend(0, 10, 5), &chain).unwrap();
        // The same output spent differently (a second signature with the
        // same key -- exactly what a wallet must never make).
        assert_eq!(pool.admit(spend(0, 12, 6), &chain), Err(Rejection::Conflict));
        // An output not on chain.
        assert_eq!(pool.admit(spend(3, 13, 1), &chain), Err(Rejection::Conflict));
    }

    #[test]
    fn invalid_transactions_are_refused() {
        let chain = chain_with(&[0]);
        let mut pool = Mempool::new();
        let mut unsigned = Transaction::new();
        unsigned.add_input(&keys().public_key(KeyId::new(0, 0)), 100).unwrap();
        unsigned.add_output(keys().output(KeyId::new(0, 10), 90)).unwrap();
        assert_eq!(pool.admit(unsigned, &chain), Err(Rejection::Invalid("bad signature")));
        let mut no_inputs = Transaction::new();
        no_inputs.add_output(keys().output(KeyId::new(0, 10), 90)).unwrap();
        assert_eq!(pool.admit(no_inputs, &chain), Err(Rejection::Invalid("no inputs")));
        // Creating an output that already exists on chain.
        let chain = chain_with(&[0, 10]);
        let mut clash = Transaction::new();
        let (sk, pk) = keys().derive(KeyId::new(0, 0));
        clash.add_input(&pk, 100).unwrap();
        clash.add_output(keys().output(KeyId::new(0, 10), 100)).unwrap();
        assert!(clash.sign_input(&pk, &sk));
        assert_eq!(pool.admit(clash, &chain), Err(Rejection::Invalid("creates an output that already exists")));
    }

    #[test]
    fn revalidation_drops_mined_and_conflicting_transactions() {
        let mut chain = chain_with(&[0, 1]);
        let mut pool = Mempool::new();
        let mined = spend(0, 10, 5);
        pool.admit(mined.clone(), &chain).unwrap();
        pool.admit(spend(1, 11, 5), &chain).unwrap();
        // A block confirms the first: its input is spent, its output exists.
        chain.0.remove(&keys().output(KeyId::new(0, 0), 100).commitment());
        chain.0.insert(mined.outputs[0].commitment());
        assert_eq!(pool.revalidate(&chain), vec![mined.id()]);
        assert_eq!(pool.len(), 1);
        // A block spends the second's input some other way.
        chain.0.remove(&keys().output(KeyId::new(0, 1), 100).commitment());
        assert_eq!(pool.revalidate(&chain).len(), 1);
        assert!(pool.is_empty());
    }
}
