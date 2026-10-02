//! A block: a list of transactions, plus the implicit rule that makes it
//! more than just a bag of independently-valid transactions -- the whole
//! thing has to balance.
//!
//! **Deliberately narrow scope for now.** A real block also needs a
//! header (previous-block hash, PMMR root, bitmap hash, proof-of-work),
//! and validating one fully means checking that header against the
//! chain's actual PMMR and bitmap state (resolving each input to a real
//! position, catching double-spends across transactions in the block,
//! replaying the resulting updates). None of that is here yet -- this is
//! just the balance statement on its own, since that's the first thing
//! intended to be backed by a real STARK proof (built separately, likely
//! over several steps: trace, constraints, quotient, composition, then
//! finally the existing `fri` commit/query machinery). Everything else
//! above gets added once that exists, rather than guessing its shape now.
//!
//! # The coinbase transaction
//!
//! Whoever assembles the block is allowed to claim the block reward, plus
//! every fee left over from the block's other transactions (recall:
//! `Transaction::verify` only requires `input_total >= output_total`, so
//! any excess is an implicit, as-yet-uncollected fee). They do that by
//! adding one more `Transaction` to the block with **zero inputs** and
//! one or more outputs -- nothing new in `transaction.rs` for this; a
//! zero-input transaction already type-checks fine there, it just happens
//! to be unable to pass `Transaction::verify`'s own balance check (`0 >=
//! some positive output total` is false). That's exactly why it's handled
//! here instead: a block recognizes a transaction with no inputs as the
//! coinbase, skips the normal per-transaction balance check for it
//! specifically (there's nothing to sign either, so nothing else to check
//! on it in isolation), and relies entirely on the block-wide equation
//! below to constrain what it's allowed to claim.
//!
//! # The balance equation
//!
//! `sum(every output in the block) == sum(every input in the block) +
//! BLOCK_REWARD`. New value only ever enters through `BLOCK_REWARD`; the
//! coinbase's own output(s) aren't special-cased in this sum at all, they
//! just count like anyone else's. Since every *other* transaction already
//! satisfies `input_total >= output_total` on its own, the only way this
//! equation holds exactly is if the coinbase claims precisely the reward
//! plus the total of every other transaction's leftover fee -- claiming
//! less burns the difference, claiming more fails the check outright.

#![allow(dead_code)]

use crate::transaction::Transaction;

/// Fixed block subsidy, paid to whoever assembles the block, on top of
/// whatever fees the block's other transactions leave unclaimed. No
/// halving schedule yet -- that would depend on block height, which isn't
/// a tracked concept anywhere in this codebase yet either.
pub const BLOCK_REWARD: u64 = 50;

#[derive(Clone, Debug, Default)]
pub struct Block {
    pub transactions: Vec<Transaction>,
}

impl Block {
    pub fn new() -> Self {
        Block {
            transactions: Vec::new(),
        }
    }

    /// Whether this block is internally sound: exactly one coinbase
    /// (zero-input) transaction, every other transaction independently
    /// valid via `Transaction::verify`, and the whole block balances
    /// (see the module docs). This is the plain-Rust reference check --
    /// not succinct, not zero-knowledge, just the ground truth that a
    /// real STARK proof will eventually be checked against instead of
    /// re-deriving.
    pub fn validate(&self) -> bool {
        let coinbase_count = self.transactions.iter().filter(|tx| tx.inputs.is_empty()).count();
        if coinbase_count != 1 {
            return false;
        }

        let mut total_inputs: u128 = 0;
        let mut total_outputs: u128 = 0;

        for tx in &self.transactions {
            if tx.inputs.is_empty() {
                // The coinbase: nothing to sign, and deliberately exempt
                // from the per-transaction balance check -- it's expected
                // to create value, not just move it. The aggregate check
                // below is what actually constrains how much it claims.
            } else if !tx.verify() {
                return false;
            }

            total_inputs += tx.inputs.iter().map(|i| i.amount as u128).sum::<u128>();
            total_outputs += tx.outputs.iter().map(|o| o.amount as u128).sum::<u128>();
        }

        total_outputs == total_inputs + BLOCK_REWARD as u128
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::output::Output;
    use crate::wots::{self, PublicKey, SecretKey};

    fn keypair(byte: u8) -> (SecretKey, PublicKey) {
        wots::keygen(&[byte; 32])
    }

    fn coinbase(byte: u8, amount: u64) -> Transaction {
        let (_, pk) = keypair(byte);
        let mut tx = Transaction::new();
        tx.add_output(Output::new(&pk, amount)).unwrap();
        tx
    }

    #[test]
    fn block_with_only_a_coinbase_validates() {
        let mut block = Block::new();
        block.transactions.push(coinbase(1, BLOCK_REWARD));
        assert!(block.validate());
    }

    #[test]
    fn block_without_any_coinbase_is_rejected() {
        // Just a perfectly self-balanced regular transaction, no coinbase
        // -- the block reward is never accounted for anywhere.
        let (sk_a, pk_a) = keypair(1);
        let (_, pk_out) = keypair(2);

        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 100).unwrap();
        tx.add_output(Output::new(&pk_out, 100)).unwrap();
        tx.sign_input(&pk_a, &sk_a);

        let mut block = Block::new();
        block.transactions.push(tx);
        assert!(!block.validate());
    }

    #[test]
    fn block_with_two_coinbases_is_rejected() {
        let mut block = Block::new();
        block.transactions.push(coinbase(1, BLOCK_REWARD));
        block.transactions.push(coinbase(2, 0));
        assert!(!block.validate());
    }

    #[test]
    fn coinbase_must_claim_exactly_the_available_fee_plus_reward() {
        let (sk_a, pk_a) = keypair(1);
        let (_, pk_out) = keypair(2);

        // A regular transaction with a 50-unit implicit fee.
        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 150).unwrap();
        tx.add_output(Output::new(&pk_out, 100)).unwrap();
        tx.sign_input(&pk_a, &sk_a);
        assert!(tx.verify());

        // Claiming exactly fee + reward balances.
        let mut balanced = Block::new();
        balanced.transactions.push(tx.clone());
        balanced.transactions.push(coinbase(3, 50 + BLOCK_REWARD));
        assert!(balanced.validate());

        // Claiming less burns the difference instead of collecting it --
        // still rejected, not just "less profitable."
        let mut under_claimed = Block::new();
        under_claimed.transactions.push(tx.clone());
        under_claimed.transactions.push(coinbase(3, BLOCK_REWARD));
        assert!(!under_claimed.validate());

        // Claiming more than is actually available is rejected outright.
        let mut over_claimed = Block::new();
        over_claimed.transactions.push(tx);
        over_claimed.transactions.push(coinbase(3, 51 + BLOCK_REWARD));
        assert!(!over_claimed.validate());
    }

    #[test]
    fn block_with_invalid_regular_transaction_is_rejected() {
        let (sk_a, pk_a) = keypair(1);
        let (_, pk_out) = keypair(2);

        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 100).unwrap();
        tx.add_output(Output::new(&pk_out, 100)).unwrap();
        tx.sign_input(&pk_a, &sk_a);

        // Tamper with the signed amount after signing -- breaks the
        // signature, same as in `transaction`'s own tests.
        tx.inputs[0].amount += 1;

        let mut block = Block::new();
        block.transactions.push(tx);
        block.transactions.push(coinbase(3, BLOCK_REWARD));
        assert!(!block.validate());
    }

    #[test]
    fn block_with_unsigned_regular_transaction_is_rejected() {
        let (_, pk_a) = keypair(1);
        let (_, pk_out) = keypair(2);

        let mut tx = Transaction::new();
        tx.add_input(&pk_a, 100).unwrap();
        tx.add_output(Output::new(&pk_out, 100)).unwrap();
        // Never signed.

        let mut block = Block::new();
        block.transactions.push(tx);
        block.transactions.push(coinbase(3, BLOCK_REWARD));
        assert!(!block.validate());
    }

    /// Multiple regular transactions, each with its own fee, all rolled
    /// up into one coinbase claim.
    #[test]
    fn multiple_regular_transactions_with_fees_roll_up_into_one_coinbase() {
        let (sk_a, pk_a) = keypair(1);
        let (sk_b, pk_b) = keypair(2);
        let (_, pk_out_1) = keypair(3);
        let (_, pk_out_2) = keypair(4);

        let mut tx_a = Transaction::new();
        tx_a.add_input(&pk_a, 120).unwrap(); // fee 20
        tx_a.add_output(Output::new(&pk_out_1, 100)).unwrap();
        tx_a.sign_input(&pk_a, &sk_a);

        let mut tx_b = Transaction::new();
        tx_b.add_input(&pk_b, 80).unwrap(); // fee 30
        tx_b.add_output(Output::new(&pk_out_2, 50)).unwrap();
        tx_b.sign_input(&pk_b, &sk_b);

        let mut block = Block::new();
        block.transactions.push(tx_a);
        block.transactions.push(tx_b);
        block.transactions.push(coinbase(5, 20 + 30 + BLOCK_REWARD));

        assert!(block.validate());
    }
}
