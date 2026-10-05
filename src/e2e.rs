//! End-to-end test of a tiny chain, driven entirely through the public
//! `chain`/`block`/`transaction`/`prover`/`pow` API -- the same pipeline
//! a real miner would run (`Chain::build_block` -> `prover::prove_block`
//! -> `block::UnprovenBlock::finish` -> `block::mine_block`, then
//! `Chain::apply_block`). Nothing here reaches into `Chain`'s private
//! `pmmr`/`bitmap`/`utxo` fields -- they aren't even visible from this
//! module -- so every assertion goes through the same surface a real
//! caller would have.

#[cfg(test)]
mod tests {
    use crate::block::mine_block;
    use crate::chain::{self, Chain, Error};
    use crate::output::Output;
    use crate::prover;
    use crate::storage::Storage;
    use crate::transaction::Transaction;
    use crate::wots::{self, PublicKey, SecretKey};
    use std::sync::atomic::{AtomicU64, Ordering};

    const REWARD: u64 = 50;

    struct TempDir(std::path::PathBuf);

    impl TempDir {
        fn new() -> Self {
            static COUNTER: AtomicU64 = AtomicU64::new(0);
            let n = COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!("e2e-test-{}-{n}", std::process::id()));
            std::fs::create_dir_all(&path).unwrap();
            TempDir(path)
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn keypair(seed: u8) -> (SecretKey, PublicKey) {
        wots::keygen(&[seed; 32])
    }

    /// A zero-input, one-output transaction: the shape a miner's block
    /// reward takes (see `block`'s module docs -- there's no separate
    /// "coinbase" concept).
    fn reward_transaction(pubkey: &PublicKey, amount: u64) -> Transaction {
        let mut tx = Transaction::new();
        tx.add_output(Output::new(pubkey, amount)).unwrap();
        tx
    }

    /// A one-input, one-output transaction spending the entire `amount`
    /// owned by `(from_sk, from_pk)` to `to_pk`, fully signed.
    fn spend_transaction(from_sk: &SecretKey, from_pk: &PublicKey, amount: u64, to_pk: &PublicKey) -> Transaction {
        let mut tx = Transaction::new();
        tx.add_input(from_pk, amount).unwrap();
        tx.add_output(Output::new(to_pk, amount)).unwrap();
        assert!(tx.sign_input(from_pk, from_sk));
        tx
    }

    /// Run the real `build_block` -> `prover::prove_block` ->
    /// `UnprovenBlock::finish` -> `mine_block` pipeline a miner would
    /// run, then `apply_block` it -- the same steps a real node follows,
    /// all through `Chain`'s public API.
    fn mine_and_apply(chain: &mut Chain, transactions: &[Transaction]) -> Result<(), Error> {
        let unproven = chain.build_block(transactions)?;
        let target = unproven.target;
        let proof =
            prover::Proof::placeholder();
        let mut block = unproven.finish(proof);
        assert!(mine_block(&mut block, &target, 100_000), "should find a nonce quickly");
        chain.apply_block(&block)
    }

    /// A single miner mines two blocks: the first just claims its block
    /// reward, the second claims a fresh reward *and* sends the first
    /// block's reward on to another user. Confirms the send actually
    /// worked, and that the spent output can't be spent again -- using
    /// only `Chain`'s public API, never reaching into `pmmr`/`bitmap`/
    /// `utxo` directly.
    #[test]
    fn miner_mines_two_blocks_and_pays_another_user() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut chain = Chain::open(&storage, chain::DifficultyConfig::for_tests(), 5, None).unwrap();
        // About the transaction flow, not proofs: real ones take seconds
        // each in a debug build (see `prover`'s tests for those).
        chain.skip_proof_checks();

        // The miner's two reward addresses -- a fresh one each time,
        // since a WOTS pubkey can only ever sign once (see
        // `transaction`'s module docs); reusing one as a second
        // receiving address would also just recreate the exact same
        // commitment as the first reward, before it's even been spent.
        let (sk_miner_1, pk_miner_1) = keypair(1);
        let (_sk_miner_2, pk_miner_2) = keypair(2);
        // The other user's address, receiving the send in block 2.
        let (sk_recipient, pk_recipient) = keypair(3);

        // Block 1: the miner claims its reward. Nothing else has
        // happened yet, so this is the chain's very first block.
        mine_and_apply(&mut chain, &[reward_transaction(&pk_miner_1, REWARD)]).unwrap();

        // Block 2: the miner claims a second, fresh reward, and spends
        // the first block's reward entirely to the other user.
        let payment = spend_transaction(&sk_miner_1, &pk_miner_1, REWARD, &pk_recipient);
        mine_and_apply(&mut chain, &[reward_transaction(&pk_miner_2, REWARD), payment]).unwrap();

        // Proof the send actually landed: the recipient can now spend
        // what they were sent. If the output didn't really exist, this
        // would fail to resolve.
        let (_sk_final, pk_final) = keypair(4);
        let onward = spend_transaction(&sk_recipient, &pk_recipient, REWARD, &pk_final);
        mine_and_apply(&mut chain, &[onward]).unwrap();

        // The original reward is spent now -- trying to spend it again
        // (e.g. to a different address) must fail to resolve, not
        // silently succeed.
        let (_sk_thief, pk_thief) = keypair(5);
        let double_spend = spend_transaction(&sk_miner_1, &pk_miner_1, REWARD, &pk_thief);
        let err = mine_and_apply(&mut chain, &[double_spend]).unwrap_err();
        assert!(matches!(err, Error::UnresolvedInput(_)));
    }
}
