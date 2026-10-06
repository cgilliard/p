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

    /// Wallets on a real chain: Alice mines rewards into her wallet, pays
    /// Bob through slates once they mature, and the payment is mined --
    /// both wallets then agree with the chain. Proof checks are skipped
    /// (about wallets, not proofs).
    #[test]
    fn wallets_mine_pay_and_confirm_on_a_real_chain() {
        use crate::keychain::Keychain;
        use crate::wallet::{Balance, COINBASE_MATURITY, Wallet};

        let dir = TempDir::new();
        let storage = Storage::open(&dir.0.join("chain")).unwrap();
        let mut chain = Chain::open(&storage, chain::DifficultyConfig::for_tests(), 5, None).unwrap();
        chain.skip_proof_checks();
        let alice = Wallet::open_with(&dir.0.join("alice"), Keychain::test("e2e alice")).unwrap();
        let bob = Wallet::open_with(&dir.0.join("bob"), Keychain::test("e2e bob")).unwrap();

        // The miner's loop: a reward to a fresh wallet key per block,
        // refreshing after each.
        let mine = |chain: &mut Chain, others: Vec<Transaction>, fees: u64| {
            let (_, reward) = alice.reward_output(REWARD + fees).unwrap();
            let mut reward_tx = Transaction::new();
            reward_tx.add_output(reward).unwrap();
            let mut txs = vec![reward_tx];
            txs.extend(others);
            mine_and_apply(chain, &txs).unwrap();
            alice.refresh(&chain.view().unwrap()).unwrap();
            bob.refresh(&chain.view().unwrap()).unwrap();
        };
        for _ in 0..=COINBASE_MATURITY {
            mine(&mut chain, vec![], 0);
        }
        let tip = |chain: &Chain| {
            use crate::wallet::ChainView;
            chain.view().unwrap().tip_height()
        };
        let balance = alice.balance(tip(&chain)).unwrap();
        assert_eq!(balance.spendable, 2 * REWARD, "two rewards have matured");
        assert_eq!(balance.immature, (COINBASE_MATURITY - 1) * REWARD);

        // Alice pays Bob 70 (from both mature rewards), fee 3.
        let s1 = alice.send(70, 3, tip(&chain)).unwrap();
        let s2 = bob.receive(&s1).unwrap();
        let tx = alice.finalize(&s2).unwrap();
        assert_eq!(bob.balance(tip(&chain)).unwrap().pending, 70);
        mine(&mut chain, vec![tx], 3);

        let t = tip(&chain);
        assert_eq!(bob.balance(t).unwrap(), Balance { spendable: 70, ..Default::default() });
        let alice_now = alice.balance(t).unwrap();
        assert_eq!(alice_now.locked, 0);
        assert_eq!(alice_now.spendable, 2 * REWARD - 70 - 3 + REWARD, "change, plus the next matured reward");
        assert!(alice.unconfirmed_transactions().unwrap().is_empty());

        // Bob can spend what he received (it's mature: not a reward).
        let s1 = bob.send(60, 1, t).unwrap();
        let s2 = alice.receive(&s1).unwrap();
        let tx = bob.finalize(&s2).unwrap();
        mine(&mut chain, vec![tx], 1);
        assert_eq!(bob.balance(tip(&chain)).unwrap().spendable, 9);
    }


    /// The whole pipeline with real proofs, on a chain that checks every
    /// one -- including a tree proof built from a real mempool. A miner
    /// mines 10 blocks into its wallet, then over the next 10 moves those
    /// funds between addresses it controls: splitting a reward into 12
    /// outputs (block 11), spending 12 of them in one block (block 12:
    /// more inputs than one chunk holds, so a tree proof), and ordinary
    /// self-transfers after. Every fee comes back to the miner, so at the
    /// end its wallet must hold exactly what was mined.
    ///
    /// Slow (about 10 minutes, mostly the tree proof); run with
    /// `cargo test --release -- --ignored --nocapture mine_then_spend_with_real_proofs`.
    #[test]
    #[ignore]
    fn mine_then_spend_with_real_proofs() {
        use crate::keychain::Keychain;
        use crate::mempool::Mempool;
        use crate::wallet::{ChainView, Wallet};
        const REWARD: u64 = prover::REWARD;
        const FEE: u64 = 100_000; // 0.0001

        let dir = TempDir::new();
        let storage = Storage::open(&dir.0.join("chain")).unwrap();
        // Proof checks stay on: every block is verified as consensus would.
        let mut chain = Chain::open(&storage, chain::DifficultyConfig::for_tests(), 5, None).unwrap();
        let wallet = Wallet::open_with(&dir.0.join("wallet"), Keychain::test("e2e real proofs")).unwrap();
        let mut mempool = Mempool::new();
        let tip = |chain: &Chain| chain.view().unwrap().tip_height();

        // What the node's miner does, synchronously: template from the
        // mempool, reward to a fresh key claiming the fees, prove (direct
        // or tree), mine, apply; then wallet and mempool follow the chain.
        let mine = |chain: &mut Chain, mempool: &mut Mempool| -> (bool, usize) {
            let (txs, fees) = mempool.select(1 << 20);
            let (_, reward) = wallet.reward_output(REWARD + fees).unwrap();
            let mut reward_tx = Transaction::new();
            reward_tx.add_output(reward).unwrap();
            let count = txs.len();
            let transactions: Vec<Transaction> = std::iter::once(reward_tx).chain(txs).collect();
            let unproven = chain.build_block(&transactions).unwrap();
            let (target, min_timestamp, inputs) = (unproven.target, unproven.min_timestamp, unproven.inputs.len());
            let start = std::time::Instant::now();
            let proof = prover::prove_block_auto(&unproven.inputs, &unproven.outputs, &transactions, [7; 32]).unwrap();
            let proving = start.elapsed();
            let tree = proof.is_tree();
            let size = proof.len();
            let mut block = unproven.finish(proof);
            block.header.timestamp = block.header.timestamp.max(min_timestamp);
            assert!(mine_block(&mut block, &target, u64::MAX));
            let height = block.header.height;
            assert_eq!(chain.accept_block(block).unwrap(), chain::AcceptOutcome::Applied, "block {height}");
            let view = chain.view().unwrap();
            wallet.refresh(&view).unwrap();
            assert!(mempool.revalidate(&view).len() == count && mempool.is_empty(), "every transaction was mined");
            println!(
                "height {height:2}: {count} transaction(s), {inputs:2} inputs -- {} proof, {:.1} KB, proved in {proving:.1?}",
                if tree { "tree" } else { "direct" },
                size as f64 / 1024.0
            );
            (tree, inputs)
        };
        let submit = |chain: &Chain, mempool: &mut Mempool, tx: Transaction| {
            mempool.admit(tx, &chain.view().unwrap()).unwrap();
        };

        // Blocks 1-10: rewards only.
        for _ in 0..10 {
            assert!(!mine(&mut chain, &mut mempool).0);
        }
        let b = wallet.balance(tip(&chain)).unwrap();
        assert_eq!((b.spendable, b.immature), (REWARD, 9 * REWARD), "the first reward has matured");

        // Block 11: split the mature reward into 12 outputs of 0.08.
        let piece = 80_000_000;
        let split = wallet.self_transfer(None, &[piece; 12], FEE, tip(&chain)).unwrap();
        submit(&chain, &mut mempool, split);
        mine(&mut chain, &mut mempool);

        // Block 12: spend all twelve, six per transaction -- 12 inputs in
        // one block, more than a chunk holds: a tree proof.
        let pieces: Vec<[u8; 32]> = wallet.outputs().unwrap().iter().filter(|o| o.amount == piece).map(|o| o.commitment).collect();
        assert_eq!(pieces.len(), 12);
        for half in pieces.chunks(6) {
            let tx = wallet.self_transfer(Some(half), &[6 * piece - FEE], FEE, tip(&chain)).unwrap();
            submit(&chain, &mut mempool, tx);
        }
        let (tree, inputs) = mine(&mut chain, &mut mempool);
        assert!(tree && inputs == 12, "a block with 12 inputs is tree-proven");

        // Blocks 13-20: ordinary self-transfers from whatever's spendable.
        for _ in 13..=20 {
            let tx = wallet.self_transfer(None, &[300_000_000, 200_000_000], FEE, tip(&chain)).unwrap();
            submit(&chain, &mut mempool, tx);
            mine(&mut chain, &mut mempool);
        }

        // Every fee came back to the miner: the wallet holds exactly the
        // 20 rewards, nothing pending or locked. (This chain has no
        // genesis block: its first block is height 0, so 20 blocks end at
        // height 19.)
        assert_eq!(tip(&chain), 19);
        let b = wallet.balance(tip(&chain)).unwrap();
        assert_eq!(b.pending + b.locked, 0, "{b:?}");
        assert_eq!(b.spendable + b.immature, 20 * REWARD, "{b:?}");
        assert!(wallet.unconfirmed_transactions().unwrap().is_empty());
    }

}
