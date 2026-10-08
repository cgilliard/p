//! End-to-end test of a tiny chain, driven entirely through the public
//! `chain`/`block`/`transaction`/`prover`/`pow` API -- the same pipeline
//! a real miner would run (`Chain::build_block` -> `prover::prove_block`
//! -> `block::UnprovenBlock::finish` -> `block::mine_block`, then
//! `Chain::apply_block`). Nothing here reaches into `Chain`'s private
//! `state`/`utxo` fields -- they aren't even visible from this
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
        assert!(mine_block(&mut block, &target, 100_000, &crate::pow::Params::TEST), "should find a nonce quickly");
        chain.apply_block(&block)
    }

    /// A single miner mines two blocks: the first just claims its block
    /// reward, the second claims a fresh reward *and* sends the first
    /// block's reward on to another user. Confirms the send actually
    /// worked, and that the spent output can't be spent again -- using
    /// only `Chain`'s public API, never reaching into its `state`/
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
            // Every output both wallets made reached the chain with its
            // recovery nonce intact.
            assert!(alice.refresh(&chain.view().unwrap()).unwrap().is_empty());
            assert!(bob.refresh(&chain.view().unwrap()).unwrap().is_empty());
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
            let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &unproven.nonces, &transactions, &unproven.plan, [7; 32]).unwrap();
            let proving = start.elapsed();
            let tree = unproven.plan.chunks.len() > 1;
            let size = proof.len();
            let mut block = unproven.finish(proof);
            block.header.timestamp = block.header.timestamp.max(min_timestamp);
            assert!(mine_block(&mut block, &target, u64::MAX, &crate::pow::Params::TEST));
            let height = block.header.height;
            assert_eq!(chain.accept_block(block).unwrap(), chain::AcceptOutcome::Applied, "block {height}");
            let view = chain.view().unwrap();
            assert!(wallet.refresh(&view).unwrap().is_empty(), "every nonce arrived intact");
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
        // The rewards from heights 0 ..= 10 - maturity have matured.
        let maturity = crate::wallet::coinbase_maturity();
        let b = wallet.balance(tip(&chain)).unwrap();
        assert_eq!((b.spendable, b.immature), ((11 - maturity) * REWARD, (maturity - 1) * REWARD), "the first rewards have matured");

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


    /// Mine one block with real proofs, as the node's miner does: a
    /// template from `mempool`, the reward (with fees) to `miner`, proven
    /// (direct or tree), mined, and applied to a chain that checks every
    /// proof; then every wallet refreshes (and must find every nonce
    /// intact) and the mempool drops what was mined.
    fn mine_real(chain: &mut Chain, mempool: &mut crate::mempool::Mempool, miner: &crate::wallet::Wallet, wallets: &[&crate::wallet::Wallet]) {
        let (txs, fees) = mempool.select(1 << 20);
        let (_, reward) = miner.reward_output(prover::REWARD + fees).unwrap();
        let mut reward_tx = Transaction::new();
        reward_tx.add_output(reward).unwrap();
        let transactions: Vec<Transaction> = std::iter::once(reward_tx).chain(txs).collect();
        let unproven = chain.build_block(&transactions).unwrap();
        let (target, min_timestamp) = (unproven.target, unproven.min_timestamp);
        let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &unproven.nonces, &transactions, &unproven.plan, [7; 32]).unwrap();
        let mut block = unproven.finish(proof);
        block.header.timestamp = block.header.timestamp.max(min_timestamp);
        assert!(mine_block(&mut block, &target, u64::MAX, &crate::pow::Params::TEST));
        assert_eq!(chain.accept_block(block).unwrap(), chain::AcceptOutcome::Applied);
        let view = chain.view().unwrap();
        for w in wallets.iter().chain([&miner]) {
            assert!(w.refresh(&view).unwrap().is_empty(), "a nonce arrived altered");
        }
        mempool.revalidate(&view);
    }

    /// Admit `tx` to the mempool, and let every wallet see it -- as the
    /// node does (`Wallet::observe_spend`).
    fn submit_real(chain: &Chain, mempool: &mut crate::mempool::Mempool, tx: &Transaction, wallets: &[&crate::wallet::Wallet]) {
        mempool.admit(tx.clone(), &chain.view().unwrap()).unwrap();
        for w in wallets {
            w.observe_spend(tx).unwrap();
        }
    }

    /// `docs/RECOVERY.md`'s acceptance test, with real proofs on a chain
    /// that checks every one. Alice mines, pays Bob, is paid by Bob, splits
    /// coins, and has one more spend signed and waiting in the mempool when
    /// her wallet is lost. A wallet restored from her **24 words alone**
    /// finds exactly her unspent outputs, respects the spend in flight
    /// (and gets its change once it confirms), never reuses a key, and --
    /// after the hold -- pays Bob.
    ///
    /// Slow (a few minutes of proving); run with
    /// `cargo test --release -- --ignored --nocapture a_wallet_restored_from_its_words`.
    #[test]
    #[ignore]
    fn a_wallet_restored_from_its_words_alone_with_real_proofs() {
        use crate::keychain::Keychain;
        use crate::mempool::Mempool;
        use crate::wallet::{ChainView, RECOVERY_HOLD_BLOCKS, RECOVERY_INDEX_MARGIN, Status, Wallet};
        const FEE: u64 = 100_000;
        let unspent_of = |w: &Wallet| {
            let mut v: Vec<([u8; 32], u64)> = w.outputs().unwrap().iter().filter(|o| o.seen_height.is_some() && !o.spent).map(|o| (o.commitment, o.amount)).collect();
            v.sort();
            v
        };

        let dir = TempDir::new();
        let storage = Storage::open(&dir.0.join("chain")).unwrap();
        let mut chain = Chain::open(&storage, chain::DifficultyConfig::for_tests(), 5, None).unwrap();
        let mut mempool = Mempool::new();
        let alice = Wallet::open_with(&dir.0.join("alice"), Keychain::random()).unwrap();
        let bob = Wallet::open_with(&dir.0.join("bob"), Keychain::random()).unwrap();
        let tip = |chain: &Chain| chain.view().unwrap().tip_height();

        // Alice mines 11 blocks: her first reward matures.
        for _ in 0..11 {
            mine_real(&mut chain, &mut mempool, &alice, &[&bob]);
        }
        // She pays Bob 0.3; Bob pays her back 0.1; she splits a coin.
        let s1 = alice.send(300_000_000, FEE, tip(&chain)).unwrap();
        let pay = alice.finalize(&bob.receive(&s1).unwrap()).unwrap();
        submit_real(&chain, &mut mempool, &pay, &[&alice, &bob]);
        mine_real(&mut chain, &mut mempool, &alice, &[&bob]);
        let s1 = bob.send(100_000_000, FEE, tip(&chain)).unwrap();
        let back = bob.finalize(&alice.receive(&s1).unwrap()).unwrap();
        submit_real(&chain, &mut mempool, &back, &[&alice, &bob]);
        mine_real(&mut chain, &mut mempool, &alice, &[&bob]);
        let split = alice.self_transfer(None, &[50_000_000, 70_000_000], FEE, tip(&chain)).unwrap();
        submit_real(&chain, &mut mempool, &split, &[&alice, &bob]);
        mine_real(&mut chain, &mut mempool, &alice, &[&bob]);
        // One more spend, signed and in the mempool -- then the wallet is lost.
        let in_flight = alice.self_transfer(None, &[110_000_000], FEE, tip(&chain)).unwrap();
        submit_real(&chain, &mut mempool, &in_flight, &[&alice, &bob]);

        let on_chain = unspent_of(&alice);
        assert!(on_chain.len() >= 12, "{} unspent", on_chain.len());
        let used = alice.outputs().unwrap().iter().map(|o| o.key.index).max().unwrap();
        let words = alice.keychain().phrase();
        let in_flight_inputs: Vec<[u8; 32]> = in_flight.inputs.iter().map(|i| i.commitment()).collect();
        let mut after_in_flight: Vec<([u8; 32], u64)> = on_chain.iter().filter(|(c, _)| !in_flight_inputs.contains(c)).copied().collect();
        after_in_flight.extend(in_flight.outputs.iter().map(|o| (o.commitment(), o.amount)));
        after_in_flight.sort();
        drop(alice);
        std::fs::remove_dir_all(dir.0.join("alice")).unwrap();
        println!("lost at height {}: {} unspent outputs, keys used up to {used}", tip(&chain), on_chain.len());

        // Restored from the words alone.
        let restored = Wallet::restore(&dir.0.join("restored"), Keychain::from_phrase(&words).unwrap()).unwrap();
        let report = restored.finish_recovery(&chain.view().unwrap()).unwrap();
        println!("{report:?}");
        assert_eq!(unspent_of(&restored), on_chain, "exactly her unspent outputs");
        assert_eq!((report.unspent, report.amount), (on_chain.len(), on_chain.iter().map(|o| o.1).sum()));
        // Past every key she ever handed out -- including ones never on
        // chain (the in-flight spend's outputs), which the margin covers.
        assert!(report.next_index > used, "{} <= {used}", report.next_index);
        assert!(report.next_index >= RECOVERY_INDEX_MARGIN);
        let now = tip(&chain);
        assert!(restored.outputs().unwrap().iter().filter(|o| !o.spent).all(|o| matches!(o.status(now), Status::Held { .. })));

        // The node sees the spend in its mempool: never signed again, and
        // resubmitted by the restored wallet.
        assert!(restored.observe_spend(&in_flight).unwrap());
        assert_eq!(restored.unconfirmed_transactions().unwrap().len(), 1);
        assert!(restored.self_transfer(Some(&in_flight_inputs), &[1], 0, now + RECOVERY_HOLD_BLOCKS).is_err());

        // Bob mines through the hold; the spend in flight confirms in the
        // first block, and its change is the restored wallet's.
        for _ in 0..RECOVERY_HOLD_BLOCKS {
            mine_real(&mut chain, &mut mempool, &bob, &[&restored]);
        }
        assert!(mempool.is_empty());
        assert_eq!(unspent_of(&restored), after_in_flight, "the in-flight spend's outputs are found");
        let b = restored.balance(tip(&chain)).unwrap();
        assert_eq!((b.held, b.locked, b.pending), (0, 0, 0), "{b:?}");
        assert_eq!(b.spendable, after_in_flight.iter().map(|o| o.1).sum::<u64>());

        // And it pays Bob, with new keys only.
        let bob_before = bob.balance(tip(&chain)).unwrap();
        let s1 = restored.send(200_000_000, FEE, tip(&chain)).unwrap();
        let pay = restored.finalize(&bob.receive(&s1).unwrap()).unwrap();
        submit_real(&chain, &mut mempool, &pay, &[&restored, &bob]);
        mine_real(&mut chain, &mut mempool, &bob, &[&restored]);
        let bob_after = bob.balance(tip(&chain)).unwrap();
        assert_eq!(bob_after.spendable + bob_after.immature, bob_before.spendable + bob_before.immature + 200_000_000 + prover::REWARD + FEE);
        let new_keys: Vec<u32> = restored.outputs().unwrap().iter().filter(|o| o.origin != crate::wallet::Origin::Recovered).map(|o| o.key.index).collect();
        assert!(!new_keys.is_empty() && new_keys.iter().all(|&k| k >= report.next_index), "{new_keys:?}");
        println!("restored wallet paid Bob at height {}; new keys from {}", tip(&chain), report.next_index);
    }


    /// Chain proofs as consensus (`docs/CHAIN_RECURSION.md`, 5c): a chain
    /// that requires every block to carry its parent's chain proof, every
    /// block proven for real. Block 1 carries the genesis circuit's proof,
    /// later ones a step proof -- each verified against the parent as the
    /// chain records it (height, state, target, work...). A block carrying
    /// a chain proof of the wrong parent is refused.
    /// `NETWORK=dev cargo test --release -- --ignored --nocapture chain_proofs_as_consensus`.
    #[test]
    #[ignore]
    fn chain_proofs_as_consensus() {
        use crate::chain_step::ChainProver;
        let dir = TempDir::new();
        let config = chain::DifficultyConfig::for_tests();
        // A fixed genesis block (empty), as a network has.
        let genesis = {
            let scratch = Storage::open(&dir.0.join("scratch")).unwrap();
            let mut c = Chain::open(&scratch, config, 5, None).unwrap();
            let unproven = c.build_block(&[]).unwrap();
            let target = unproven.target;
            let mut g = unproven.finish(prover::Proof::placeholder());
            assert!(mine_block(&mut g, &target, u64::MAX, &crate::pow::Params::TEST));
            g
        };
        let storage = Storage::open(&dir.0.join("chain")).unwrap();
        let mut chain = Chain::open(&storage, config, 5, Some(&genesis)).unwrap();
        let mut chain_prover = ChainProver::new(config, prover::tree());
        let reader = chain::BlockReader::open(&storage).unwrap();
        let tip = |_: &Chain| reader.tip().unwrap().unwrap().1;

        // Make the next block on the tip, carrying the tip's chain proof.
        let make = |chain: &mut Chain, chain_prover: &mut ChainProver, k: u8, chain_proof: Option<Vec<u8>>| -> (crate::block::Block, Vec<u8>) {
            let parent = tip(chain);
            let start = std::time::Instant::now();
            let inputs = chain.chain_proof_inputs(parent).unwrap();
            let second = || reader.active_hash_at(1).ok().flatten().and_then(|h| chain.chain_proof_inputs(h).ok());
            let made = chain_prover.prove(&inputs, second, [k; 32]).unwrap();
            let chain_proof_time = start.elapsed();
            let (_, pk) = wots::keygen(&[90 + k; 32]);
            let mut reward = Transaction::new();
            reward.add_output(Output::new(&pk, prover::REWARD)).unwrap();
            let txs = [reward];
            let unproven = chain.build_block(&txs).unwrap();
            let (target, min_timestamp) = (unproven.target, unproven.min_timestamp);
            let start = std::time::Instant::now();
            let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &unproven.nonces, &txs, &unproven.plan, [k; 32]).unwrap();
            println!("block {}: chain proof {chain_proof_time:.1?}, block proof {:.1?}", unproven.height, start.elapsed());
            let mut block = unproven.finish_with_chain_proof(proof, chain_proof.unwrap_or_else(|| made.clone()));
            block.header.timestamp = block.header.timestamp.max(min_timestamp);
            assert!(mine_block(&mut block, &target, u64::MAX, &crate::pow::Params::TEST));
            (block, made)
        };

        // Block 1: carries the genesis proof. Requiring chain proofs needs
        // only the genesis circuit's key for it.
        let (b1, genesis_proof) = make(&mut chain, &mut chain_prover, 1, None);
        chain.require_chain_proofs(chain_prover.verifier().unwrap());
        assert_eq!(chain.accept_block(b1).unwrap(), chain::AcceptOutcome::Applied);
        // Block 2: its chain proof (of block 1) is the first step proof;
        // proving it derives the step key, so the full verifier exists.
        let (b2, _) = make(&mut chain, &mut chain_prover, 2, None);
        chain.require_chain_proofs(chain_prover.verifier().unwrap());
        assert_eq!(chain.accept_block(b2).unwrap(), chain::AcceptOutcome::Applied);
        // Block 3 with the wrong chain proof (genesis's, not block 2's).
        let (bad, _) = make(&mut chain, &mut chain_prover, 3, Some(genesis_proof));
        assert!(chain.accept_block(bad).is_err(), "a chain proof of another block");
        // Block 3, right: a step proof over a step proof.
        let (b3, _) = make(&mut chain, &mut chain_prover, 3, None);
        assert_eq!(chain.accept_block(b3).unwrap(), chain::AcceptOutcome::Applied);
        assert_eq!(reader.tip().unwrap().unwrap().0, 3);
    }

}
