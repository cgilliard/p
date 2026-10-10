//! The node's event loop: one place that owns the chain, the wallet and
//! the mempool, and serves everything else -- blocks from the network,
//! requests from the CLI (`cli`), and its own mining -- one event at a
//! time, so nothing shares mutable state.
//!
//! # Mining
//!
//! Mining is a small state machine stepped by the loop:
//!
//! - **Idle**: when mining is on, build a template -- the reward to a fresh
//!   wallet key, plus mempool transactions -- and start proving it.
//! - **Proving**: on a worker thread (seconds for a small block, minutes for
//!   a tree), so requests and blocks keep being handled meanwhile.
//! - **Mining**: proof of work in batches of nonces between events.
//!
//! Whenever the tip moves, a template built on the old tip is abandoned
//! (its expected reward forgotten), and the wallet and mempool are
//! brought up to date.

use std::net::SocketAddrV4;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{Receiver, Sender, TryRecvError};
use std::time::{Duration, Instant};

use crate::block::{Block, UnprovenBlock, mine_block, now_millis};
use crate::chain::{AcceptOutcome, BlockReader, Chain};
use crate::mempool::{Mempool, Rejection};
use crate::net::Command;
use crate::output::format_amount;
use crate::peers::PeerTable;
use crate::prover;
use crate::slate::Slate;
use crate::transaction::Transaction;
use crate::wallet::{self, ChainView, Wallet};

/// A request from the CLI.
#[derive(Debug)]
pub enum Request {
    Balance,
    Outputs,
    /// Start a payment; write slate S1 to `file` (default
    /// `<id>.s1.slate`).
    Send { amount: u64, fee: u64, file: Option<PathBuf> },
    /// Answer slate S1 in `file`; write S2 to `<id>.s2.slate`.
    Receive { file: PathBuf },
    /// Finish a payment from slate S2 in `file` and submit it.
    Finalize { file: PathBuf },
    Cancel { id: [u8; 16] },
    Slates,
    Status,
    Mine(bool),
    Seed,
    /// A new key for spending policies: one-time, or a key tree of
    /// `2^height` leaves (`docs/CONTRACTS.md`; `contract`).
    ContractKey { height: usize },
    /// A fresh hash-lock preimage and its image.
    Hashlock,
    /// Pay `amount` (plus `fee`) into an output locked to the policy in
    /// `policy`.
    LockFunds { amount: u64, fee: u64, policy: PathBuf },
    /// Write an unsigned spend of a policy output (`amount`, locked to the
    /// policy in `policy`) by branch `branch`, paying `amount - fee` to
    /// this wallet or (`to`) another policy; a REBIND branch declares
    /// `state`.
    SpendPolicy { policy: PathBuf, branch: u32, amount: u64, to: Option<PathBuf>, fee: u64, state: u32, preimage: Option<[u8; 32]>, out: Option<PathBuf> },
    /// Sign a transaction file with this wallet's policy keys.
    SignFile { file: PathBuf },
    /// Add a fee input (and change) from the wallet to a transaction file.
    AttachFee { file: PathBuf, fee: u64 },
    /// Re-point a transaction file's REBIND input at another output.
    Rebind { file: PathBuf, policy: PathBuf, branch: u32, amount: u64 },
    /// Submit a transaction file.
    SubmitFile { file: PathBuf },
    /// Summarize a transaction file.
    Inspect { file: PathBuf },
    Quit,
}

/// What to print back: the text, or an error message.
pub type Reply = Result<String, String>;

/// A chain proof being made in the background: `None` while it's being
/// proven, then `Some(proof)` -- `Some(None)` if proving failed. Waited on
/// (the condvar) by whatever needs it.
type ChainProofSlot = Arc<(std::sync::Mutex<Option<Option<Vec<u8>>>>, std::sync::Condvar)>;

/// Wait for a chain proof job to finish; its proof, if it made one.
fn wait_for(slot: &ChainProofSlot) -> Option<Vec<u8>> {
    let (lock, ready) = &**slot;
    let mut state = lock.lock().unwrap();
    while state.is_none() {
        state = ready.wait(state).unwrap();
    }
    state.clone().unwrap()
}

enum Miner {
    Idle,
    Proving {
        unproven: UnprovenBlock,
        reward: [u8; 32],
        /// The block proof, and the parent's chain proof it carries.
        result: Receiver<Option<(prover::Proof, Vec<u8>)>>,
        started: Instant,
    },
    Mining {
        block: Block,
        target: [u8; 32],
        min_timestamp: u64,
        reward: [u8; 32],
        started: Instant,
        batches: u64,
    },
}

/// The largest share of a block template given to mempool transactions
/// (the 2 MB cap, less room for the commitments and proof).
const TEMPLATE_TX_BYTES: usize = 1 << 20;

pub struct Node {
    pub chain: Chain,
    pub reader: BlockReader,
    pub received: Receiver<(Block, SocketAddrV4)>,
    /// Transactions from peers (encoded), for the mempool to check.
    pub received_txs: Receiver<(Vec<u8>, SocketAddrV4)>,
    pub commands: Sender<Command>,
    pub peer_table: PeerTable,
    pub wallet: Wallet,
    pub mempool: Mempool,
    pub mining: bool,
    pub requests: Receiver<(Request, Sender<Reply>)>,
    /// The highest tip any peer has reported (`net::NO_PEER_HEIGHT`
    /// until one has), kept current by the network thread.
    pub peer_height: Arc<AtomicU64>,
    /// No seeds were given: this node may be the network's first, so
    /// with no peer heights known it counts as caught up.
    pub standalone: bool,
    /// Makes the chain proofs this node's blocks carry (`chain_step`):
    /// shared with the proving thread, which derives its keys once.
    pub chain_prover: Arc<std::sync::Mutex<crate::chain_step::ChainProver>>,
    /// Proving ahead: the chain proof of the tip, started the moment the
    /// tip moves (`prove_tip`) and made alongside the block proof -- by
    /// the block it attests. Every template on that tip reuses it.
    chain_job: Option<([u8; 32], ChainProofSlot)>,
    miner: Miner,
    last_balance: Option<wallet::Balance>,
    /// Build the next template without mempool transactions (after one
    /// with them failed to build or prove).
    skip_mempool: bool,
    /// The wallet is restored from backup words and waits for the chain
    /// to catch up before scanning it (`try_finish_recovery`); checked at
    /// most once per `RECOVERY_CHECK`.
    recovering: bool,
    next_recovery_check: Instant,
    /// Fast sync in progress (`fastsync`): blocks go to it, no mining.
    pub fast_sync: Option<crate::fastsync::FastSync>,
    /// Fast-sync events from the network.
    pub sync_events: Option<Receiver<crate::statesync::Event>>,
}

/// How often a recovering wallet checks whether the chain has caught up.
const RECOVERY_CHECK: Duration = Duration::from_secs(1);

impl Node {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        chain: Chain,
        reader: BlockReader,
        received: Receiver<(Block, SocketAddrV4)>,
        received_txs: Receiver<(Vec<u8>, SocketAddrV4)>,
        commands: Sender<Command>,
        peer_table: PeerTable,
        wallet: Wallet,
        mining: bool,
        requests: Receiver<(Request, Sender<Reply>)>,
    ) -> Self {
        let recovering = wallet.is_recovering().unwrap_or(false);
        Node {
            chain,
            reader,
            received,
            received_txs,
            commands,
            peer_table,
            wallet,
            mempool: Mempool::new(),
            mining,
            requests,
            peer_height: Arc::new(AtomicU64::new(crate::net::NO_PEER_HEIGHT)),
            standalone: false,
            chain_prover: Arc::new(std::sync::Mutex::new(crate::chain_step::ChainProver::new(
                crate::chain::DifficultyConfig::for_tests(),
                prover::tree(),
            ))),
            chain_job: None,
            miner: Miner::Idle,
            last_balance: None,
            skip_mempool: false,
            recovering,
            next_recovery_check: Instant::now(),
            fast_sync: None,
            sync_events: None,
        }
    }

    fn tip_height(&self) -> u64 {
        self.chain.view().map(|v| v.tip_height()).unwrap_or(0)
    }

    /// Run until a `Quit` request.
    pub fn run(mut self) {
        self.refresh_wallet();
        // Transactions we signed that haven't confirmed: back in the pool.
        match self.wallet.unconfirmed_transactions() {
            Ok(txs) => {
                for tx in txs {
                    self.submit(tx).ok();
                }
            }
            Err(e) => error!("wallet: {e}"),
        }
        info!("{}", if self.mining { "Mining." } else { "Not mining." });
        if self.recovering {
            info!("wallet: restored from backup words -- waiting for the chain to catch up with peers before scanning it");
        }
        loop {
            let mut busy = self.try_finish_recovery();
            while let Ok((request, reply)) = self.requests.try_recv() {
                busy = true;
                let quit = matches!(request, Request::Quit);
                let answer = self.handle(request);
                let _ = reply.send(answer);
                if quit {
                    info!("Shutting down.");
                    return;
                }
            }
            busy |= self.fast_sync_step();
            if self.process_received() {
                self.on_tip_moved();
            }
            busy |= self.process_received_txs();
            busy |= self.mine_step();
            if !busy {
                std::thread::sleep(Duration::from_millis(20));
            }
        }
    }

    // ---- recovery ---------------------------------------------------------

    /// Whether the chain has caught up with every peer that's told us its
    /// tip (or, with none and no seeds, whether we stand alone).
    fn caught_up(&self) -> bool {
        match self.peer_height.load(Ordering::Relaxed) {
            crate::net::NO_PEER_HEIGHT => self.standalone,
            best => self.tip_height() >= best,
        }
    }

    /// For a restored wallet: once the chain has caught up, scan it for
    /// our outputs (`Wallet::finish_recovery`). Returns whether it did.
    fn try_finish_recovery(&mut self) -> bool {
        if !self.recovering || Instant::now() < self.next_recovery_check {
            return false;
        }
        self.next_recovery_check = Instant::now() + RECOVERY_CHECK;
        if !self.caught_up() {
            return false;
        }
        let result = match self.chain.view() {
            Ok(view) => self.wallet.finish_recovery(&view),
            Err(e) => {
                error!("wallet: failed to read the chain: {e}");
                return false;
            }
        };
        match result {
            Ok(r) => {
                self.recovering = false;
                info!(
                    "wallet: recovered {} output(s) at height {} -- {} unspent, {} in all; spendable from height {} (a hold in case a spend was in flight); new keys from index {}",
                    r.outputs,
                    self.tip_height(),
                    r.unspent,
                    format_amount(r.amount),
                    r.spendable_from,
                    r.next_index
                );
                self.last_balance = None;
                self.refresh_wallet();
                true
            }
            Err(e) => {
                error!("wallet: recovery failed: {e}");
                false
            }
        }
    }

    // ---- fast sync -------------------------------------------------------

    /// Move fast sync along, if it's running; whether anything happened.
    fn fast_sync_step(&mut self) -> bool {
        use crate::fastsync::Outcome;
        let Some(fast_sync) = self.fast_sync.as_mut() else {
            return false;
        };
        let mut busy = false;
        let mut outcome = Outcome::Running;
        if let Some(events) = &self.sync_events {
            while let Ok(event) = events.try_recv() {
                busy = true;
                outcome = fast_sync.on_event(event, &mut self.chain, &self.commands);
                if !matches!(outcome, Outcome::Running) {
                    break;
                }
            }
        }
        if matches!(outcome, Outcome::Running) {
            let best = match self.peer_height.load(Ordering::Relaxed) {
                crate::net::NO_PEER_HEIGHT => None,
                best => Some(best),
            };
            outcome = fast_sync.step(best, self.standalone, &self.commands);
        }
        match outcome {
            Outcome::Running => busy,
            Outcome::Done(next) => {
                self.fast_sync = None;
                let unknown = SocketAddrV4::new(std::net::Ipv4Addr::UNSPECIFIED, 0);
                crate::process_one(&mut self.chain, &self.reader, &self.commands, *next, unknown);
                self.on_tip_moved();
                true
            }
            Outcome::Abandoned => {
                self.fast_sync = None;
                true
            }
        }
    }

    // ---- chain events ---------------------------------------------------

    /// Hand every block the network has received so far to the chain --
    /// or, during a fast sync, to it. Returns whether the tip moved.
    fn process_received(&mut self) -> bool {
        let mut moved = false;
        while let Ok((block, from)) = self.received.try_recv() {
            match self.fast_sync.as_mut() {
                Some(fast_sync) => fast_sync.on_block(block, &self.commands),
                None => moved |= crate::process_one(&mut self.chain, &self.reader, &self.commands, block, from),
            }
        }
        moved
    }

    /// Check transactions from peers against the mempool; accepted ones
    /// are relayed onward. Returns whether there were any.
    fn process_received_txs(&mut self) -> bool {
        let mut any = false;
        while let Ok((bytes, from)) = self.received_txs.try_recv() {
            any = true;
            let Some(tx) = Transaction::from_bytes(&bytes) else {
                debug!("undecodable transaction from {from}");
                continue;
            };
            match self.submit_from(tx, Some(from)) {
                Ok(_) | Err(Rejection::AlreadyKnown) => {}
                Err(e) => debug!("transaction from {from} not accepted: {e}"),
            }
        }
        any
    }

    /// After any change to the active chain: wallet and mempool up to date,
    /// and a template on the old tip dropped.
    fn on_tip_moved(&mut self) {
        self.refresh_wallet();
        if let Ok(view) = self.chain.view() {
            let dropped = self.mempool.revalidate(&view);
            if !dropped.is_empty() {
                info!("mempool: {} transaction(s) mined or no longer valid; {} waiting", dropped.len(), self.mempool.len());
            }
            for id in dropped {
                let _ = self.commands.send(Command::ForgetTx { id });
            }
        }
        self.prove_tip();
        let tip = self.reader.tip().ok().flatten().map(|(_, hash)| hash);
        let stale = match &self.miner {
            Miner::Proving { unproven, .. } => Some(unproven.prev_hash) != tip,
            Miner::Mining { block, .. } => Some(block.header.prev_hash) != tip,
            Miner::Idle => false,
        };
        if stale {
            debug!("the tip moved: abandoning the block template");
            self.abandon_template();
        }
    }

    fn refresh_wallet(&mut self) {
        let view = match self.chain.view() {
            Ok(view) => view,
            Err(e) => return error!("wallet: failed to read the chain: {e}"),
        };
        match self.wallet.refresh(&view) {
            Ok(unrecoverable) => {
                for commitment in unrecoverable {
                    warn!(
                        "wallet: output {} confirmed, but its recovery nonce was altered on the way -- \
                         the backup words can't restore it; keep this wallet's files until it's spent",
                        crate::hex(&commitment[..8])
                    );
                }
            }
            Err(e) => return error!("wallet: refresh failed: {e}"),
        }
        match self.wallet.balance(view.tip_height()) {
            Ok(b) if self.last_balance != Some(b) => {
                let held = if b.held > 0 {
                    format!(", held {} (recovered, until height {})", format_amount(b.held), b.held_until)
                } else {
                    String::new()
                };
                info!(
                    "wallet: spendable {}, immature {}, pending {}, locked {}{held}",
                    format_amount(b.spendable),
                    format_amount(b.immature),
                    format_amount(b.pending),
                    format_amount(b.locked)
                );
                self.last_balance = Some(b);
            }
            Ok(_) => {}
            Err(e) => error!("wallet: {e}"),
        }
    }

    /// Put one of our own transactions in the mempool, and announce it.
    fn submit(&mut self, tx: Transaction) -> Result<[u8; 32], Rejection> {
        self.submit_from(tx, None)
    }

    /// Put a transaction in the mempool (for the next block template) and
    /// relay it to every peer but `from`, the one that sent it.
    fn submit_from(&mut self, tx: Transaction, from: Option<SocketAddrV4>) -> Result<[u8; 32], Rejection> {
        let bytes = tx.to_bytes();
        let tx_copy = tx.clone();
        let view = self.chain.view().map_err(|_| Rejection::Invalid("the chain is unreadable"))?;
        let id = self.mempool.admit(tx, &view)?;
        drop(view);
        // A spend of one of our outputs we didn't sign here (a restored
        // wallet's in-flight spend, or a copy of this wallet): never sign
        // that output again.
        match self.wallet.observe_spend(&tx_copy) {
            Ok(true) => warn!("wallet: transaction {} spends outputs of ours signed elsewhere; marked as spent", crate::hex(&id[..8])),
            Ok(false) => {}
            Err(e) => error!("wallet: {e}"),
        }
        let source = from.map_or("this wallet".to_string(), |f| f.to_string());
        info!("mempool: accepted {} from {source}; {} waiting", crate::hex(&id[..8]), self.mempool.len());
        let _ = self.commands.send(Command::AnnounceTx { bytes, except: from });
        Ok(id)
    }

    // ---- mining ---------------------------------------------------------

    fn abandon_template(&mut self) {
        let reward = match std::mem::replace(&mut self.miner, Miner::Idle) {
            Miner::Proving { reward, .. } | Miner::Mining { reward, .. } => reward,
            Miner::Idle => return,
        };
        if let Err(e) = self.wallet.forget(&reward) {
            error!("wallet: {e}");
        }
    }

    /// One step of the mining state machine; whether it did any work.
    fn mine_step(&mut self) -> bool {
        match &mut self.miner {
            Miner::Idle => {
                // A recovering wallet hands out no keys, rewards included;
                // a fast-syncing node has no tip to mine on yet.
                if !self.mining || self.recovering || self.fast_sync.is_some() {
                    return false;
                }
                self.start_template();
                true
            }
            Miner::Proving { result, .. } => match result.try_recv() {
                Err(TryRecvError::Empty) => false,
                Ok(Some((proof, chain_proof))) => {
                    let Miner::Proving {
                        unproven,
                        reward,
                        started,
                        ..
                    } = std::mem::replace(&mut self.miner, Miner::Idle)
                    else {
                        unreachable!()
                    };
                    debug!("proved block #{} in {:.2?}", unproven.height, started.elapsed());
                    let (target, min_timestamp) = (unproven.target, unproven.min_timestamp);
                    self.miner = Miner::Mining {
                        block: unproven.finish_with_chain_proof(proof, chain_proof),
                        target,
                        min_timestamp,
                        reward,
                        started: Instant::now(),
                        batches: 0,
                    };
                    true
                }
                Ok(None) | Err(TryRecvError::Disconnected) => {
                    error!("proving the block template failed; the next one leaves out the mempool");
                    self.skip_mempool = true;
                    self.abandon_template();
                    true
                }
            },
            Miner::Mining {
                block,
                target,
                min_timestamp,
                batches,
                ..
            } => {
                if !mine_block(block, target, crate::MINE_BATCH, &self.chain.pow_params()) {
                    *batches += 1;
                    // A fresh timestamp opens a fresh nonce space.
                    block.header.timestamp = now_millis().max(*min_timestamp);
                    return true;
                }
                let Miner::Mining {
                    block,
                    target,
                    started,
                    batches,
                    ..
                } = std::mem::replace(&mut self.miner, Miner::Idle)
                else {
                    unreachable!()
                };
                self.mined(block, target, started.elapsed(), batches);
                true
            }
        }
    }

    /// Build a block template and start proving it on a worker thread.
    /// Proving ahead: make sure the chain proof of the current tip is made
    /// or being made, in the background, if this node mines -- started
    /// the moment the tip moves, so it's done (or nearly) by the time the
    /// next block's own proof is. The tip and its job.
    fn prove_tip(&mut self) -> Option<([u8; 32], ChainProofSlot)> {
        if !self.mining || self.recovering || self.fast_sync.is_some() {
            return None;
        }
        let tip = self.reader.tip().ok().flatten()?.1;
        if let Some((hash, slot)) = &self.chain_job
            && *hash == tip
            && !matches!(*slot.0.lock().unwrap(), Some(None))
        {
            return Some((tip, slot.clone())); // being made, or made: reused
        }
        let inputs = match self.chain.chain_proof_inputs(tip) {
            Ok(inputs) => inputs,
            Err(e) => {
                error!("can't gather the tip's chain proof inputs: {e}");
                return None;
            }
        };
        let second = self.reader.active_hash_at(1).ok().flatten().and_then(|h| self.chain.chain_proof_inputs(h).ok());
        let slot: ChainProofSlot = Arc::new((std::sync::Mutex::new(None), std::sync::Condvar::new()));
        let (job, chain_prover) = (slot.clone(), self.chain_prover.clone());
        std::thread::spawn(move || {
            // One at a time: a job for an earlier tip still running finishes
            // first (the prover's lock), rather than both at once.
            let mut chain_prover = chain_prover.lock().unwrap();
            let start = Instant::now();
            let made = match chain_prover.prove(&inputs, || second, crate::random_key()) {
                Ok(proof) if crate::chain_step::consensus_verifier().verify(&inputs.tip, &proof) => {
                    debug!("chain proof of block #{}: {:.2?}", inputs.tip.height, start.elapsed());
                    Some(proof)
                }
                Ok(_) => {
                    error!("the chain proof doesn't verify against this network's keys -- are the chain-proof constants stale?");
                    None
                }
                Err(e) => {
                    error!("proving the tip's chain proof failed: {e:?}");
                    None
                }
            };
            let (lock, ready) = &*job;
            *lock.lock().unwrap() = Some(made);
            ready.notify_all();
        });
        self.chain_job = Some((tip, slot.clone()));
        Some((tip, slot))
    }

    fn start_template(&mut self) {
        let (txs, fees) = if std::mem::take(&mut self.skip_mempool) {
            (Vec::new(), 0)
        } else {
            self.mempool.select(TEMPLATE_TX_BYTES)
        };
        let Some(subsidy) = prover::schedule().reward(self.tip_height() + 1) else {
            error!("the chain has reached its end height: no further block can be mined");
            self.mining = false;
            return;
        };
        let (_, reward) = match self.wallet.reward_output(subsidy + fees) {
            Ok(r) => r,
            Err(e) => {
                error!("wallet: failed to make a reward output: {e}");
                self.mining = false;
                return;
            }
        };
        let mut reward_tx = Transaction::new();
        reward_tx.add_output(reward).expect("fresh transaction never finalized");
        let count = txs.len();
        let transactions: Vec<Transaction> = std::iter::once(reward_tx).chain(txs).collect();
        let unproven = match self.chain.build_block(&transactions) {
            Ok(u) => u,
            Err(e) => {
                error!("failed to build a block template: {e}; the next one leaves out the mempool");
                let _ = self.wallet.forget(&reward.commitment());
                self.skip_mempool = true;
                return;
            }
        };
        if count > 0 {
            info!(
                "block template #{}: {count} transaction(s), fees {} -- proving{}",
                unproven.height,
                format_amount(fees),
                if unproven.plan.chunks.len() > 1 { format!(" ({} chunks: this takes a while)", unproven.plan.chunks.len()) } else { String::new() }
            );
        }
        let (inputs, outputs, nonces, plan) = (unproven.inputs.clone(), unproven.outputs.clone(), unproven.nonces.clone(), unproven.plan.clone());
        // The parent's chain proof is (normally) already being made; the
        // block proof runs alongside it, and mining waits for both.
        let Some(slot) = self.prove_tip().filter(|(hash, _)| *hash == unproven.prev_hash).map(|(_, slot)| slot) else {
            self.abandon_template();
            return;
        };
        let (send, result) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let start = Instant::now();
            let block = prover::prove_block(&inputs, &outputs, &nonces, &transactions, &plan, crate::random_key());
            debug!("block proof: {:.2?}", start.elapsed());
            let both = block.and_then(|proof| {
                let waited = Instant::now();
                let chain_proof = wait_for(&slot)?;
                if waited.elapsed() > Duration::from_millis(500) {
                    debug!("waited {:.2?} for the parent's chain proof", waited.elapsed());
                }
                Some((proof, chain_proof))
            });
            let _ = send.send(both);
        });
        self.miner = Miner::Proving {
            unproven,
            reward: reward.commitment(),
            result,
            started: Instant::now(),
        };
    }

    fn mined(&mut self, block: Block, target: [u8; 32], elapsed: Duration, batches: u64) {
        // `pow::mine` counts nonces up from 0 in the nonce's first 8 bytes,
        // so the winning nonce says how many tries the last batch took.
        let last_batch = u64::from_le_bytes(block.header.nonce[..8].try_into().unwrap()) + 1;
        let hashes = batches * crate::MINE_BATCH + last_batch;
        match self.chain.accept_block(block.clone()) {
            Ok(AcceptOutcome::Applied) => {
                crate::print_block(&block);
                crate::print_mining_stats(hashes, elapsed, &target);
                if let Ok(hosts) = self.peer_table.all() {
                    let answering = hosts.iter().filter(|(_, record)| record.is_answering()).count();
                    info!("  peers:       {answering} answering, {} known", hosts.len());
                }
                crate::announce_tip(&self.reader, &self.commands, None);
            }
            other => info!("mined block #{} was not applied: {other:?}", block.header.height),
        }
        self.on_tip_moved();
    }

    // ---- requests -------------------------------------------------------

    fn handle(&mut self, request: Request) -> Reply {
        let tip = self.tip_height();
        match request {
            Request::Balance => {
                let b = self.wallet.balance(tip).map_err(|e| e.to_string())?;
                let held = if b.held > 0 {
                    format!(
                        "held:      {}  (recovered; spendable from height {}, in case the lost wallet's last spend is still in flight)\n",
                        format_amount(b.held),
                        b.held_until
                    )
                } else {
                    String::new()
                };
                Ok(format!(
                    "spendable: {}\nimmature:  {}  (mining rewards need {} confirmations)\npending:   {}\nlocked:    {}\n{held}total:     {}",
                    format_amount(b.spendable),
                    format_amount(b.immature),
                    wallet::coinbase_maturity(),
                    format_amount(b.pending),
                    format_amount(b.locked),
                    format_amount(b.total())
                ))
            }
            Request::Outputs => {
                let mut outputs = self.wallet.outputs().map_err(|e| e.to_string())?;
                // Not spent, and not the reward of a block still being mined.
                outputs.retain(|o| {
                    let status = o.status(tip);
                    status != wallet::Status::Spent && !(status == wallet::Status::Pending && o.origin == wallet::Origin::Mined)
                });
                outputs.sort_by_key(|o| (o.seen_height.unwrap_or(u64::MAX), o.key.index));
                if outputs.is_empty() {
                    return Ok("no outputs".into());
                }
                let lines: Vec<String> = outputs
                    .iter()
                    .map(|o| {
                        let status = match o.status(tip) {
                            wallet::Status::Pending => "pending".to_string(),
                            wallet::Status::Confirmed { confirmations, mature } => {
                                format!("{confirmations} conf{}", if mature { "" } else { ", immature" })
                            }
                            wallet::Status::Locked => "locked".into(),
                            wallet::Status::Spending => "spending".into(),
                            wallet::Status::Spent => "spent".into(),
                            wallet::Status::Held { confirmations, until } => format!("{confirmations} conf, held to {until}"),
                        };
                        format!("{:>22}  {:<20} {:?} {}", format_amount(o.amount), status, o.origin, crate::hex(&o.commitment[..8]))
                    })
                    .collect();
                Ok(lines.join("\n"))
            }
            Request::ContractKey { height } => {
                let id = self.wallet.new_contract_key(height).map_err(|e| e.to_string())?;
                let kind = if height == 0 { "a one-time key (signs once)".to_string() } else { format!("a key tree of {} signatures", 1u64 << height) };
                Ok(format!("key {}\n{kind} -- list it in a policy's `keys=`", crate::hex(&id)))
            }
            Request::Hashlock => {
                let preimage = crate::poseidon2::hash_bytes_32(&crate::keychain::random_bytes());
                let image = crate::policy::hashlock(&preimage).ok_or("preimage generation failed")?;
                Ok(format!(
                    "preimage {}\nimage    {}\n(the image goes in a policy's `hashlock=`; keep the preimage secret until it's spent)",
                    crate::hex(&preimage),
                    crate::hex(&image)
                ))
            }
            Request::LockFunds { amount, fee, policy } => {
                let policy = crate::contract::read_policy(&policy)?;
                let tx = self.wallet.lock_funds(policy.lock(), amount, fee, tip).map_err(|e| e.to_string())?;
                let output = crate::output::Output::locked(policy.lock(), amount).commitment();
                self.submit(tx).map_err(|e| format!("signed, but not accepted: {e}"))?;
                Ok(format!("submitted: {} locked to the policy (output {})", format_amount(amount), crate::hex(&output[..8])))
            }
            Request::SpendPolicy { policy, branch, amount, to, fee, state, preimage, out } => {
                let policy = crate::contract::read_policy(&policy)?;
                let b = policy.branches.get(branch as usize).ok_or("no such branch (they're numbered from 0)")?.clone();
                let paid = amount.checked_sub(fee).filter(|&p| p > 0).ok_or("the fee must be less than the amount")?;
                if let Some(s) = b.rebind
                    && state <= s
                {
                    return Err(format!("a REBIND branch at state {s} needs a higher state= declared"));
                }
                let output = match &to {
                    None => self.wallet.fresh_output(paid).map_err(|e| e.to_string())?,
                    Some(file) => crate::output::Output::locked(crate::contract::read_policy(file)?.lock(), paid),
                };
                let path = policy.path(branch).iter().map(|h| crate::poseidon2::digest_to_bytes(*h)).collect();
                let mut tx = Transaction::new();
                let named = if b.rebind.is_some() { vec![output.commitment()] } else { Vec::new() };
                let state = if b.rebind.is_some() { state } else { 0 };
                tx.add_rebind_input(b, branch, path, preimage, amount, state, named).map_err(|e| e.to_string())?;
                tx.add_output(output).map_err(|e| e.to_string())?;
                let file = out.unwrap_or_else(|| PathBuf::from(format!("{}.tx", crate::hex(&tx.inputs[0].commitment()[..8]))));
                crate::contract::write_transaction(&tx, &file)?;
                Ok(format!("wrote {} -- each signer runs `sign` on it, then `submit` it\n{}", file.display(), crate::contract::describe(&tx).trim_end()))
            }
            Request::SignFile { file } => {
                let mut tx = crate::contract::read_transaction(&file)?;
                let added = self.wallet.sign_contract(&mut tx).map_err(|e| e.to_string())?;
                crate::contract::write_transaction(&tx, &file)?;
                Ok(format!("added {added} signature(s) to {}\n{}", file.display(), crate::contract::describe(&tx).trim_end()))
            }
            Request::AttachFee { file, fee } => {
                let tx = crate::contract::read_transaction(&file)?;
                let tx = self.wallet.attach_fee(tx, fee, tip).map_err(|e| e.to_string())?;
                crate::contract::write_transaction(&tx, &file)?;
                Ok(format!("added a fee of {} to {}\n{}", format_amount(fee), file.display(), crate::contract::describe(&tx).trim_end()))
            }
            Request::Rebind { file, policy, branch, amount } => {
                let mut tx = crate::contract::read_transaction(&file)?;
                let policy = crate::contract::read_policy(&policy)?;
                let b = policy.branches.get(branch as usize).ok_or("no such branch (they're numbered from 0)")?.clone();
                let current = tx.inputs.iter().find(|i| i.rebinds()).ok_or("the transaction has no REBIND input")?.commitment();
                let path = policy.path(branch).iter().map(|h| crate::poseidon2::digest_to_bytes(*h)).collect();
                if !tx.rebind(&current, b, branch, path, amount) {
                    return Err("can't re-point it: it already has an ordinary signature (re-point before `fee`)".into());
                }
                crate::contract::write_transaction(&tx, &file)?;
                Ok(format!("re-pointed {}\n{}", file.display(), crate::contract::describe(&tx).trim_end()))
            }
            Request::SubmitFile { file } => {
                let tx = crate::contract::read_transaction(&file)?;
                if !tx.verify() {
                    return Err("not fully signed yet (see `inspect`)".into());
                }
                let id = tx.id();
                match self.submit(tx) {
                    Ok(_) | Err(Rejection::AlreadyKnown) => Ok(format!("submitted: transaction {}", crate::hex(&id[..8]))),
                    Err(e) => Err(format!("not accepted: {e}")),
                }
            }
            Request::Inspect { file } => Ok(crate::contract::describe(&crate::contract::read_transaction(&file)?).trim_end().to_string()),
            Request::Send { amount, fee, file } => {
                let slate = self.wallet.send(amount, fee, tip).map_err(|e| e.to_string())?;
                let path = file.unwrap_or_else(|| PathBuf::from(format!("{}.s1.slate", slate.id_hex())));
                // The wallet already locked the inputs. Without the file
                // nobody can answer the slate, so undo it (nothing was
                // signed) rather than leave them locked.
                if let Err(e) = slate.write_file(&path) {
                    let undone = self.wallet.cancel(&slate.id);
                    warn!("wallet: couldn't write slate {} to {}: {e}; cancelled: {undone:?}", slate.id_hex(), path.display());
                    return Err(format!("couldn't write {}: {e} -- nothing was sent, the funds are free again", path.display()));
                }
                info!("wallet: sending {} (fee {}), slate {}", format_amount(amount), format_amount(fee), slate.id_hex());
                Ok(format!(
                    "wrote {} -- give it to the receiver, then `finalize` the file they send back\n(the inputs stay locked until then; `cancel {}` to undo)",
                    path.display(),
                    slate.id_hex()
                ))
            }
            Request::Receive { file } => {
                let s1 = Slate::read_file(&file).map_err(|e| e.to_string())?;
                let s2 = self.wallet.receive(&s1).map_err(|e| e.to_string())?;
                let path = PathBuf::from(format!("{}.s2.slate", s2.id_hex()));
                s2.write_file(&path).map_err(|e| e.to_string())?;
                info!("wallet: receiving {}, slate {}", format_amount(s2.amount), s2.id_hex());
                Ok(format!(
                    "receiving {}: wrote {} -- give it back to the sender",
                    format_amount(s2.amount),
                    path.display()
                ))
            }
            Request::Finalize { file } => {
                let s2 = Slate::read_file(&file).map_err(|e| e.to_string())?;
                let tx = self.wallet.finalize(&s2).map_err(|e| e.to_string())?;
                let id = tx.id();
                match self.submit(tx) {
                    Ok(_) | Err(Rejection::AlreadyKnown) => Ok(format!(
                        "signed and submitted: transaction {} (in the mempool, and relayed to peers)",
                        crate::hex(&id[..8])
                    )),
                    Err(e) => Err(format!("signed, but not accepted: {e}")),
                }
            }
            Request::Cancel { id } => {
                self.wallet.cancel(&id).map_err(|e| e.to_string())?;
                Ok("cancelled: its inputs are spendable again".into())
            }
            Request::Slates => {
                let slates = self.wallet.slates().map_err(|e| e.to_string())?;
                if slates.is_empty() {
                    return Ok("no slates".into());
                }
                Ok(slates
                    .iter()
                    .map(|r| format!("{}  {:?} {:?}  {}", r.slate.id_hex(), r.role, r.state, format_amount(r.slate.amount)))
                    .collect::<Vec<_>>()
                    .join("\n"))
            }
            Request::Status => {
                let tip_hash = self.reader.tip().ok().flatten().map(|(_, h)| crate::hex(&h[..8])).unwrap_or_default();
                let hosts = self.peer_table.all().unwrap_or_default();
                let answering = hosts.iter().filter(|(_, record)| record.is_answering()).count();
                let peers = format!("{answering} ({} known)", hosts.len());
                let miner = match (&self.miner, self.mining) {
                    (_, false) => "off".to_string(),
                    (Miner::Idle, true) => "starting".into(),
                    (Miner::Proving { started, .. }, true) => format!("proving ({:.0?})", started.elapsed()),
                    (Miner::Mining { started, .. }, true) => format!("mining ({:.0?})", started.elapsed()),
                };
                let mut out = format!(
                    "height:  {tip} ({tip_hash}…)\npeers:   {peers}\nmempool: {} transaction(s)\nmining:  {miner}",
                    self.mempool.len()
                );
                if let Some(fast_sync) = &self.fast_sync {
                    out += &format!("\nsync:    fast sync -- {}", fast_sync.describe());
                }
                if self.recovering {
                    let best = match self.peer_height.load(Ordering::Relaxed) {
                        crate::net::NO_PEER_HEIGHT => "no peer has reported its height yet".to_string(),
                        best => format!("peers are at height {best}"),
                    };
                    out += &format!("\nwallet:  recovering -- scans the chain once it has caught up ({best})");
                }
                Ok(out)
            }
            Request::Mine(on) => {
                self.mining = on;
                if !on {
                    self.abandon_template();
                }
                info!("mining {}", if on { "on" } else { "off" });
                Ok(format!("mining {}", if on { "on" } else { "off" }))
            }
            Request::Seed => {
                let (words, passphrase) = self.wallet.backup_words().map_err(|e| e.to_string())?;
                let reminder = if passphrase {
                    "\nThis wallet also has a passphrase: restoring it takes the words AND the passphrase.\nWithout the passphrase the words restore an empty wallet."
                } else {
                    ""
                };
                Ok(format!(
                    "{}\nThese 24 words are this wallet's backup: write them down, in order, and keep them\nsecret -- anyone who has them can spend everything in it.{reminder}",
                    crate::mnemonic::display(&words)
                ))
            }
            Request::Quit => Ok("bye".into()),
        }
    }
}
