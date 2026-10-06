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
    Quit,
}

/// What to print back: the text, or an error message.
pub type Reply = Result<String, String>;

enum Miner {
    Idle,
    Proving {
        unproven: UnprovenBlock,
        reward: [u8; 32],
        result: Receiver<Option<prover::Proof>>,
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
    miner: Miner,
    last_balance: Option<wallet::Balance>,
    /// Build the next template without mempool transactions (after one
    /// with them failed to build or prove).
    skip_mempool: bool,
}

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
            miner: Miner::Idle,
            last_balance: None,
            skip_mempool: false,
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
        loop {
            let mut busy = false;
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

    // ---- chain events ---------------------------------------------------

    /// Hand every block the network has received so far to the chain.
    /// Returns whether the tip moved.
    fn process_received(&mut self) -> bool {
        let mut moved = false;
        while let Ok((block, from)) = self.received.try_recv() {
            moved |= crate::process_one(&mut self.chain, &self.reader, &self.commands, block, from);
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
        if let Err(e) = self.wallet.refresh(&view) {
            return error!("wallet: refresh failed: {e}");
        }
        match self.wallet.balance(view.tip_height()) {
            Ok(b) if self.last_balance != Some(b) => {
                info!(
                    "wallet: spendable {}, immature {}, pending {}, locked {}",
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
        let view = self.chain.view().map_err(|_| Rejection::Invalid("the chain is unreadable"))?;
        let id = self.mempool.admit(tx, &view)?;
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
                if !self.mining {
                    return false;
                }
                self.start_template();
                true
            }
            Miner::Proving { result, .. } => match result.try_recv() {
                Err(TryRecvError::Empty) => false,
                Ok(Some(proof)) => {
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
                        block: unproven.finish(proof),
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
                if !mine_block(block, target, crate::MINE_BATCH) {
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
    fn start_template(&mut self) {
        let (txs, fees) = if std::mem::take(&mut self.skip_mempool) {
            (Vec::new(), 0)
        } else {
            self.mempool.select(TEMPLATE_TX_BYTES)
        };
        let (_, reward) = match self.wallet.reward_output(prover::REWARD + fees) {
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
                if unproven.inputs.len() > prover::CHUNK_SHAPE.inputs { " (tree proof: this takes a while)" } else { "" }
            );
        }
        let (inputs, outputs) = (unproven.inputs.clone(), unproven.outputs.clone());
        let (send, result) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let proof = prover::prove_block_auto(&inputs, &outputs, &transactions, crate::random_key());
            let _ = send.send(proof);
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
                    let verified = hosts.iter().filter(|(_, record)| record.is_verified()).count();
                    info!("  peers:       {} known, {verified} verified", hosts.len());
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
                Ok(format!(
                    "spendable: {}\nimmature:  {}  (mining rewards need {} confirmations)\npending:   {}\nlocked:    {}\ntotal:     {}",
                    format_amount(b.spendable),
                    format_amount(b.immature),
                    wallet::COINBASE_MATURITY,
                    format_amount(b.pending),
                    format_amount(b.locked),
                    format_amount(b.spendable + b.immature + b.pending + b.locked)
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
                        };
                        format!("{:>22}  {:<20} {:?} {}", format_amount(o.amount), status, o.origin, crate::hex(&o.commitment[..8]))
                    })
                    .collect();
                Ok(lines.join("\n"))
            }
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
                let peers = self.peer_table.all().map(|h| h.len()).unwrap_or(0);
                let miner = match (&self.miner, self.mining) {
                    (_, false) => "off".to_string(),
                    (Miner::Idle, true) => "starting".into(),
                    (Miner::Proving { started, .. }, true) => format!("proving ({:.0?})", started.elapsed()),
                    (Miner::Mining { started, .. }, true) => format!("mining ({:.0?})", started.elapsed()),
                };
                Ok(format!(
                    "height:  {tip} ({tip_hash}…)\npeers:   {peers}\nmempool: {} transaction(s)\nmining:  {miner}",
                    self.mempool.len()
                ))
            }
            Request::Mine(on) => {
                self.mining = on;
                if !on {
                    self.abandon_template();
                }
                info!("mining {}", if on { "on" } else { "off" });
                Ok(format!("mining {}", if on { "on" } else { "off" }))
            }
            Request::Seed => Ok(format!(
                "{}\nAnyone with this seed can spend everything in this wallet. Keep it secret.",
                self.wallet.keychain().seed_hex()
            )),
            Request::Quit => Ok("bye".into()),
        }
    }
}
