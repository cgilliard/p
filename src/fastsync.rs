//! Fast sync, as the node runs it (`docs/CHAIN_RECURSION.md`, 5d): a node
//! starting with nothing but the genesis block starts at a recent block H
//! instead of replaying the whole chain.
//!
//! 1. **Pick H.** Once peers have reported their heights, H is the best
//!    one less `depth` (blocks after H are then replayed in full, which
//!    is also how far back this node can reorg at first). A chain no
//!    longer than `depth` + 1 is just synced block by block.
//! 2. **Blocks H and H+1** from the peer furthest ahead. Block H+1 carries
//!    the chain proof of H: everything from genesis to H valid.
//! 3. **H's sync point** -- the target, window start and work after it --
//!    from any peer; believed once the chain proof verifies against it.
//! 4. **The state as of H** (`statesync`), from every peer, each piece
//!    checked against the state root the chain proof attests.
//! 5. **Start there** (`Chain::import_snapshot`), apply H+1, and catch up
//!    block by block -- every block from there validated in full.
//!
//! Catching up block by block is paused throughout, so nothing else gets
//! applied first. Each step is asked again if it gets no answer.

use std::sync::mpsc::Sender;
use std::time::{Duration, Instant};

use crate::block::Block;
use crate::chain::Chain;
use crate::net::Command;
use crate::snapshot::SyncPoint;
use crate::statesync::Event;

/// How long a step waits for an answer before asking again.
const RETRY: Duration = Duration::from_secs(10);
/// How long the state download may take before it's started over, at a
/// newer H.
const STATE_TIMEOUT: Duration = Duration::from_secs(30 * 60);
/// With no seeds, how long to wait for a peer before syncing (from
/// nothing) block by block -- this may be the network's first node.
const ALONE: Duration = Duration::from_secs(5);

enum Phase {
    /// Waiting to hear peers' heights.
    Waiting,
    Blocks { height: u64, base: Option<Block>, next: Option<Block> },
    Point { base: Block, next: Block },
    State { base: Block, next: Block, point: SyncPoint },
}

/// What a step came to.
pub enum Outcome {
    /// Still going.
    Running,
    /// Started at H: the block after it, to accept as usual.
    Done(Box<Block>),
    /// Not worth it (a short chain, or no peers): sync block by block.
    Abandoned,
}

pub struct FastSync {
    depth: u64,
    phase: Phase,
    /// When the current phase started, or last asked again.
    asked: Instant,
    started: Instant,
}

impl FastSync {
    /// Start: pauses block-by-block syncing.
    pub fn new(depth: u64, commands: &Sender<Command>) -> Self {
        let _ = commands.send(Command::PauseBlockSync(true));
        info!("fast sync: waiting for peers' heights");
        FastSync {
            depth,
            phase: Phase::Waiting,
            asked: Instant::now(),
            started: Instant::now(),
        }
    }

    /// One line for `status`.
    pub fn describe(&self) -> String {
        match &self.phase {
            Phase::Waiting => "waiting for peers' heights".into(),
            Phase::Blocks { height, .. } => format!("fetching blocks {height} and {}", height + 1),
            Phase::Point { base, .. } => format!("checking block {}'s chain proof", base.header.height),
            Phase::State { base, .. } => format!("downloading the state as of block {} ({:.0?})", base.header.height, self.started.elapsed()),
        }
    }

    fn restart(&mut self, commands: &Sender<Command>) {
        let _ = commands.send(Command::StopStateSync);
        self.phase = Phase::Waiting;
        self.asked = Instant::now();
    }

    /// Move along, given the best height peers report (if any has) and
    /// whether this node has no seeds.
    pub fn step(&mut self, peer_height: Option<u64>, standalone: bool, commands: &Sender<Command>) -> Outcome {
        let stale = self.asked.elapsed() >= RETRY;
        match &mut self.phase {
            Phase::Waiting => match peer_height {
                None if standalone && self.asked.elapsed() >= ALONE => return self.abandon(commands, "no peers"),
                None => {}
                Some(best) if best <= self.depth + 1 => {
                    return self.abandon(commands, &format!("the chain is short ({best} blocks)"));
                }
                Some(best) => {
                    let height = best - self.depth;
                    info!("fast sync: peers are at height {best}; starting at block {height}");
                    let _ = commands.send(Command::FetchHeight(height));
                    let _ = commands.send(Command::FetchHeight(height + 1));
                    self.phase = Phase::Blocks { height, base: None, next: None };
                    self.asked = Instant::now();
                    self.started = Instant::now();
                }
            },
            Phase::Blocks { height, base, next } if stale => {
                for (h, have) in [(*height, base.is_some()), (*height + 1, next.is_some())] {
                    if !have {
                        let _ = commands.send(Command::FetchHeight(h));
                    }
                }
                self.asked = Instant::now();
            }
            Phase::Point { base, .. } if stale => {
                let _ = commands.send(Command::RequestSyncPoint(base.header.hash()));
                self.asked = Instant::now();
            }
            Phase::State { .. } if self.started.elapsed() >= STATE_TIMEOUT => {
                warn!("fast sync: the state download is taking too long -- starting over");
                self.restart(commands);
            }
            _ => {}
        }
        Outcome::Running
    }

    fn abandon(&mut self, commands: &Sender<Command>, why: &str) -> Outcome {
        info!("fast sync: not needed ({why}) -- syncing block by block");
        let _ = commands.send(Command::PauseBlockSync(false));
        Outcome::Abandoned
    }

    /// A block downloaded while syncing: taken if it's one of H, H+1.
    pub fn on_block(&mut self, block: Block, commands: &Sender<Command>) {
        let Phase::Blocks { height, base, next } = &mut self.phase else {
            return;
        };
        if block.header.height == *height {
            *base = Some(block);
        } else if block.header.height == *height + 1 {
            *next = Some(block);
        } else {
            return;
        }
        let (Some(b), Some(n)) = (base.as_ref(), next.as_ref()) else {
            return;
        };
        if n.header.prev_hash != b.header.hash() {
            // From different branches (a peer reorged meanwhile): again.
            let height = *height;
            *base = None;
            *next = None;
            let _ = commands.send(Command::FetchHeight(height));
            let _ = commands.send(Command::FetchHeight(height + 1));
            return;
        }
        let (base, next) = (base.take().unwrap(), next.take().unwrap());
        let _ = commands.send(Command::RequestSyncPoint(base.header.hash()));
        self.phase = Phase::Point { base, next };
        self.asked = Instant::now();
    }

    /// A fast-sync event from the network.
    pub fn on_event(&mut self, event: Event, chain: &mut Chain, commands: &Sender<Command>) -> Outcome {
        match (event, &mut self.phase) {
            (Event::Point { hash, point, from }, Phase::Point { base, next }) if hash == base.header.hash() => {
                if let Err(e) = chain.check_sync_point(base, &point, &next.body.chain_proof) {
                    warn!("fast sync: {from}'s sync point for block {}: {e}", base.header.height);
                    return Outcome::Running;
                }
                info!(
                    "fast sync: block {}'s chain proof verifies -- downloading the state as of it ({} outputs ever)",
                    base.header.height, base.header.output_count
                );
                let _ = commands.send(Command::SyncState {
                    at: hash,
                    root: base.header.state_root,
                    count: base.header.output_count,
                });
                let Phase::Point { base, next } = std::mem::replace(&mut self.phase, Phase::Waiting) else {
                    unreachable!()
                };
                self.phase = Phase::State { base, next, point };
                self.started = Instant::now();
            }
            (Event::State(unspent), Phase::State { base, next, point }) => {
                let found = unspent.len();
                match chain.import_snapshot(base, point, &next.body.chain_proof, &unspent) {
                    Ok(()) => {
                        info!(
                            "fast sync: started at block {} with {found} unspent outputs (state downloaded in {:.1?}) -- catching up from there",
                            base.header.height,
                            self.started.elapsed()
                        );
                        let _ = commands.send(Command::PauseBlockSync(false));
                        let Phase::State { next, .. } = std::mem::replace(&mut self.phase, Phase::Waiting) else {
                            unreachable!()
                        };
                        return Outcome::Done(Box::new(next));
                    }
                    Err(e) => {
                        error!("fast sync: the downloaded state was refused: {e} -- starting over");
                        self.restart(commands);
                    }
                }
            }
            _ => {}
        }
        Outcome::Running
    }
}
