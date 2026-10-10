//! Moving blocks between peers over UDP, where a block (up to a couple
//! of megabytes) is far bigger than one packet.
//!
//! # Announce, then pull
//!
//! A node with a new tip doesn't push the block itself -- most peers
//! will already have it from someone else. It sends a small `INV`
//! (hash, height, size). A peer that doesn't have that block pulls it as
//! `CHUNK`s, `CHUNK_LEN` bytes each, asking for a window of them at a
//! time with `GET_CHUNKS`. The *receiver* drives the transfer: it asks
//! for the next window only once the current one has arrived, and
//! re-asks for whatever's missing if nothing arrives for
//! `chunk_timeout_ms` -- which is both loss recovery and flow control,
//! so a sender never blasts a whole block into socket buffers at once.
//! The finished block is checked as a whole: its header hash must match
//! what was announced (the header commits to the body via `body_hash`),
//! otherwise it's thrown away.
//!
//! # Sync
//!
//! The same machinery catches a node up. An `INV` for a height more than
//! one past our tip isn't downloaded directly -- we ask that peer for
//! *its block at our tip + 1* (`GET_INV` by height) and pull that
//! instead, then the next, and so on. If a block we pull turns out to be
//! an orphan (the peer is on a fork we don't have), the caller asks for
//! its parent by hash (`request_block`), walking back until the branch
//! connects.
//!
//! Knowing who's ahead takes knowing every peer's height. Mostly that
//! comes for free: every `INV` a peer announces says its height. A peer
//! we haven't heard a height from -- a new one, or one silent for
//! `peer_height_refresh_ms` -- is asked once with `GET_INV` for our tip +
//! 1, which every node always answers: with that block if it has one,
//! or else with an `INV` for its own tip (telling us it isn't ahead).
//! So a node in step with its peers sends no sync traffic at all beyond
//! the announcements themselves.
//!
//! # Abuse resistance
//!
//! A `GET_CHUNKS` reply is up to `MAX_SERVE_WINDOW` full packets for a
//! ~60-byte request, so it's only honored with a valid `cookie` (see
//! `discovery`) -- proof the requester really owns its address. A
//! `CHUNK` is only accepted from the peer we're downloading that block
//! from, at an index we asked for, at exactly the right length.
//! Announced sizes over `max_block_bytes` are ignored, and at most
//! `max_downloads` blocks are in flight at once, bounding memory.
//!
//! Like `discovery`, nothing here does network I/O or reads a clock;
//! `net::Node` drives it.

#![allow(dead_code)]

use crate::block::{self, Block, BlockHeader};
use crate::chain::{self, BlockReader};
use crate::discovery::{Discovery, Outgoing};
use crate::wire::{self, CHUNK_LEN, InvQuery, Message};
use std::collections::{BTreeSet, HashMap};
use std::net::SocketAddrV4;

/// The most chunks this node sends in reply to one `GET_CHUNKS`, however
/// many are asked for.
pub const MAX_SERVE_WINDOW: u16 = 64;

#[derive(Clone, Debug)]
pub struct Config {
    /// The biggest block (encoded) this node will download.
    pub max_block_bytes: usize,
    /// Chunks asked for per `GET_CHUNKS`. Capped at `MAX_SERVE_WINDOW`.
    pub window: u16,
    /// How long a download may go without receiving anything before the
    /// missing chunks are asked for again, in milliseconds.
    pub chunk_timeout_ms: u64,
    /// How many times in a row a download may time out before it's
    /// abandoned.
    pub max_retries: u32,
    /// How many blocks may be downloading at once.
    pub max_downloads: usize,
    /// How long a peer's last known height stays fresh, in milliseconds
    /// -- after that, it's asked again (see the module docs).
    pub peer_height_refresh_ms: u64,
}

impl Config {
    fn window(&self) -> u16 {
        self.window.clamp(1, MAX_SERVE_WINDOW)
    }
}

#[derive(Debug)]
pub enum Error {
    Chain(chain::Error),
    Peers(crate::peers::Error),
}

impl From<chain::Error> for Error {
    fn from(e: chain::Error) -> Self {
        Error::Chain(e)
    }
}

impl From<crate::peers::Error> for Error {
    fn from(e: crate::peers::Error) -> Self {
        Error::Peers(e)
    }
}

pub type Result<T> = std::result::Result<T, Error>;

/// What one call produced: packets to send, and any blocks that finished
/// downloading (each with the peer it came from), ready for
/// `Chain::accept_block`.
#[derive(Debug, Default)]
pub struct Step {
    pub packets: Vec<Outgoing>,
    pub delivered: Vec<(Block, SocketAddrV4)>,
}

/// A block being pulled from one peer.
struct Download {
    peer: SocketAddrV4,
    height: u64,
    data: Vec<u8>,
    received: Vec<bool>,
    remaining: usize,
    /// The first chunk index not yet asked for.
    next_to_request: u32,
    /// Asked for, not yet received.
    outstanding: BTreeSet<u32>,
    last_activity_ms: u64,
    retries: u32,
}

/// What this node knows of one peer's chain.
struct PeerHeight {
    /// The highest height it has told us about, if it ever has.
    height: Option<u64>,
    /// When we last heard its height, or last asked for it -- whichever
    /// is later; `None` if neither has happened yet. It's asked (again)
    /// once `peer_height_refresh_ms` has passed since.
    as_of_ms: Option<u64>,
}

/// How long a just-downloaded block is remembered, so it isn't fetched
/// again while it waits to be applied (`has_block` can't see it until
/// then), in milliseconds.
const RECENTLY_DELIVERED_MS: u64 = 30_000;

pub struct Transfer {
    config: Config,
    downloads: HashMap<[u8; 32], Download>,
    /// What we know of each peer's height -- who to sync from.
    peer_heights: HashMap<SocketAddrV4, PeerHeight>,
    /// The last `GET_INV` sent to catch up from a peer known to be ahead:
    /// which height was asked for, and when. Not repeated for the same
    /// height until `chunk_timeout_ms` has passed without an answer.
    last_catch_up: Option<(u64, u64)>,
    /// Blocks downloaded and handed off, by when -- see
    /// `RECENTLY_DELIVERED_MS`.
    recently_delivered: HashMap<[u8; 32], u64>,
    /// While a fast sync is under way: download no blocks but those asked
    /// for by height (`fetch_height`) -- peers' heights are still tracked.
    paused: bool,
    /// Heights asked for with `fetch_height`, downloaded however far ahead.
    wanted: std::collections::HashSet<u64>,
}

impl Transfer {
    pub fn new(config: Config) -> Self {
        Transfer {
            config,
            downloads: HashMap::new(),
            peer_heights: HashMap::new(),
            last_catch_up: None,
            recently_delivered: HashMap::new(),
            paused: false,
            wanted: Default::default(),
        }
    }

    /// Stop (or resume) catching up block by block -- see `paused`.
    pub fn pause(&mut self, paused: bool) {
        self.paused = paused;
        if !paused {
            self.wanted.clear();
        }
    }

    /// Fetch the active-chain block at `height` from the peer furthest
    /// ahead, however far ahead of our tip it is.
    pub fn fetch_height(&mut self, height: u64) -> Vec<Outgoing> {
        self.wanted.insert(height);
        let best = self
            .peer_heights
            .iter()
            .filter_map(|(peer, known)| Some((*peer, known.height?)))
            .filter(|&(_, h)| h >= height)
            .max_by_key(|&(_, h)| h);
        match best {
            Some((peer, _)) => vec![Outgoing {
                to: peer,
                bytes: Message::GetInv(InvQuery::ByHeight(height)).encode(),
            }],
            None => Vec::new(),
        }
    }

    /// The highest tip any peer has told us about, if any has.
    pub fn best_peer_height(&self) -> Option<u64> {
        self.peer_heights.values().filter_map(|p| p.height).max()
    }

    pub fn downloading(&self) -> usize {
        self.downloads.len()
    }

    /// The height a block must have to extend our tip directly.
    fn next_height(reader: &BlockReader) -> Result<u64> {
        Ok(reader.tip()?.map_or(0, |(height, _)| height + 1))
    }

    /// Tell every verified peer (but `except`, typically whoever we got
    /// the block from) that we have this block.
    pub fn announce(
        &self,
        hash: [u8; 32],
        height: u64,
        size: u32,
        except: Option<SocketAddrV4>,
        discovery: &Discovery,
    ) -> Result<Vec<Outgoing>> {
        let message = Message::Inv {
            hash,
            height,
            size,
            tip_height: height,
        }
        .encode();
        let peers = discovery.table().active(usize::MAX, except.unwrap_or(SocketAddrV4::new(0.into(), 0)))?;
        Ok(peers
            .into_iter()
            .map(|to| Outgoing {
                to,
                bytes: message.clone(),
            })
            .collect())
    }

    /// Ask `peer` about a specific block -- typically an orphan's missing
    /// parent. If it has it, its `INV` reply starts the download.
    pub fn request_block(&self, hash: [u8; 32], peer: SocketAddrV4) -> Vec<Outgoing> {
        vec![Outgoing {
            to: peer,
            bytes: Message::GetInv(InvQuery::ByHash(hash)).encode(),
        }]
    }

    /// Handle one decoded message from `from`. Messages that aren't about
    /// block transfer are ignored.
    pub fn handle(
        &mut self,
        from: SocketAddrV4,
        message: &Message,
        discovery: &Discovery,
        reader: &BlockReader,
        now_ms: u64,
    ) -> Result<Step> {
        let mut step = Step::default();
        match message {
            &Message::Inv {
                hash,
                height,
                size,
                tip_height,
            } => self.on_inv(from, hash, height, size, tip_height, discovery, reader, now_ms, &mut step)?,
            Message::GetInv(query) => step.packets.extend(self.on_get_inv(from, *query, reader)?),
            &Message::GetChunks {
                cookie,
                hash,
                first,
                count,
            } if discovery.check_cookie(from, cookie) => {
                step.packets.extend(self.serve_chunks(from, hash, first, count, reader)?);
            }
            Message::Chunk { hash, index, data } => self.on_chunk(from, *hash, *index, data, discovery, now_ms, &mut step),
            _ => {}
        }
        Ok(step)
    }

    #[allow(clippy::too_many_arguments)]
    fn on_inv(
        &mut self,
        from: SocketAddrV4,
        hash: [u8; 32],
        height: u64,
        size: u32,
        tip_height: u64,
        discovery: &Discovery,
        reader: &BlockReader,
        now_ms: u64,
        step: &mut Step,
    ) -> Result<()> {
        let known = self.peer_heights.entry(from).or_insert(PeerHeight {
            height: None,
            as_of_ms: None,
        });
        // The sender's tip, as of now -- not a running maximum: after a
        // reorg onto a heavier but shorter chain, it can go down.
        known.height = Some(tip_height.max(height));
        known.as_of_ms = Some(now_ms);

        if self.downloads.contains_key(&hash)
            || self.recently_delivered.contains_key(&hash)
            || reader.has_block(hash)?
        {
            return Ok(());
        }
        let size = size as usize;
        if size == 0 || size > self.config.max_block_bytes {
            return Ok(());
        }

        let wanted = self.wanted.contains(&height);
        if self.paused && !wanted {
            return Ok(());
        }
        let next = Self::next_height(reader)?;
        if height > next && !wanted {
            // Too far ahead to connect: catch up from our own tip instead.
            step.packets.push(Outgoing {
                to: from,
                bytes: Message::GetInv(InvQuery::ByHeight(next)).encode(),
            });
            self.last_catch_up = Some((next, now_ms));
            return Ok(());
        }

        if self.downloads.len() >= self.config.max_downloads {
            return Ok(());
        }
        // No cookie yet means this peer hasn't answered us; discovery
        // will probe it shortly, and the block will be offered again.
        let Some(cookie) = discovery.cookie_from(from) else {
            return Ok(());
        };
        let chunks = wire::chunk_count(size);
        let mut download = Download {
            peer: from,
            height,
            data: vec![0u8; size],
            received: vec![false; chunks],
            remaining: chunks,
            next_to_request: 0,
            outstanding: BTreeSet::new(),
            last_activity_ms: now_ms,
            retries: 0,
        };
        step.packets.push(self.request_next_window(hash, &mut download, cookie));
        self.downloads.insert(hash, download);
        Ok(())
    }

    fn request_next_window(&self, hash: [u8; 32], download: &mut Download, cookie: u64) -> Outgoing {
        let total = download.received.len() as u32;
        let first = download.next_to_request;
        let count = (self.config.window() as u32).min(total - first) as u16;
        download.outstanding.extend(first..first + count as u32);
        download.next_to_request = first + count as u32;
        Outgoing {
            to: download.peer,
            bytes: Message::GetChunks {
                cookie,
                hash,
                first,
                count,
            }
            .encode(),
        }
    }

    fn on_get_inv(&self, from: SocketAddrV4, query: InvQuery, reader: &BlockReader) -> Result<Vec<Outgoing>> {
        let hash = match query {
            // Beyond our tip, answer with the tip itself: that tells the
            // asker our height, which is what it needs to know either way.
            InvQuery::ByHeight(height) => match reader.active_hash_at(height)? {
                Some(hash) => hash,
                None => match reader.tip()? {
                    Some((tip_height, tip_hash)) if tip_height < height => tip_hash,
                    _ => return Ok(Vec::new()),
                },
            },
            InvQuery::ByHash(hash) => hash,
        };
        let Some((size, header_bytes)) = reader.block_range(hash, 0, block::HEADER_LEN)? else {
            return Ok(Vec::new());
        };
        let Ok(header) = BlockHeader::from_bytes(&header_bytes) else {
            return Ok(Vec::new());
        };
        Ok(vec![Outgoing {
            to: from,
            bytes: Message::Inv {
                hash,
                height: header.height,
                size: size as u32,
                tip_height: reader.tip()?.map_or(0, |(h, _)| h),
            }
            .encode(),
        }])
    }

    fn serve_chunks(
        &self,
        to: SocketAddrV4,
        hash: [u8; 32],
        first: u32,
        count: u16,
        reader: &BlockReader,
    ) -> Result<Vec<Outgoing>> {
        let mut out = Vec::new();
        for index in first..first.saturating_add(count.min(MAX_SERVE_WINDOW) as u32) {
            let start = index as usize * CHUNK_LEN;
            let Some((_, data)) = reader.block_range(hash, start, CHUNK_LEN)? else {
                break;
            };
            out.push(Outgoing {
                to,
                bytes: Message::Chunk { hash, index, data }.encode(),
            });
        }
        Ok(out)
    }

    #[allow(clippy::too_many_arguments)]
    fn on_chunk(
        &mut self,
        from: SocketAddrV4,
        hash: [u8; 32],
        index: u32,
        data: &[u8],
        discovery: &Discovery,
        now_ms: u64,
        step: &mut Step,
    ) {
        let Some(download) = self.downloads.get_mut(&hash) else {
            return;
        };
        if download.peer != from || !download.outstanding.contains(&index) {
            return;
        }
        let i = index as usize;
        if wire::chunk_len(download.data.len(), i) != Some(data.len()) {
            return;
        }
        download.outstanding.remove(&index);
        if !download.received[i] {
            download.received[i] = true;
            download.remaining -= 1;
            download.data[i * CHUNK_LEN..i * CHUNK_LEN + data.len()].copy_from_slice(data);
        }
        download.last_activity_ms = now_ms;
        download.retries = 0;

        if download.remaining == 0 {
            let download = self.downloads.remove(&hash).unwrap();
            match Block::from_bytes(&download.data) {
                Ok(block) if block.header.hash() == hash => {
                    self.recently_delivered.insert(hash, now_ms);
                    step.delivered.push((block, download.peer));
                }
                _ => {} // corrupt or not what was announced: dropped
            }
            return;
        }

        let more_to_ask = (download.next_to_request as usize) < download.received.len();
        if download.outstanding.is_empty() && more_to_ask {
            let Some(cookie) = discovery.cookie_from(download.peer) else {
                self.downloads.remove(&hash);
                return;
            };
            let mut download = self.downloads.remove(&hash).unwrap();
            step.packets.push(self.request_next_window(hash, &mut download, cookie));
            self.downloads.insert(hash, download);
        }
    }

    /// Housekeeping, to be called regularly: re-ask for chunks that have
    /// gone missing (or abandon downloads that keep stalling), and run
    /// the idle sync probe when it's due.
    pub fn tick(&mut self, discovery: &Discovery, reader: &BlockReader, now_ms: u64) -> Result<Step> {
        let mut step = Step::default();

        let timeout = self.config.chunk_timeout_ms;
        let stalled: Vec<[u8; 32]> = self
            .downloads
            .iter()
            .filter(|(_, d)| now_ms >= d.last_activity_ms + timeout)
            .map(|(hash, _)| *hash)
            .collect();
        for hash in stalled {
            let mut download = self.downloads.remove(&hash).unwrap();
            download.retries += 1;
            let cookie = discovery.cookie_from(download.peer);
            let (Some(cookie), true) = (cookie, download.retries <= self.config.max_retries) else {
                continue; // abandoned
            };
            download.last_activity_ms = now_ms;
            // Re-ask for the span still outstanding. Contiguous, so it
            // may re-fetch a few chunks that did arrive -- harmless.
            let first = *download.outstanding.first().unwrap_or(&download.next_to_request);
            let last = download.outstanding.last().copied().unwrap_or(first);
            let count = (last - first + 1).min(self.config.window() as u32) as u16;
            download.outstanding.extend(first..first + count as u32);
            step.packets.push(Outgoing {
                to: download.peer,
                bytes: Message::GetChunks {
                    cookie,
                    hash,
                    first,
                    count,
                }
                .encode(),
            });
            self.downloads.insert(hash, download);
        }

        self.recently_delivered
            .retain(|_, &mut at| now_ms < at + RECENTLY_DELIVERED_MS);

        if self.downloads.is_empty() {
            step.packets.extend(self.sync(discovery, reader, now_ms)?);
        }
        Ok(step)
    }

    /// If some peer is known to be ahead, ask the furthest-ahead one for
    /// our tip + 1 (at most once per `chunk_timeout_ms` for the same
    /// height). Otherwise, ask every verified peer whose height we don't
    /// know, or haven't heard in `peer_height_refresh_ms`.
    fn sync(&mut self, discovery: &Discovery, reader: &BlockReader, now_ms: u64) -> Result<Vec<Outgoing>> {
        let next = Self::next_height(reader)?;
        let query = Message::GetInv(InvQuery::ByHeight(next)).encode();

        let ahead = (!self.paused).then_some(()).and(self
            .peer_heights
            .iter()
            .filter_map(|(peer, known)| Some((*peer, known.height?)))
            .filter(|&(_, height)| height >= next)
            .max_by_key(|&(_, height)| height)
            .map(|(peer, _)| peer));
        if let Some(peer) = ahead {
            let asked_recently = self
                .last_catch_up
                .is_some_and(|(height, at)| height == next && now_ms < at + self.config.chunk_timeout_ms);
            if asked_recently {
                return Ok(Vec::new());
            }
            self.last_catch_up = Some((next, now_ms));
            return Ok(vec![Outgoing { to: peer, bytes: query }]);
        }

        let refresh = self.config.peer_height_refresh_ms;
        let mut out = Vec::new();
        for peer in discovery.table().active(usize::MAX, SocketAddrV4::new(0.into(), 0))? {
            let known = self.peer_heights.entry(peer).or_insert(PeerHeight {
                height: None,
                as_of_ms: None,
            });
            if known.as_of_ms.is_none_or(|at| now_ms >= at + refresh) {
                known.as_of_ms = Some(now_ms);
                out.push(Outgoing {
                    to: peer,
                    bytes: query.clone(),
                });
            }
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chain::{Chain, DifficultyConfig};
    use crate::discovery;
    use crate::output::Output;
    use crate::peers::PeerTable;
    use crate::storage::Storage;
    use crate::transaction::Transaction;
    use crate::wots;
    use std::net::{Ipv4Addr, SocketAddr};
    use std::sync::atomic::{AtomicU64, Ordering};

    struct TempDir(std::path::PathBuf);

    impl TempDir {
        fn new() -> Self {
            static COUNTER: AtomicU64 = AtomicU64::new(0);
            let n = COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!("transfer-test-{}-{n}", std::process::id()));
            std::fs::create_dir_all(&path).unwrap();
            TempDir(path)
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    /// One node's worth of state: its chain, a reader over it, discovery
    /// (for peers and cookies), and transfer.
    struct Side {
        _dir: TempDir,
        addr: SocketAddrV4,
        chain: Chain,
        reader: BlockReader,
        discovery: Discovery,
        transfer: Transfer,
    }

    fn config() -> Config {
        Config {
            max_block_bytes: crate::block::MAX_BLOCK_BYTES,
            window: 2,
            chunk_timeout_ms: 100,
            max_retries: 2,
            max_downloads: 4,
            peer_height_refresh_ms: 1_000,
        }
    }

    fn side(port: u16) -> Side {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut chain = Chain::open(&storage, DifficultyConfig::for_tests(), 5, None).unwrap();
        chain.skip_proof_checks();
        let reader = BlockReader::open(&storage).unwrap();
        let table = PeerTable::open(&storage, 100, 4).unwrap();
        let cfg = discovery::Config {
            seeds: vec![],
            share_limit: 10,
            probe_interval_ms: 60_000,
            response_timeout_ms: 1_000,
        };
        Side {
            _dir: dir,
            addr: SocketAddrV4::new(Ipv4Addr::LOCALHOST, port),
            chain,
            reader,
            discovery: Discovery::new(cfg, table, [port as u8; 32]),
            transfer: Transfer::new(config()),
        }
    }

    /// One discovery round trip: `asker` asks `answerer` for hosts and
    /// gets the reply -- verifying `answerer` and collecting its cookie.
    fn ask(asker: &mut Side, answerer: &mut Side) {
        asker.discovery.table().add_candidate(answerer.addr).unwrap();
        let out = asker.discovery.tick(0).unwrap();
        for packet in out.into_iter().filter(|p| p.to == answerer.addr) {
            let replies = answerer.discovery.handle(SocketAddr::V4(asker.addr), &packet.bytes, 0).unwrap();
            for reply in replies {
                asker.discovery.handle(SocketAddr::V4(answerer.addr), &reply.bytes, 1).unwrap();
            }
        }
    }

    /// Make `a` and `b` mutually verified peers holding each other's cookies.
    fn introduce(a: &mut Side, b: &mut Side) {
        ask(a, b);
        ask(b, a);
    }

    /// A block with `outputs` reward outputs -- 32 bytes each, so enough
    /// of them span several chunks.
    fn mine_block_with_outputs(chain: &mut Chain, outputs: usize, key_base: u8) -> Block {
        let transactions: Vec<Transaction> = (0..outputs)
            .map(|i| {
                let mut seed = [key_base; 32];
                seed[..8].copy_from_slice(&(i as u64).to_be_bytes());
                let (_sk, pk) = wots::keygen(&seed);
                let mut tx = Transaction::new();
                tx.add_output(Output::new(&pk, 50)).unwrap();
                tx
            })
            .collect();
        let unproven = chain.build_block(&transactions).unwrap();
        let target = unproven.target;
        let proof = crate::prover::Proof::placeholder();
        let mut block = unproven.finish(proof);
        assert!(block::mine_block(&mut block, &target, 100_000, &crate::pow::Params::TEST));
        block
    }

    /// Deliver every packet in `packets` addressed to `to`, from `from`,
    /// optionally dropping CHUNKs whose index `drop` says to.
    fn deliver(from: &Side, to: &mut Side, packets: Vec<Outgoing>, now: u64, drop: &dyn Fn(u32) -> bool) -> Step {
        let mut total = Step::default();
        for packet in packets.into_iter().filter(|p| p.to == to.addr) {
            let message = Message::decode(&packet.bytes).unwrap();
            if let Message::Chunk { index, .. } = message
                && drop(index)
            {
                continue;
            }
            let step = to
                .transfer
                .handle(from.addr, &message, &to.discovery, &to.reader, now)
                .unwrap();
            total.packets.extend(step.packets);
            total.delivered.extend(step.delivered);
        }
        total
    }

    /// Ping-pong packets between `a` and `b` until neither sends anything
    /// more, collecting what each one delivered.
    fn exchange(a: &mut Side, b: &mut Side, first: Vec<Outgoing>, now: u64, drop: &dyn Fn(u32) -> bool) -> (Step, Step) {
        let (mut got_a, mut got_b) = (Step::default(), Step::default());
        let mut to_b = first;
        for _ in 0..10_000 {
            let step_b = deliver(a, b, to_b, now, drop);
            got_b.delivered.extend(step_b.delivered);
            let step_a = deliver(b, a, step_b.packets, now, drop);
            got_a.delivered.extend(step_a.delivered);
            if step_a.packets.is_empty() {
                return (got_a, got_b);
            }
            to_b = step_a.packets;
        }
        panic!("exchange never settled");
    }

    #[test]
    fn a_multi_chunk_block_is_announced_pulled_and_delivered_intact() {
        let (mut a, mut b) = (side(1), side(2));
        introduce(&mut a, &mut b);

        let block = mine_block_with_outputs(&mut a.chain, 100, 1);
        a.chain.apply_block(&block).unwrap();
        let size = block.to_bytes().len();
        assert!(wire::chunk_count(size) > 2, "test needs a block spanning several windows");

        let announce = a
            .transfer
            .announce(block.header.hash(), 0, size as u32, None, &a.discovery)
            .unwrap();
        let (_, got_b) = exchange(&mut a, &mut b, announce, 0, &|_| false);

        assert_eq!(got_b.delivered.len(), 1);
        assert_eq!(got_b.delivered[0].0.to_bytes(), block.to_bytes());
        assert_eq!(got_b.delivered[0].1, a.addr);
        assert_eq!(b.transfer.downloading(), 0);
    }

    #[test]
    fn lost_chunks_are_re_requested_after_a_timeout() {
        let (mut a, mut b) = (side(1), side(2));
        introduce(&mut a, &mut b);
        let block = mine_block_with_outputs(&mut a.chain, 100, 1);
        a.chain.apply_block(&block).unwrap();
        let size = block.to_bytes().len() as u32;

        // Chunk 1 is lost the first time around.
        let announce = a.transfer.announce(block.header.hash(), 0, size, None, &a.discovery).unwrap();
        let (_, got_b) = exchange(&mut a, &mut b, announce, 0, &|index| index == 1);
        assert!(got_b.delivered.is_empty());
        assert_eq!(b.transfer.downloading(), 1);

        // Nothing until the timeout...
        assert!(b.transfer.tick(&b.discovery, &b.reader, 50).unwrap().packets.is_empty());
        // ...then a re-request, which now gets through.
        let retry = b.transfer.tick(&b.discovery, &b.reader, 100).unwrap();
        let retry: Vec<Outgoing> = retry.packets.into_iter().filter(|p| p.to == a.addr).collect();
        assert!(!retry.is_empty());
        let step_a = deliver(&b, &mut a, retry, 100, &|_| false);
        let (_, got_b) = exchange(&mut a, &mut b, step_a.packets, 100, &|_| false);
        assert_eq!(got_b.delivered.len(), 1);
        assert_eq!(got_b.delivered[0].0.to_bytes(), block.to_bytes());
    }

    #[test]
    fn a_download_that_keeps_stalling_is_abandoned() {
        let (mut a, mut b) = (side(1), side(2));
        introduce(&mut a, &mut b);
        let block = mine_block_with_outputs(&mut a.chain, 100, 1);
        a.chain.apply_block(&block).unwrap();
        let size = block.to_bytes().len() as u32;

        let announce = a.transfer.announce(block.header.hash(), 0, size, None, &a.discovery).unwrap();
        deliver(&a, &mut b, announce, 0, &|_| false); // b asks; nothing ever comes back
        assert_eq!(b.transfer.downloading(), 1);

        let mut now = 0;
        for _ in 0..=config().max_retries {
            now += 100;
            b.transfer.tick(&b.discovery, &b.reader, now).unwrap();
        }
        assert_eq!(b.transfer.downloading(), 0);
    }

    #[test]
    fn chunk_requests_without_a_valid_cookie_are_ignored() {
        let (mut a, mut b) = (side(1), side(2));
        introduce(&mut a, &mut b);
        let block = mine_block_with_outputs(&mut a.chain, 10, 1);
        a.chain.apply_block(&block).unwrap();

        let request = Message::GetChunks {
            cookie: b.discovery.cookie_from(a.addr).unwrap() ^ 1,
            hash: block.header.hash(),
            first: 0,
            count: 4,
        };
        let step = a.transfer.handle(b.addr, &request, &a.discovery, &a.reader, 0).unwrap();
        assert!(step.packets.is_empty());

        // The genuine cookie works.
        let request = Message::GetChunks {
            cookie: b.discovery.cookie_from(a.addr).unwrap(),
            hash: block.header.hash(),
            first: 0,
            count: 4,
        };
        let step = a.transfer.handle(b.addr, &request, &a.discovery, &a.reader, 0).unwrap();
        assert!(!step.packets.is_empty());
    }

    #[test]
    fn chunks_from_the_wrong_peer_or_unasked_for_are_ignored() {
        let (mut a, mut b) = (side(1), side(2));
        introduce(&mut a, &mut b);
        let block = mine_block_with_outputs(&mut a.chain, 100, 1);
        a.chain.apply_block(&block).unwrap();
        let bytes = block.to_bytes();
        let hash = block.header.hash();

        let announce = a.transfer.announce(hash, 0, bytes.len() as u32, None, &a.discovery).unwrap();
        deliver(&a, &mut b, announce, 0, &|_| false);

        // Right data, wrong sender.
        let chunk0 = Message::Chunk {
            hash,
            index: 0,
            data: bytes[..CHUNK_LEN].to_vec(),
        };
        let stranger = SocketAddrV4::new(Ipv4Addr::new(10, 9, 9, 9), 1);
        b.transfer.handle(stranger, &chunk0, &b.discovery, &b.reader, 0).unwrap();
        // Right sender, chunk not asked for yet (the window is 0..2).
        let chunk3 = Message::Chunk {
            hash,
            index: 3,
            data: bytes[3 * CHUNK_LEN..].to_vec(),
        };
        b.transfer.handle(a.addr, &chunk3, &b.discovery, &b.reader, 0).unwrap();

        let download = &b.transfer.downloads[&hash];
        assert!(!download.received[0]);
        assert!(!download.received[3]);
    }

    #[test]
    fn an_inv_far_ahead_triggers_a_sync_from_our_tip() {
        let (mut a, mut b) = (side(1), side(2));
        introduce(&mut a, &mut b);
        let mut blocks = Vec::new();
        for i in 0..3u8 {
            let block = mine_block_with_outputs(&mut a.chain, 1, 10 + i);
            a.chain.apply_block(&block).unwrap();
            blocks.push(block);
        }
        let tip = blocks.last().unwrap();

        // b (empty) hears about a's tip at height 2: asks for height 0.
        let announce = a
            .transfer
            .announce(tip.header.hash(), 2, tip.to_bytes().len() as u32, None, &a.discovery)
            .unwrap();
        let step = deliver(&a, &mut b, announce, 0, &|_| false);
        assert_eq!(step.packets.len(), 1);
        assert_eq!(
            Message::decode(&step.packets[0].bytes),
            Some(Message::GetInv(InvQuery::ByHeight(0)))
        );

        // a answers with its block 0, which b then pulls.
        let answer = deliver(&b, &mut a, step.packets, 0, &|_| false);
        let (_, got_b) = exchange(&mut a, &mut b, answer.packets, 0, &|_| false);
        assert_eq!(got_b.delivered.len(), 1);
        assert_eq!(got_b.delivered[0].0.to_bytes(), blocks[0].to_bytes());
    }

    #[test]
    fn an_idle_node_probes_a_peer_for_its_next_height() {
        let (mut a, mut b) = (side(1), side(2));
        introduce(&mut a, &mut b);

        let step = b.transfer.tick(&b.discovery, &b.reader, 0).unwrap();
        assert_eq!(step.packets.len(), 1);
        assert_eq!(step.packets[0].to, a.addr);
        assert_eq!(
            Message::decode(&step.packets[0].bytes),
            Some(Message::GetInv(InvQuery::ByHeight(0)))
        );
        // Not again until the interval passes.
        assert!(b.transfer.tick(&b.discovery, &b.reader, 500).unwrap().packets.is_empty());
        assert_eq!(b.transfer.tick(&b.discovery, &b.reader, 1_000).unwrap().packets.len(), 1);
    }

    #[test]
    fn get_inv_by_hash_answers_for_any_stored_block_and_by_height_for_the_active_chain() {
        let (mut a, b) = (side(1), side(2));
        let block = mine_block_with_outputs(&mut a.chain, 1, 1);
        a.chain.apply_block(&block).unwrap();
        let size = block.to_bytes().len() as u32;
        let expected = Some(Message::Inv {
            hash: block.header.hash(),
            height: 0,
            size,
            tip_height: 0,
        });

        for query in [InvQuery::ByHeight(0), InvQuery::ByHash(block.header.hash())] {
            let step = a
                .transfer
                .handle(b.addr, &Message::GetInv(query), &a.discovery, &a.reader, 0)
                .unwrap();
            assert_eq!(Message::decode(&step.packets[0].bytes), expected);
        }
        // Beyond the tip: answered with the tip, so the asker learns our height.
        let step = a
            .transfer
            .handle(b.addr, &Message::GetInv(InvQuery::ByHeight(7)), &a.discovery, &a.reader, 0)
            .unwrap();
        assert_eq!(Message::decode(&step.packets[0].bytes), expected);
        // An unknown hash gets no answer.
        let step = a
            .transfer
            .handle(b.addr, &Message::GetInv(InvQuery::ByHash([9; 32])), &a.discovery, &a.reader, 0)
            .unwrap();
        assert!(step.packets.is_empty());
    }

    #[test]
    fn oversized_or_known_blocks_are_not_downloaded() {
        let (mut a, mut b) = (side(1), side(2));
        introduce(&mut a, &mut b);
        let block = mine_block_with_outputs(&mut a.chain, 1, 1);
        a.chain.apply_block(&block).unwrap();
        b.chain.apply_block(&block).unwrap();

        let known = Message::Inv {
            hash: block.header.hash(),
            height: 0,
            size: 300,
            tip_height: 0,
        };
        let huge = Message::Inv {
            hash: [5; 32],
            height: 1,
            size: (config().max_block_bytes + 1) as u32,
            tip_height: 1,
        };
        for message in [known, huge] {
            let step = b.transfer.handle(a.addr, &message, &b.discovery, &b.reader, 0).unwrap();
            assert!(step.packets.is_empty(), "{message:?}");
        }
        assert_eq!(b.transfer.downloading(), 0);
    }

    /// Two nodes on the same tip: once each knows the other's height,
    /// neither sends anything until that knowledge goes stale.
    #[test]
    fn nodes_in_step_send_no_sync_traffic() {
        let (mut a, mut b) = (side(1), side(2));
        introduce(&mut a, &mut b);
        let block = mine_block_with_outputs(&mut a.chain, 1, 1);
        a.chain.apply_block(&block).unwrap();
        b.chain.apply_block(&block).unwrap();

        // b asks a's height once; a answers with its tip, which b has.
        let probe = b.transfer.tick(&b.discovery, &b.reader, 0).unwrap();
        assert_eq!(probe.packets.len(), 1);
        let answer = deliver(&b, &mut a, probe.packets, 0, &|_| false);
        let step = deliver(&a, &mut b, answer.packets, 0, &|_| false);
        assert!(step.packets.is_empty());

        for now in [100, 500, 999] {
            assert!(b.transfer.tick(&b.discovery, &b.reader, now).unwrap().packets.is_empty(), "at {now}");
        }
        // Stale after the refresh interval: asked once more.
        assert_eq!(b.transfer.tick(&b.discovery, &b.reader, 1_000).unwrap().packets.len(), 1);
    }

    /// A peer known to be ahead is asked for our next block right away,
    /// then not again for that height until `chunk_timeout_ms` passes.
    #[test]
    fn a_peer_known_to_be_ahead_is_asked_without_waiting_but_not_flooded() {
        let (mut a, mut b) = (side(1), side(2));
        introduce(&mut a, &mut b);
        // a claims height 5; b has nothing.
        let inv = Message::Inv {
            hash: [5; 32],
            height: 5,
            size: 300,
            tip_height: 5,
        };
        let step = b.transfer.handle(a.addr, &inv, &b.discovery, &b.reader, 0).unwrap();
        assert_eq!(step.packets.len(), 1);

        assert!(b.transfer.tick(&b.discovery, &b.reader, 50).unwrap().packets.is_empty());
        let again = b.transfer.tick(&b.discovery, &b.reader, 100).unwrap();
        assert_eq!(again.packets.len(), 1);
        assert_eq!(again.packets[0].to, a.addr);
        assert_eq!(
            Message::decode(&again.packets[0].bytes),
            Some(Message::GetInv(InvQuery::ByHeight(0)))
        );
    }

    /// A block downloaded but not applied yet (the chain's owner hasn't
    /// got to it) isn't downloaded a second time when offered again.
    #[test]
    fn a_just_delivered_block_is_not_downloaded_again() {
        let (mut a, mut b) = (side(1), side(2));
        introduce(&mut a, &mut b);
        let block = mine_block_with_outputs(&mut a.chain, 1, 1);
        a.chain.apply_block(&block).unwrap();
        let size = block.to_bytes().len() as u32;
        let hash = block.header.hash();

        let announce = a.transfer.announce(hash, 0, size, None, &a.discovery).unwrap();
        let (_, got_b) = exchange(&mut a, &mut b, announce.clone(), 0, &|_| false);
        assert_eq!(got_b.delivered.len(), 1);

        let step = deliver(&a, &mut b, announce, 10, &|_| false);
        assert!(step.packets.is_empty());
        assert_eq!(b.transfer.downloading(), 0);
    }
}
