//! Fast sync over the network (`docs/CHAIN_RECURSION.md`, 5d): serving and
//! fetching what a node needs to start at a recent block instead of
//! replaying the chain -- the block's *sync point* (what its chain proof
//! attests besides the header) and the state tree as of it, in pieces
//! (`snapshot`).
//!
//! - `GET_SYNC_POINT` / `SYNC_POINT`: one small packet each way. Any peer
//!   may answer; the answer is only believed once the block's chain proof
//!   verifies against it (the node checks that).
//! - `GET_PIECE` / `PIECE_CHUNK`: a piece travels like a block, in
//!   `CHUNK_LEN` chunks, a window at a time; the first chunk tells its
//!   size. Pieces are fetched from every usable peer at once, at most
//!   `max_in_flight` at a time. A finished piece is checked on the spot
//!   (`snapshot::Plan::accept`): one that doesn't match its hash gets its
//!   sender banned from this sync and is fetched again elsewhere; a peer
//!   that times out on a piece (`max_retries` times in a row) gets a
//!   strike, and is no longer asked after `max_strikes` -- a peer that
//!   can't serve the sync point (pruned past it, or on another branch)
//!   just never answers.
//!
//! Abuse resistance follows `transfer`'s: a `GET_PIECE` reply can be many
//! packets, so it needs a valid cookie; chunks are accepted only from the
//! peer asked, for the piece asked, at an index within the window asked,
//! of a consistent size no bigger than a piece can be.
//!
//! Like `transfer`, nothing here does I/O or reads a clock; `net::Node`
//! drives it.

use std::collections::{HashMap, VecDeque};
use std::net::SocketAddrV4;

use crate::chain::StateReader;
use crate::discovery::{Discovery, Outgoing};
use crate::snapshot::{MAX_PIECE_BYTES, Piece, Plan, SyncPoint};
use crate::state_tree::Entry;
use crate::transfer::MAX_SERVE_WINDOW;
use crate::wire::{self, CHUNK_LEN, Message};

#[derive(Clone, Debug)]
pub struct Config {
    /// Chunks asked for per `GET_PIECE`. Capped at `MAX_SERVE_WINDOW`.
    pub window: u16,
    /// How long a piece may go without receiving anything before the
    /// missing chunks are asked for again, in milliseconds.
    pub chunk_timeout_ms: u64,
    /// How many times in a row a piece may time out before it's given to
    /// another peer.
    pub max_retries: u32,
    /// How many pieces may be downloading at once (across all peers).
    pub max_in_flight: usize,
    /// How many pieces a peer may fail before it's no longer asked.
    pub max_strikes: u32,
}

/// What fast sync produced for the node.
#[derive(Debug)]
pub enum Event {
    /// A peer's answer to `request_point`: unverified.
    Point { hash: [u8; 32], point: SyncPoint, from: SocketAddrV4 },
    /// The state download finished: every unspent output as of the sync
    /// point, each piece checked.
    State(Vec<Entry>),
}

#[derive(Debug, Default)]
pub struct Step {
    pub packets: Vec<Outgoing>,
    pub events: Vec<Event>,
}

struct Download {
    piece: Piece,
    peer: SocketAddrV4,
    /// Unknown until the first chunk arrives.
    size: Option<usize>,
    data: Vec<u8>,
    received: Vec<bool>,
    remaining: usize,
    /// Chunks asked for so far: `0..requested`.
    requested: u32,
    last_activity_ms: u64,
    retries: u32,
}

/// The state download in progress.
struct Session {
    at: [u8; 32],
    plan: Plan,
    downloads: HashMap<(usize, u64), Download>,
    strikes: HashMap<SocketAddrV4, u32>,
    pieces: usize,
}

/// How many served pieces are kept for repeat requests (each piece is
/// asked for a window at a time).
const SERVED_CACHE: usize = 32;

type ServedPiece = ([u8; 32], u8, u32);

pub struct StateSync {
    config: Config,
    session: Option<Session>,
    /// Pieces recently served, newest last.
    served: VecDeque<(ServedPiece, std::sync::Arc<Vec<u8>>)>,
}

impl StateSync {
    pub fn new(config: Config) -> Self {
        StateSync {
            config,
            session: None,
            served: VecDeque::new(),
        }
    }

    fn window(&self) -> u32 {
        self.config.window.clamp(1, MAX_SERVE_WINDOW) as u32
    }

    /// Ask every verified peer for block `hash`'s sync point.
    pub fn request_point(&self, hash: [u8; 32], discovery: &Discovery) -> Result<Vec<Outgoing>, crate::peers::Error> {
        let message = Message::GetSyncPoint { hash }.encode();
        let peers = discovery.table().active(usize::MAX, SocketAddrV4::new(0.into(), 0))?;
        Ok(peers.into_iter().map(|to| Outgoing { to, bytes: message.clone() }).collect())
    }

    /// Start downloading the state as of block `at`: a tree with `root`
    /// holding `count` outputs (both attested). Replaces any download in
    /// progress.
    pub fn start(&mut self, at: [u8; 32], root: [u8; 32], count: u64) {
        self.session = Some(Session {
            at,
            plan: Plan::new(root, count),
            downloads: HashMap::new(),
            strikes: HashMap::new(),
            pieces: 0,
        });
    }

    pub fn stop(&mut self) {
        self.session = None;
    }

    /// Handle one decoded message from `from`; others are ignored.
    pub fn handle(&mut self, from: SocketAddrV4, message: &Message, discovery: &Discovery, reader: &StateReader, now_ms: u64) -> Step {
        let mut step = Step::default();
        match message {
            &Message::GetSyncPoint { hash } => {
                if let Ok(Some(point)) = reader.sync_point(hash) {
                    step.packets.push(Outgoing {
                        to: from,
                        bytes: Message::SyncPoint { hash, point }.encode(),
                    });
                }
            }
            &Message::SyncPoint { hash, point } => step.events.push(Event::Point { hash, point, from }),
            &Message::GetPiece {
                cookie,
                at,
                level,
                index,
                first,
                count,
            } if discovery.check_cookie(from, cookie) => {
                step.packets.extend(self.serve(from, (at, level, index), first, count, reader));
            }
            Message::PieceChunk {
                at,
                level,
                index,
                size,
                chunk,
                data,
            } => self.on_chunk(from, (*at, *level, *index), *size as usize, *chunk, data, discovery, now_ms, &mut step),
            _ => {}
        }
        step
    }

    fn serve(&mut self, to: SocketAddrV4, id: ServedPiece, first: u32, count: u16, reader: &StateReader) -> Vec<Outgoing> {
        let bytes = match self.served.iter().find(|(served, _)| *served == id) {
            Some((_, bytes)) => bytes.clone(),
            None => {
                let (at, level, index) = id;
                let Ok(Some(bytes)) = reader.piece(at, level as usize, index as u64) else {
                    return Vec::new();
                };
                let bytes = std::sync::Arc::new(bytes);
                if self.served.len() >= SERVED_CACHE {
                    self.served.pop_front();
                }
                self.served.push_back((id, bytes.clone()));
                bytes
            }
        };
        let (at, level, index) = id;
        let size = bytes.len() as u32;
        let chunks = wire::chunk_count(bytes.len()).max(1) as u32;
        (first..first.saturating_add(count.min(MAX_SERVE_WINDOW) as u32).min(chunks))
            .map(|chunk| {
                let start = (chunk as usize * CHUNK_LEN).min(bytes.len());
                let end = (start + CHUNK_LEN).min(bytes.len());
                Outgoing {
                    to,
                    bytes: Message::PieceChunk {
                        at,
                        level,
                        index,
                        size,
                        chunk,
                        data: bytes[start..end].to_vec(),
                    }
                    .encode(),
                }
            })
            .collect()
    }

    fn request(at: [u8; 32], download: &Download, first: u32, count: u32, cookie: u64) -> Outgoing {
        Outgoing {
            to: download.peer,
            bytes: Message::GetPiece {
                cookie,
                at,
                level: download.piece.level as u8,
                index: download.piece.index as u32,
                first,
                count: count as u16,
            }
            .encode(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn on_chunk(&mut self, from: SocketAddrV4, (at, level, index): ServedPiece, size: usize, chunk: u32, data: &[u8], discovery: &Discovery, now_ms: u64, step: &mut Step) {
        let window = self.window();
        let Some(session) = &mut self.session else {
            return;
        };
        let key = (level as usize, index as u64);
        let Some(download) = session.downloads.get_mut(&key) else {
            return;
        };
        if at != session.at || download.peer != from || chunk >= download.requested || size > MAX_PIECE_BYTES {
            return;
        }
        let chunks = wire::chunk_count(size).max(1);
        match download.size {
            None => {
                download.size = Some(size);
                download.data = vec![0u8; size];
                download.received = vec![false; chunks];
                download.remaining = chunks;
            }
            Some(known) if known != size => return,
            Some(_) => {}
        }
        let i = chunk as usize;
        if i >= chunks || wire::chunk_len(size, i).unwrap_or(0) != data.len() {
            return;
        }
        if !download.received[i] {
            download.received[i] = true;
            download.remaining -= 1;
            download.data[i * CHUNK_LEN..i * CHUNK_LEN + data.len()].copy_from_slice(data);
        }
        download.last_activity_ms = now_ms;
        download.retries = 0;

        if download.remaining == 0 {
            let download = session.downloads.remove(&key).unwrap();
            if session.plan.accept(&download.piece, &download.data) {
                session.pieces += 1;
            } else {
                warn!("fast sync: {from} sent a bad piece of the state -- no longer asking it");
                session.strikes.insert(from, u32::MAX);
                session.plan.retry(download.piece);
            }
            self.fill(discovery, now_ms, step);
            return;
        }
        // The window's in: ask for the next.
        let requested = download.requested as usize;
        let window_done = download.received[..requested.min(chunks)].iter().all(|&r| r);
        if window_done && requested < chunks {
            let Some(cookie) = discovery.cookie_from(download.peer) else {
                return;
            };
            let count = window.min((chunks - requested) as u32);
            let first = download.requested;
            download.requested += count;
            let (at, download) = (session.at, &session.downloads[&key]);
            step.packets.push(Self::request(at, download, first, count, cookie));
        }
    }

    /// Start fetching pieces until `max_in_flight` are out, each from the
    /// usable peer with the fewest in flight; and report the download
    /// finished once nothing is left.
    fn fill(&mut self, discovery: &Discovery, now_ms: u64, step: &mut Step) {
        let window = self.window();
        let max_strikes = self.config.max_strikes;
        let Some(session) = &mut self.session else {
            return;
        };
        let peers: Vec<(SocketAddrV4, u64)> = discovery
            .table()
            .active(usize::MAX, SocketAddrV4::new(0.into(), 0))
            .unwrap_or_default()
            .into_iter()
            .filter(|p| session.strikes.get(p).copied().unwrap_or(0) < max_strikes)
            .filter_map(|p| Some((p, discovery.cookie_from(p)?)))
            .collect();
        while session.downloads.len() < self.config.max_in_flight {
            let Some(&(peer, cookie)) = peers
                .iter()
                .min_by_key(|(p, _)| session.downloads.values().filter(|d| d.peer == *p).count())
            else {
                break;
            };
            let Some(piece) = session.plan.next() else {
                break;
            };
            let download = Download {
                piece,
                peer,
                size: None,
                data: Vec::new(),
                received: Vec::new(),
                remaining: 1,
                requested: window,
                last_activity_ms: now_ms,
                retries: 0,
            };
            let at = session.at;
            step.packets.push(Outgoing {
                to: peer,
                bytes: Message::GetPiece {
                    cookie,
                    at,
                    level: piece.level as u8,
                    index: piece.index as u32,
                    first: 0,
                    count: window as u16,
                }
                .encode(),
            });
            session.downloads.insert((piece.level, piece.index), download);
        }
        if session.downloads.is_empty() {
            match session.plan.next() {
                Some(piece) => session.plan.retry(piece), // no usable peer yet
                None => {
                    let session = self.session.take().unwrap();
                    debug!("fast sync: the state's {} pieces are in", session.pieces);
                    step.events.push(Event::State(session.plan.finish()));
                }
            }
        }
    }

    /// Housekeeping, to be called regularly: re-ask for missing chunks,
    /// hand pieces that keep stalling to other peers, and keep pieces in
    /// flight.
    pub fn tick(&mut self, discovery: &Discovery, now_ms: u64) -> Step {
        let mut step = Step::default();
        let (timeout, max_retries) = (self.config.chunk_timeout_ms, self.config.max_retries);
        let Some(session) = &mut self.session else {
            return step;
        };
        let stalled: Vec<(usize, u64)> = session
            .downloads
            .iter()
            .filter(|(_, d)| now_ms >= d.last_activity_ms + timeout)
            .map(|(k, _)| *k)
            .collect();
        let mut again = Vec::new();
        for key in stalled {
            let download = session.downloads.get_mut(&key).unwrap();
            download.retries += 1;
            let cookie = discovery.cookie_from(download.peer);
            match cookie {
                Some(cookie) if download.retries <= max_retries => {
                    download.last_activity_ms = now_ms;
                    let first = download.received.iter().position(|r| !r).unwrap_or(0) as u32;
                    let count = download.requested.saturating_sub(first).max(1);
                    again.push((key, first, count, cookie));
                }
                _ => {
                    let download = session.downloads.remove(&key).unwrap();
                    *session.strikes.entry(download.peer).or_insert(0) += 1;
                    session.plan.retry(download.piece);
                }
            }
        }
        for (key, first, count, cookie) in again {
            let download = &self.session.as_ref().unwrap().downloads[&key];
            let at = self.session.as_ref().unwrap().at;
            step.packets.push(Self::request(at, download, first, count, cookie));
        }
        self.fill(discovery, now_ms, &mut step);
        step
    }
}
