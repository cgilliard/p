//! Relaying transactions between peers -- the transaction counterpart of
//! `transfer` (which moves blocks), over the same UDP packets and the same
//! announce-then-pull pattern.
//!
//! - A node announces transactions it holds with `TX_INV` (id and encoded
//!   size). A peer that wants one asks for it with `GET_TX` and receives
//!   `TX_CHUNK`s. Transactions are small (at most `MAX_TX_BYTES`, under
//!   `MAX_SERVE_WINDOW` chunks), so one request covers a whole
//!   transaction; anything missing is asked for again after
//!   `chunk_timeout_ms`.
//! - A finished download must hash to the id it was announced under
//!   (`Transaction::id` is the hash of its encoding); then it's handed to
//!   the node, which checks it against its mempool. **Only transactions
//!   the node accepted are relayed onward** (`add`) -- an invalid one stops
//!   at the first hop.
//! - A newly seen peer is asked once for everything it holds
//!   (`GET_TX_INV`), so a node joining the network fills its mempool.
//!
//! Abuse resistance follows `transfer`'s: replies bigger than the request
//! (`GET_TX`, `GET_TX_INV`) need a valid cookie (see `discovery`); a
//! chunk is only accepted from the peer we asked, at an index of the
//! announced size; at most `max_downloads` transactions are in flight;
//! and ids seen recently aren't fetched again for `seen_ttl_ms`, whether
//! they turned out valid or not.
//!
//! Like `transfer`, nothing here does I/O or reads a clock; `net::Node`
//! drives it.

#![allow(dead_code)]

use std::collections::{HashMap, HashSet};
use std::net::SocketAddrV4;

use crate::discovery::{Discovery, Outgoing};
use crate::poseidon2::hash_bytes_32;
use crate::transfer::MAX_SERVE_WINDOW;
use crate::wire::{self, CHUNK_LEN, MAX_TX_INV, Message};

/// The largest transaction relayed: enough for a full chunk's worth of
/// inputs (10 × ~4.2 KB) and outputs (256 × 40 B), and no more than one
/// `GET_TX` can fetch.
pub const MAX_TX_BYTES: usize = MAX_SERVE_WINDOW as usize * CHUNK_LEN;

#[derive(Clone, Debug)]
pub struct Config {
    /// How long a download may go without receiving anything before the
    /// missing chunks are asked for again, in milliseconds.
    pub chunk_timeout_ms: u64,
    /// How many times in a row a download may time out before it's
    /// abandoned.
    pub max_retries: u32,
    /// How many transactions may be downloading at once.
    pub max_downloads: usize,
    /// How long an id stays "seen" (not fetched again), in milliseconds.
    pub seen_ttl_ms: u64,
}

#[derive(Debug, Default)]
pub struct Step {
    pub packets: Vec<Outgoing>,
    /// Finished downloads -- encoded transactions, each with the peer it
    /// came from -- for the node to check.
    pub delivered: Vec<(Vec<u8>, SocketAddrV4)>,
}

struct Download {
    peer: SocketAddrV4,
    data: Vec<u8>,
    received: Vec<bool>,
    remaining: usize,
    last_activity_ms: u64,
    retries: u32,
}

pub struct TxRelay {
    config: Config,
    /// Transactions we hold (accepted into our mempool), to serve.
    store: HashMap<[u8; 32], Vec<u8>>,
    /// Ids seen recently (held, downloaded, or rejected), by when.
    seen: HashMap<[u8; 32], u64>,
    downloads: HashMap<[u8; 32], Download>,
    /// Peers we've asked for their transactions (`GET_TX_INV`).
    synced: HashSet<SocketAddrV4>,
}

impl TxRelay {
    pub fn new(config: Config) -> Self {
        TxRelay {
            config,
            store: HashMap::new(),
            seen: HashMap::new(),
            downloads: HashMap::new(),
            synced: HashSet::new(),
        }
    }

    pub fn held(&self) -> usize {
        self.store.len()
    }

    pub fn downloading(&self) -> usize {
        self.downloads.len()
    }

    /// Hold `bytes` (a transaction our mempool accepted) and announce it
    /// to every verified peer but `except` (whoever sent it to us).
    pub fn add(
        &mut self,
        bytes: Vec<u8>,
        except: Option<SocketAddrV4>,
        discovery: &Discovery,
        now_ms: u64,
    ) -> Result<Vec<Outgoing>, crate::peers::Error> {
        if bytes.len() > MAX_TX_BYTES {
            return Ok(Vec::new());
        }
        let id = hash_bytes_32(&bytes);
        let size = bytes.len() as u32;
        self.seen.insert(id, now_ms);
        self.store.insert(id, bytes);
        let message = Message::TxInv(vec![(id, size)]).encode();
        let peers = discovery.table().active(usize::MAX, except.unwrap_or(SocketAddrV4::new(0.into(), 0)))?;
        Ok(peers.into_iter().map(|to| Outgoing { to, bytes: message.clone() }).collect())
    }

    /// Stop holding a transaction (mined, or no longer valid). It stays
    /// "seen", so it isn't fetched straight back.
    pub fn remove(&mut self, id: &[u8; 32]) {
        self.store.remove(id);
    }

    /// Handle one decoded message from `from`; others are ignored.
    pub fn handle(&mut self, from: SocketAddrV4, message: &Message, discovery: &Discovery, now_ms: u64) -> Step {
        let mut step = Step::default();
        match message {
            Message::TxInv(entries) => {
                for &(id, size) in entries {
                    self.on_tx_inv(from, id, size as usize, discovery, now_ms, &mut step);
                }
            }
            &Message::GetTx { cookie, id, first, count } if discovery.check_cookie(from, cookie) => {
                step.packets.extend(self.serve(from, id, first, count));
            }
            Message::TxChunk { id, index, data } => self.on_chunk(from, *id, *index, data, now_ms, &mut step),
            &Message::GetTxInv { cookie } if discovery.check_cookie(from, cookie) => {
                let entries: Vec<([u8; 32], u32)> = self.store.iter().map(|(id, b)| (*id, b.len() as u32)).collect();
                for batch in entries.chunks(MAX_TX_INV) {
                    step.packets.push(Outgoing {
                        to: from,
                        bytes: Message::TxInv(batch.to_vec()).encode(),
                    });
                }
            }
            _ => {}
        }
        step
    }

    fn on_tx_inv(&mut self, from: SocketAddrV4, id: [u8; 32], size: usize, discovery: &Discovery, now_ms: u64, step: &mut Step) {
        if self.seen.contains_key(&id) || self.downloads.contains_key(&id) {
            return;
        }
        if size == 0 || size > MAX_TX_BYTES || self.downloads.len() >= self.config.max_downloads {
            return;
        }
        // No cookie yet: this peer hasn't answered us. It'll be offered
        // again (or we'll ask for its transactions once it's verified).
        let Some(cookie) = discovery.cookie_from(from) else {
            return;
        };
        let chunks = wire::chunk_count(size);
        self.downloads.insert(
            id,
            Download {
                peer: from,
                data: vec![0u8; size],
                received: vec![false; chunks],
                remaining: chunks,
                last_activity_ms: now_ms,
                retries: 0,
            },
        );
        step.packets.push(Outgoing {
            to: from,
            bytes: Message::GetTx {
                cookie,
                id,
                first: 0,
                count: chunks as u16,
            }
            .encode(),
        });
    }

    fn serve(&self, to: SocketAddrV4, id: [u8; 32], first: u32, count: u16) -> Vec<Outgoing> {
        let Some(bytes) = self.store.get(&id) else {
            return Vec::new();
        };
        (first..first.saturating_add(count.min(MAX_SERVE_WINDOW) as u32))
            .map_while(|index| {
                let len = wire::chunk_len(bytes.len(), index as usize)?;
                let start = index as usize * CHUNK_LEN;
                Some(Outgoing {
                    to,
                    bytes: Message::TxChunk {
                        id,
                        index,
                        data: bytes[start..start + len].to_vec(),
                    }
                    .encode(),
                })
            })
            .collect()
    }

    fn on_chunk(&mut self, from: SocketAddrV4, id: [u8; 32], index: u32, data: &[u8], now_ms: u64, step: &mut Step) {
        let Some(download) = self.downloads.get_mut(&id) else {
            return;
        };
        let i = index as usize;
        if download.peer != from || wire::chunk_len(download.data.len(), i) != Some(data.len()) {
            return;
        }
        if !download.received[i] {
            download.received[i] = true;
            download.remaining -= 1;
            download.data[i * CHUNK_LEN..i * CHUNK_LEN + data.len()].copy_from_slice(data);
        }
        download.last_activity_ms = now_ms;
        download.retries = 0;
        if download.remaining > 0 {
            return;
        }
        let download = self.downloads.remove(&id).unwrap();
        self.seen.insert(id, now_ms);
        if hash_bytes_32(&download.data) == id {
            step.delivered.push((download.data, download.peer));
        }
    }

    /// Housekeeping, to be called regularly: re-ask for missing chunks
    /// (or give up), forget old "seen" ids, and ask newly verified peers
    /// for their transactions.
    pub fn tick(&mut self, discovery: &Discovery, now_ms: u64) -> Result<Step, crate::peers::Error> {
        let mut step = Step::default();
        let timeout = self.config.chunk_timeout_ms;
        let stalled: Vec<[u8; 32]> = self
            .downloads
            .iter()
            .filter(|(_, d)| now_ms >= d.last_activity_ms + timeout)
            .map(|(id, _)| *id)
            .collect();
        for id in stalled {
            let mut download = self.downloads.remove(&id).unwrap();
            download.retries += 1;
            let (Some(cookie), true) = (discovery.cookie_from(download.peer), download.retries <= self.config.max_retries) else {
                continue; // abandoned; it can be offered again later
            };
            download.last_activity_ms = now_ms;
            // Ask again for the span from the first missing chunk.
            let first = download.received.iter().position(|r| !r).unwrap_or(0);
            let count = download.received.len() - first;
            step.packets.push(Outgoing {
                to: download.peer,
                bytes: Message::GetTx {
                    cookie,
                    id,
                    first: first as u32,
                    count: count as u16,
                }
                .encode(),
            });
            self.downloads.insert(id, download);
        }

        let ttl = self.config.seen_ttl_ms;
        let store = &self.store;
        self.seen.retain(|id, &mut at| store.contains_key(id) || now_ms < at + ttl);

        for peer in discovery.table().active(usize::MAX, SocketAddrV4::new(0.into(), 0))? {
            if self.synced.contains(&peer) {
                continue;
            }
            if let Some(cookie) = discovery.cookie_from(peer) {
                self.synced.insert(peer);
                step.packets.push(Outgoing {
                    to: peer,
                    bytes: Message::GetTxInv { cookie }.encode(),
                });
            }
        }
        Ok(step)
    }
}
