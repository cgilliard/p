//! The network's wire format: every message any node sends or accepts,
//! and their exact byte encodings. Shared by `discovery` (finding peers)
//! and `transfer` (moving blocks); nothing here does any I/O.
//!
//! Every packet: `MAGIC` (4) ‖ `VERSION` (1) ‖ type (1) ‖ body. Integers
//! are big-endian. A packet that doesn't parse *exactly* -- wrong
//! length, trailing bytes, non-zero padding -- is rejected whole.
//!
//! | type | message      | body                                                        |
//! |------|--------------|-------------------------------------------------------------|
//! | 1    | `GET_HOSTS`  | nonce u64 ‖ max u16 ‖ zero padding                          |
//! | 2    | `HOSTS`      | nonce u64 ‖ cookie u64 ‖ count u16 ‖ count × addr (6)       |
//! | 3    | `INV`        | hash (32) ‖ height u64 ‖ size u32                           |
//! | 4    | `GET_INV`    | kind u8 (0 = by height, 1 = by hash) ‖ 32-byte field          |
//! | 5    | `GET_CHUNKS` | cookie u64 ‖ hash (32) ‖ first u32 ‖ count u16               |
//! | 6    | `CHUNK`      | hash (32) ‖ index u32 ‖ data (`CHUNK_LEN`, or less if last)  |
//!
//! `GET_INV`'s field is the hash, or for a height, 24 zero bytes then
//! the height -- one fixed size either way, so its `INV` reply (50
//! bytes) never exceeds `AMPLIFICATION_FACTOR` times the request (39).
//!
//! Every packet is at most `MAX_PACKET` bytes, so none ever needs IP
//! fragmentation -- minimal (bare-metal) stacks often can't reassemble.
//! A block bigger than one packet travels as `CHUNK`s; see `transfer`.

#![allow(dead_code)]

use crate::peers::{self, ADDR_LEN};
use std::net::SocketAddrV4;

pub const MAGIC: [u8; 4] = *b"TBRN";
pub const VERSION: u8 = 2;

/// Largest packet this protocol ever sends or accepts -- comfortably
/// under the 1280-byte IPv6 minimum MTU (and every realistic IPv4 path
/// MTU), so nothing is ever fragmented.
pub const MAX_PACKET: usize = 1200;

/// A reply is never more than this many times the size of the request
/// that prompted it, unless the requester has proven it owns its source
/// address (a `cookie`) -- see `discovery`'s docs.
pub const AMPLIFICATION_FACTOR: usize = 3;

/// Bytes of block data per `CHUNK`. A round number that leaves room for
/// the chunk's own header within `MAX_PACKET`.
pub const CHUNK_LEN: usize = 1024;

const TYPE_GET_HOSTS: u8 = 1;
const TYPE_HOSTS: u8 = 2;
const TYPE_INV: u8 = 3;
const TYPE_GET_INV: u8 = 4;
const TYPE_GET_CHUNKS: u8 = 5;
const TYPE_CHUNK: u8 = 6;

pub const HEADER_LEN: usize = MAGIC.len() + 2;
const GET_HOSTS_MIN: usize = HEADER_LEN + 8 + 2;
const HOSTS_MIN: usize = HEADER_LEN + 8 + 8 + 2;
const INV_LEN: usize = HEADER_LEN + 32 + 8 + 4;
const GET_INV_LEN: usize = HEADER_LEN + 1 + 32;
const GET_CHUNKS_LEN: usize = HEADER_LEN + 8 + 32 + 4 + 2;
const CHUNK_HEADER_LEN: usize = HEADER_LEN + 32 + 4;

/// The most addresses a single `HOSTS` packet can carry.
pub const MAX_HOSTS_PER_PACKET: usize = (MAX_PACKET - HOSTS_MIN) / ADDR_LEN;

const _: () = assert!(CHUNK_HEADER_LEN + CHUNK_LEN <= MAX_PACKET);
const _: () = assert!(INV_LEN <= GET_INV_LEN * AMPLIFICATION_FACTOR);

/// Which block a `GET_INV` asks about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InvQuery {
    /// The sender's active-chain block at this height.
    ByHeight(u64),
    /// This exact block, active chain or not.
    ByHash([u8; 32]),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Message {
    /// "Send me hosts you know." See `discovery`.
    GetHosts { nonce: u64, max: u16 },
    /// The answer to `GetHosts`, plus a `cookie` the requester must
    /// quote back in any `GetChunks` it sends us -- proof it really
    /// receives packets at its source address.
    Hosts { nonce: u64, cookie: u64, hosts: Vec<SocketAddrV4> },
    /// "I have this block, `size` bytes encoded." Sent unprompted when a
    /// node gets a new tip, and as the answer to `GetInv`.
    Inv { hash: [u8; 32], height: u64, size: u32 },
    /// "Tell me about this block, if you have it."
    GetInv(InvQuery),
    /// "Send me chunks `first .. first + count` of this block."
    GetChunks { cookie: u64, hash: [u8; 32], first: u32, count: u16 },
    /// One piece of a block's encoding, at byte offset `index * CHUNK_LEN`.
    Chunk { hash: [u8; 32], index: u32, data: Vec<u8> },
}

/// Size of a `HOSTS` packet carrying `count` addresses.
pub fn hosts_packet_len(count: usize) -> usize {
    HOSTS_MIN + count * ADDR_LEN
}

/// How many addresses a `HOSTS` reply to a `request_len`-byte request
/// may carry without breaking the amplification bound.
pub fn hosts_amplification_limit(request_len: usize) -> usize {
    (request_len * AMPLIFICATION_FACTOR).saturating_sub(HOSTS_MIN) / ADDR_LEN
}

/// How many `CHUNK`s a block of `size` bytes splits into.
pub fn chunk_count(size: usize) -> usize {
    size.div_ceil(CHUNK_LEN)
}

/// The exact length chunk `index` of a `size`-byte block must have, or
/// `None` if there's no such chunk.
pub fn chunk_len(size: usize, index: usize) -> Option<usize> {
    let start = index.checked_mul(CHUNK_LEN)?;
    if start >= size {
        return None;
    }
    Some((size - start).min(CHUNK_LEN))
}

fn read_hash(bytes: &[u8]) -> [u8; 32] {
    bytes[..32].try_into().unwrap()
}

fn read_u16(bytes: &[u8]) -> u16 {
    u16::from_be_bytes(bytes[..2].try_into().unwrap())
}

fn read_u32(bytes: &[u8]) -> u32 {
    u32::from_be_bytes(bytes[..4].try_into().unwrap())
}

fn read_u64(bytes: &[u8]) -> u64 {
    u64::from_be_bytes(bytes[..8].try_into().unwrap())
}

impl Message {
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(MAX_PACKET);
        out.extend_from_slice(&MAGIC);
        out.push(VERSION);
        match self {
            Message::GetHosts { nonce, max } => {
                out.push(TYPE_GET_HOSTS);
                out.extend_from_slice(&nonce.to_be_bytes());
                out.extend_from_slice(&max.to_be_bytes());
                // Pad so the answer we're asking for fits under the
                // amplification bound: request_len * FACTOR >= reply_len.
                let max = (*max as usize).min(MAX_HOSTS_PER_PACKET);
                let needed = hosts_packet_len(max).div_ceil(AMPLIFICATION_FACTOR);
                if out.len() < needed {
                    out.resize(needed, 0);
                }
            }
            Message::Hosts { nonce, cookie, hosts } => {
                out.push(TYPE_HOSTS);
                out.extend_from_slice(&nonce.to_be_bytes());
                out.extend_from_slice(&cookie.to_be_bytes());
                let hosts = &hosts[..hosts.len().min(MAX_HOSTS_PER_PACKET)];
                out.extend_from_slice(&(hosts.len() as u16).to_be_bytes());
                for host in hosts {
                    out.extend_from_slice(&peers::encode_addr(*host));
                }
            }
            Message::Inv { hash, height, size } => {
                out.push(TYPE_INV);
                out.extend_from_slice(hash);
                out.extend_from_slice(&height.to_be_bytes());
                out.extend_from_slice(&size.to_be_bytes());
            }
            Message::GetInv(query) => {
                out.push(TYPE_GET_INV);
                match query {
                    InvQuery::ByHeight(height) => {
                        out.push(0);
                        out.extend_from_slice(&[0u8; 24]);
                        out.extend_from_slice(&height.to_be_bytes());
                    }
                    InvQuery::ByHash(hash) => {
                        out.push(1);
                        out.extend_from_slice(hash);
                    }
                }
            }
            Message::GetChunks { cookie, hash, first, count } => {
                out.push(TYPE_GET_CHUNKS);
                out.extend_from_slice(&cookie.to_be_bytes());
                out.extend_from_slice(hash);
                out.extend_from_slice(&first.to_be_bytes());
                out.extend_from_slice(&count.to_be_bytes());
            }
            Message::Chunk { hash, index, data } => {
                out.push(TYPE_CHUNK);
                out.extend_from_slice(hash);
                out.extend_from_slice(&index.to_be_bytes());
                out.extend_from_slice(&data[..data.len().min(CHUNK_LEN)]);
            }
        }
        out
    }

    /// Parse a packet, or `None` if it isn't exactly a valid one.
    pub fn decode(bytes: &[u8]) -> Option<Message> {
        if bytes.len() < HEADER_LEN || bytes.len() > MAX_PACKET {
            return None;
        }
        if bytes[..4] != MAGIC || bytes[4] != VERSION {
            return None;
        }
        let body = &bytes[HEADER_LEN..];
        match bytes[5] {
            TYPE_GET_HOSTS if bytes.len() >= GET_HOSTS_MIN => {
                // Padding is allowed (and required, for large `max`),
                // but must be zeros -- no room to smuggle anything in.
                if !body[10..].iter().all(|&b| b == 0) {
                    return None;
                }
                Some(Message::GetHosts {
                    nonce: read_u64(body),
                    max: read_u16(&body[8..]),
                })
            }
            TYPE_HOSTS if bytes.len() >= HOSTS_MIN => {
                let count = read_u16(&body[16..]) as usize;
                let addrs = &body[18..];
                if addrs.len() != count * ADDR_LEN {
                    return None;
                }
                let hosts = addrs
                    .chunks_exact(ADDR_LEN)
                    .map(|chunk| peers::decode_addr(chunk.try_into().unwrap()))
                    .collect();
                Some(Message::Hosts {
                    nonce: read_u64(body),
                    cookie: read_u64(&body[8..]),
                    hosts,
                })
            }
            TYPE_INV if bytes.len() == INV_LEN => Some(Message::Inv {
                hash: read_hash(body),
                height: read_u64(&body[32..]),
                size: read_u32(&body[40..]),
            }),
            TYPE_GET_INV if bytes.len() == GET_INV_LEN => match body[0] {
                0 if body[1..25].iter().all(|&b| b == 0) => Some(Message::GetInv(InvQuery::ByHeight(read_u64(&body[25..])))),
                1 => Some(Message::GetInv(InvQuery::ByHash(read_hash(&body[1..])))),
                _ => None,
            },
            TYPE_GET_CHUNKS if bytes.len() == GET_CHUNKS_LEN => Some(Message::GetChunks {
                cookie: read_u64(body),
                hash: read_hash(&body[8..]),
                first: read_u32(&body[40..]),
                count: read_u16(&body[44..]),
            }),
            // An empty chunk is never valid -- every chunk carries at
            // least one byte (see `chunk_len`).
            TYPE_CHUNK if bytes.len() > CHUNK_HEADER_LEN => Some(Message::Chunk {
                hash: read_hash(body),
                index: read_u32(&body[32..]),
                data: body[36..].to_vec(),
            }),
            _ => None,
        }
    }

    /// A one-line, human-readable summary, for logs.
    pub fn describe(&self) -> String {
        fn short(hash: &[u8; 32]) -> String {
            hash[..6].iter().map(|b| format!("{b:02x}")).collect()
        }
        match self {
            Message::GetHosts { nonce, max } => format!("GET_HOSTS(nonce={nonce:016x}, max={max})"),
            Message::Hosts { nonce, hosts, .. } => {
                let hosts: Vec<String> = hosts.iter().map(|h| h.to_string()).collect();
                format!("HOSTS(nonce={nonce:016x}, [{}])", hosts.join(", "))
            }
            Message::Inv { hash, height, size } => format!("INV({} @ {height}, {size} bytes)", short(hash)),
            Message::GetInv(InvQuery::ByHeight(height)) => format!("GET_INV(height {height})"),
            Message::GetInv(InvQuery::ByHash(hash)) => format!("GET_INV({})", short(hash)),
            Message::GetChunks { hash, first, count, .. } => {
                format!("GET_CHUNKS({}, {first}..{})", short(hash), *first as u64 + *count as u64)
            }
            Message::Chunk { hash, index, data } => format!("CHUNK({} #{index}, {} bytes)", short(hash), data.len()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::Ipv4Addr;

    fn addr(last_octet: u8, port: u16) -> SocketAddrV4 {
        SocketAddrV4::new(Ipv4Addr::new(10, 0, 0, last_octet), port)
    }

    fn all_kinds() -> Vec<Message> {
        vec![
            Message::GetHosts { nonce: 42, max: 17 },
            Message::Hosts {
                nonce: 43,
                cookie: 0xdead_beef,
                hosts: vec![addr(1, 1), addr(2, 2)],
            },
            Message::Inv {
                hash: [7; 32],
                height: 1_000,
                size: 2_000_000,
            },
            Message::GetInv(InvQuery::ByHeight(12)),
            Message::GetInv(InvQuery::ByHash([9; 32])),
            Message::GetChunks {
                cookie: 5,
                hash: [3; 32],
                first: 64,
                count: 32,
            },
            Message::Chunk {
                hash: [4; 32],
                index: 3,
                data: vec![1; CHUNK_LEN],
            },
            Message::Chunk {
                hash: [4; 32],
                index: 4,
                data: vec![2; 17],
            },
        ]
    }

    #[test]
    fn every_message_roundtrips_and_fits_a_packet() {
        for message in all_kinds() {
            let bytes = message.encode();
            assert!(bytes.len() <= MAX_PACKET, "{message:?}");
            assert_eq!(Message::decode(&bytes), Some(message));
        }
    }

    #[test]
    fn every_message_rejects_a_bad_header_or_trailing_byte() {
        for message in all_kinds() {
            let good = message.encode();
            let mut bad_magic = good.clone();
            bad_magic[0] ^= 1;
            let mut bad_version = good.clone();
            bad_version[4] = VERSION + 1;
            let mut bad_type = good.clone();
            bad_type[5] = 99;
            for bad in [bad_magic, bad_version, bad_type] {
                assert_eq!(Message::decode(&bad), None, "{message:?}");
            }

            // Fixed-size messages reject any extra byte; padded/variable
            // ones reject a non-zero or misaligned one.
            let mut trailing = good.clone();
            trailing.push(1);
            if !matches!(message, Message::Chunk { .. }) {
                assert_eq!(Message::decode(&trailing), None, "{message:?}");
            }
        }
    }

    #[test]
    fn truncated_packets_are_rejected() {
        for message in all_kinds() {
            let good = message.encode();
            // A `CHUNK` stays valid down to one data byte, a `GET_HOSTS`
            // down to its unpadded length; anything shorter isn't.
            let shortest_valid = match message {
                Message::Chunk { .. } => CHUNK_HEADER_LEN + 1,
                Message::GetHosts { .. } => GET_HOSTS_MIN,
                _ => good.len(),
            };
            assert_eq!(Message::decode(&good[..shortest_valid - 1]), None, "{message:?}");
        }
        assert_eq!(Message::decode(&[]), None);
        assert_eq!(Message::decode(&vec![0u8; MAX_PACKET + 1]), None);
    }

    #[test]
    fn get_inv_by_height_must_zero_its_unused_bytes() {
        let mut packet = Message::GetInv(InvQuery::ByHeight(5)).encode();
        packet[HEADER_LEN + 1] = 1;
        assert_eq!(Message::decode(&packet), None);
    }

    #[test]
    fn get_hosts_padding_must_be_zero() {
        let mut packet = Message::GetHosts { nonce: 1, max: 50 }.encode();
        *packet.last_mut().unwrap() = 1;
        assert_eq!(Message::decode(&packet), None);
    }

    #[test]
    fn a_get_hosts_is_padded_to_cover_the_reply_it_asks_for() {
        for max in [0u16, 1, 10, 100, MAX_HOSTS_PER_PACKET as u16] {
            let request = Message::GetHosts { nonce: 0, max }.encode();
            assert!(request.len() * AMPLIFICATION_FACTOR >= hosts_packet_len(max as usize), "max = {max}");
            assert!(hosts_amplification_limit(request.len()) >= max as usize);
        }
    }

    #[test]
    fn chunk_lengths_cover_a_block_exactly() {
        assert_eq!(chunk_count(0), 0);
        assert_eq!(chunk_count(1), 1);
        assert_eq!(chunk_count(CHUNK_LEN), 1);
        assert_eq!(chunk_count(CHUNK_LEN + 1), 2);

        let size = 3 * CHUNK_LEN + 5;
        let lens: Vec<usize> = (0..chunk_count(size)).map(|i| chunk_len(size, i).unwrap()).collect();
        assert_eq!(lens, vec![CHUNK_LEN, CHUNK_LEN, CHUNK_LEN, 5]);
        assert_eq!(chunk_len(size, 4), None);
        assert_eq!(chunk_len(size, usize::MAX), None);
    }
}
