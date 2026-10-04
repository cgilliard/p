mod bitmap;
mod block;
mod chain;
mod discovery;
mod e2e;
mod fri;
mod merkle;
mod net;
mod output;
mod peers;
mod pmmr;
mod poseidon2;
mod pow;
mod prover;
mod storage;
mod transaction;
mod transfer;
mod transcript;
mod utxo;
mod wire;
mod wots;

use block::{Block, mine_block, now_millis};
use chain::{AcceptOutcome, BlockReader, Chain};
use discovery::Discovery;
use net::Command;
use std::net::SocketAddrV4;
use std::sync::mpsc::{Receiver, Sender};
use output::Output;
use peers::PeerTable;
use storage::Storage;
use transaction::Transaction;

/// Every block's reward claim, in full -- arbitrary for now. Nothing
/// anywhere checks this is the "right" amount (see `docs/BLOCK_TODO.md`
/// #1): that's permanently the future ZK proof's job, not something
/// this driver or `chain`/`block` enforce in plaintext.
const REWARD: u64 = 50;

/// How many leading zero bits this driver's starting PoW target has --
/// the knob to turn if the first few blocks feel too fast or too slow.
/// Whole bytes (multiples of 8) are a 256x jump each, too coarse to
/// dial in by hand -- see `pow::max_hash_with_leading_zero_bits`'s
/// docs -- so this is in bits, not bytes: 16 was too fast, 24 too
/// slow, 20 closer but still a bit fast. Only an informed guess, not a
/// calibration: `Chain`'s retargeting corrects for however wrong it
/// actually is after the first `RETARGET_INTERVAL` blocks regardless,
/// and this number is independent of `block::INITIAL_MAX_HASH` (which
/// stays fixed and easy, since tests built around it need to mine
/// quickly -- see that constant's docs).
const INITIAL_LEADING_ZERO_BITS: u32 = 23;

/// Retargeting knobs for this driver's actual run -- independent of
/// `chain::DifficultyConfig::for_tests`'s own numbers (see that
/// method's docs for why they're deliberately never the same values).
/// `target_block_time_ms` here is `10_000` (10 real seconds), not the
/// test suite's `10` (milliseconds) -- same window size, genuinely
/// different real-world pace, which is exactly the point of the two
/// being independent numbers.
const RETARGET_INTERVAL: u64 = 10;
const TARGET_BLOCK_TIME_MS: u64 = 10_000;
const MAX_ADJUSTMENT_FACTOR: u64 = 4;

/// How many blocks a reorg is ever allowed to unwind in this driver's
/// actual run -- independent of the test suite's own (much smaller)
/// number, same reasoning as the retargeting knobs above. 1000 is a
/// starting point, not a calibration.
const MAX_REORG_DEPTH: u64 = 1000;

/// UDP port discovery listens on when `--port` isn't given.
const DEFAULT_PORT: u16 = 7701;

/// Peer discovery knobs for this driver's actual run (see `discovery`
/// and `peers` for what each one does). Starting points, not
/// calibrations.
const SHARE_LIMIT: u16 = 100;
const MAX_KNOWN_HOSTS: usize = 1000;
const MAX_HOST_FAILURES: u8 = 3;
const PROBE_INTERVAL_MS: u64 = 60_000;
const RESPONSE_TIMEOUT_MS: u64 = 5_000;
/// Block transfer knobs (see `transfer`). Also starting points.
const MAX_BLOCK_BYTES: usize = 2 * 1024 * 1024;
const CHUNK_WINDOW: u16 = 32;
const CHUNK_TIMEOUT_MS: u64 = 1_000;
const MAX_CHUNK_RETRIES: u32 = 5;
const MAX_DOWNLOADS: usize = 4;
const SYNC_INTERVAL_MS: u64 = 10_000;

/// How often the network thread runs both protocols' ticks.
const NETWORK_TICK_MS: u64 = 100;
/// How long one `recv_from` waits before `Node::poll` returns to tick --
/// well under `NETWORK_TICK_MS`, so ticks aren't delayed by it.
const SOCKET_READ_TIMEOUT_MS: u64 = 20;

/// Nonces tried per mining batch. Between batches the miner hands any
/// blocks the network received to the chain, and starts over on a new
/// template if the tip moved -- so this bounds how long it can keep
/// mining on a stale tip.
const MINE_BATCH: u64 = 200_000;

fn default_data_dir() -> std::path::PathBuf {
    let home = std::env::var("HOME").expect("HOME environment variable must be set");
    std::path::PathBuf::from(home).join(".tabernacle").join("lmdb")
}

/// Command-line options. Hand-parsed -- there are only a few, and this
/// crate takes on no dependencies it doesn't need.
struct Args {
    data_dir: std::path::PathBuf,
    port: u16,
    seeds: Vec<SocketAddrV4>,
    mine: bool,
}

const USAGE: &str = "usage: p [--data-dir PATH] [--port PORT] [--seed IPV4:PORT]... [--no-mine]";

fn parse_args() -> Args {
    let mut args = Args {
        data_dir: default_data_dir(),
        port: DEFAULT_PORT,
        seeds: Vec::new(),
        mine: true,
    };
    let mut iter = std::env::args().skip(1);
    while let Some(flag) = iter.next() {
        let mut value = || {
            iter.next().unwrap_or_else(|| {
                eprintln!("{flag} needs a value\n{USAGE}");
                std::process::exit(2);
            })
        };
        match flag.as_str() {
            "--data-dir" => args.data_dir = value().into(),
            "--port" => {
                let v = value();
                args.port = v.parse().unwrap_or_else(|_| {
                    eprintln!("invalid port: {v}\n{USAGE}");
                    std::process::exit(2);
                });
            }
            "--seed" => {
                let v = value();
                args.seeds.push(v.parse().unwrap_or_else(|_| {
                    eprintln!("invalid seed (expected IPV4:PORT): {v}\n{USAGE}");
                    std::process::exit(2);
                }));
            }
            "--no-mine" => args.mine = false,
            "--help" | "-h" => {
                println!("{USAGE}");
                std::process::exit(0);
            }
            other => {
                eprintln!("unknown argument: {other}\n{USAGE}");
                std::process::exit(2);
            }
        }
    }
    args
}

/// 32 fresh random bytes from the OS.
fn random_key() -> [u8; 32] {
    use std::io::Read;
    let mut key = [0u8; 32];
    std::fs::File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut key))
        .expect("failed to read /dev/urandom");
    key
}

/// Run the network -- discovery and block transfer -- on its own thread
/// for the life of the process. Returns the channel finished downloads
/// arrive on (each with the peer it came from) and the one to send it
/// `Command`s on.
fn spawn_network(storage: &Storage, port: u16, seeds: Vec<SocketAddrV4>) -> (Receiver<(Block, SocketAddrV4)>, Sender<Command>) {
    let socket = std::net::UdpSocket::bind(("0.0.0.0", port)).unwrap_or_else(|e| {
        eprintln!("failed to bind UDP port {port}: {e}");
        std::process::exit(1);
    });
    socket
        .set_read_timeout(Some(std::time::Duration::from_millis(SOCKET_READ_TIMEOUT_MS)))
        .expect("failed to set socket read timeout");
    let table = PeerTable::open(storage, MAX_KNOWN_HOSTS, MAX_HOST_FAILURES).expect("failed to open peer table");
    let discovery = Discovery::new(
        discovery::Config {
            seeds,
            share_limit: SHARE_LIMIT,
            probe_interval_ms: PROBE_INTERVAL_MS,
            response_timeout_ms: RESPONSE_TIMEOUT_MS,
        },
        table,
        random_key(),
    );
    let transfer = transfer::Transfer::new(transfer::Config {
        max_block_bytes: MAX_BLOCK_BYTES,
        window: CHUNK_WINDOW,
        chunk_timeout_ms: CHUNK_TIMEOUT_MS,
        max_retries: MAX_CHUNK_RETRIES,
        max_downloads: MAX_DOWNLOADS,
        sync_interval_ms: SYNC_INTERVAL_MS,
    });
    let reader = BlockReader::open(storage).expect("failed to open block reader");
    let mut node = net::Node::new(discovery, transfer, reader, socket, NETWORK_TICK_MS);
    // Debugging aid for now: log every datagram sent and received,
    // labeled with this node's port so several local nodes' logs are
    // easy to tell apart.
    node.log = Some(format!(":{port}"));

    let (blocks_tx, blocks_rx) = std::sync::mpsc::channel();
    let (commands_tx, commands_rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        static NEVER_STOP: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
        let deliver = |block, from| {
            let _ = blocks_tx.send((block, from));
        };
        if let Err(e) = node.run(now_millis, &NEVER_STOP, deliver, &commands_rx) {
            eprintln!("network stopped: {e:?}");
        }
    });
    (blocks_rx, commands_tx)
}

/// Tell the network to announce our current tip to every peer but
/// `except`.
fn announce_tip(reader: &BlockReader, commands: &Sender<Command>, except: Option<SocketAddrV4>) {
    let Some((height, hash)) = reader.tip().expect("failed to read tip") else {
        return;
    };
    let size = reader
        .block_bytes(hash)
        .expect("failed to read tip block")
        .expect("tip block is stored")
        .len() as u32;
    let _ = commands.send(Command::Announce {
        hash,
        height,
        size,
        except,
    });
}

/// Hand every block the network has received so far to the chain (see
/// `process_one`). Returns whether the tip moved.
fn process_received(
    chain: &mut Chain,
    reader: &BlockReader,
    received: &Receiver<(Block, SocketAddrV4)>,
    commands: &Sender<Command>,
) -> bool {
    let mut tip_moved = false;
    while let Ok((block, from)) = received.try_recv() {
        tip_moved |= process_one(chain, reader, commands, block, from);
    }
    tip_moved
}

/// Hand one block received from `from` to the chain, announcing a new
/// tip or asking for a missing parent as needed. Returns whether the tip
/// moved -- compared before and after, since accepting a block can also
/// connect waiting orphans and move the tip further than the block itself.
fn process_one(chain: &mut Chain, reader: &BlockReader, commands: &Sender<Command>, block: Block, from: SocketAddrV4) -> bool {
    let height = block.header.height;
    let prev_hash = block.header.prev_hash;
    let tip_before = reader.tip().expect("failed to read tip");
    match chain.accept_block(block.clone()) {
        Ok(AcceptOutcome::Applied) => {
            println!("received block #{height} from {from}");
            print_block(&block);
        }
        Ok(AcceptOutcome::Reorged { unwound, applied }) => {
            println!("received block #{height} from {from}: reorg, unwound {unwound}, applied {applied}");
            print_block(&block);
        }
        Ok(AcceptOutcome::Orphaned) => {
            println!("received block #{height} from {from}: orphan, asking for its parent");
            let _ = commands.send(Command::RequestBlock { hash: prev_hash, from });
        }
        Ok(AcceptOutcome::StoredAsSideBranch) => println!("received block #{height} from {from}: side branch"),
        Ok(AcceptOutcome::AlreadyKnown) => {}
        Err(e) => println!("rejected block #{height} from {from}: {e}"),
    }
    let tip_moved = reader.tip().expect("failed to read tip") != tip_before;
    if tip_moved {
        announce_tip(reader, commands, Some(from));
    }
    tip_moved
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Convert a Unix timestamp, in **milliseconds**, into a human-readable
/// "YYYY-MM-DD HH:MM:SS.mmm UTC" string. A small, self-contained civil-
/// calendar conversion -- no time zone database needed since this is
/// always UTC, and no new dependency needed for just this. The
/// year/month/day half is Howard Hinnant's `civil_from_days`
/// algorithm (http://howardhinnant.github.io/date_algorithms.html),
/// chosen because it's a well-known, easy-to-verify closed form rather
/// than a loop over "days in this month" by hand.
fn format_timestamp(unix_millis: u64) -> String {
    let unix_secs = unix_millis / 1000;
    let millis = unix_millis % 1000;
    let days = (unix_secs / 86400) as i64;
    let secs_of_day = unix_secs % 86400;
    let (year, month, day) = civil_from_days(days);
    let hour = secs_of_day / 3600;
    let minute = (secs_of_day % 3600) / 60;
    let second = secs_of_day % 60;
    format!("{year:04}-{month:02}-{day:02} {hour:02}:{minute:02}:{second:02}.{millis:03} UTC")
}

/// Days since the Unix epoch (1970-01-01) -> (year, month, day) in the
/// proleptic Gregorian calendar.
fn civil_from_days(z: i64) -> (i64, u32, u32) {
    let z = z + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = (z - era * 146_097) as u64; // day of era, [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146_096) / 365; // year of era, [0, 399]
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // day of year, [0, 365]
    let mp = (5 * doy + 2) / 153; // month, shifted so March = 0, [0, 11]
    let day = (doy - (153 * mp + 2) / 5 + 1) as u32; // [1, 31]
    let month = if mp < 10 { mp + 3 } else { mp - 9 } as u32; // [1, 12]
    let year = if month <= 2 { y + 1 } else { y };
    (year, month, day)
}

/// A 256-bit big-endian integer as an `f64` -- approximate past 2^53,
/// which is fine for display.
fn u256_to_f64(value: [u8; 32]) -> f64 {
    value.iter().fold(0.0, |acc, &byte| acc * 256.0 + byte as f64)
}

/// A hash rate with a readable unit: "812.3 kH/s".
fn format_hash_rate(hashes_per_sec: f64) -> String {
    let units = ["H/s", "kH/s", "MH/s", "GH/s", "TH/s"];
    let mut value = hashes_per_sec;
    let mut unit = 0;
    while value >= 1000.0 && unit < units.len() - 1 {
        value /= 1000.0;
        unit += 1;
    }
    format!("{value:.1} {}", units[unit])
}

/// A duration in seconds with a readable unit: "2.6 s", "4.2 min", "1.5 h".
fn format_duration(secs: f64) -> String {
    if secs < 120.0 {
        format!("{secs:.1} s")
    } else if secs < 7200.0 {
        format!("{:.1} min", secs / 60.0)
    } else {
        format!("{:.1} h", secs / 3600.0)
    }
}

/// This node's mining speed on the block it just mined, and how long a
/// block at `target` would take on average at that speed -- set against
/// the network's intended block time.
fn print_mining_stats(hashes: u64, elapsed: std::time::Duration, target: &[u8; 32]) {
    let secs = elapsed.as_secs_f64().max(1e-9);
    let rate = hashes as f64 / secs;
    let expected_hashes = u256_to_f64(pow::work_for_target(*target));
    println!(
        "  hash rate:   {} ({hashes} hashes in {})",
        format_hash_rate(rate),
        format_duration(secs)
    );
    println!(
        "  expected:    {} per block at this rate (target {})",
        format_duration(expected_hashes / rate),
        format_duration(TARGET_BLOCK_TIME_MS as f64 / 1000.0)
    );
}

fn print_block(block: &Block) {
    println!("------------------------------------------------------------");
    println!("block #{}", block.header.height);
    println!("  hash:        {}", hex(&block.header.hash()));
    println!("  prev_hash:   {}", hex(&block.header.prev_hash));
    println!(
        "  timestamp:   {} ({})",
        block.header.timestamp,
        format_timestamp(block.header.timestamp)
    );
    println!("  nonce:       {}", hex(&block.header.nonce));
    println!("  pmmr_root:   {}", hex(&block.header.pmmr_root));
    println!("  bitmap_root: {}", hex(&block.header.bitmap_root));
    println!("  body_hash:   {}", hex(&block.header.body_hash));
    println!("  inputs:      {}", block.body.inputs.len());
    for commitment in &block.body.inputs {
        println!("    - {}", hex(commitment));
    }
    println!("  outputs:     {}", block.body.outputs.len());
    for commitment in &block.body.outputs {
        println!("    + {}", hex(commitment));
    }
}

fn main() {
    let args = parse_args();
    let path = args.data_dir.clone();
    // `Storage::open` would transparently create-or-load either way
    // (LMDB behaves the same regardless), but checking first lets us
    // say which one actually happened.
    let is_new = !path.exists();
    if is_new {
        println!("No existing chain found at {} -- creating a new one.", path.display());
    } else {
        println!("Found an existing chain at {} -- loading it.", path.display());
    }

    let storage = Storage::open(&path).expect("failed to open storage");
    let difficulty = chain::DifficultyConfig {
        initial_target: pow::max_hash_with_leading_zero_bits(INITIAL_LEADING_ZERO_BITS),
        interval: RETARGET_INTERVAL,
        target_block_time_ms: TARGET_BLOCK_TIME_MS,
        max_adjustment_factor: MAX_ADJUSTMENT_FACTOR,
    };
    let mut chain = Chain::open(&storage, difficulty, MAX_REORG_DEPTH).expect("failed to open chain");

    {
        let rtxn = storage.read_txn().expect("failed to open read transaction");
        match chain.height(&rtxn).expect("failed to read chain height") {
            Some(height) => {
                let tip = chain.tip_hash(&rtxn).expect("failed to read tip hash");
                println!("Resuming at height {height}, tip {}.", hex(&tip));
            }
            None => println!("Starting from genesis."),
        }
    }

    if args.seeds.is_empty() {
        println!("Listening on UDP port {} (no seeds given).", args.port);
    } else {
        let seeds: Vec<String> = args.seeds.iter().map(|s| s.to_string()).collect();
        println!("Listening on UDP port {}, seeds: {}.", args.port, seeds.join(", "));
    }
    let (received, commands) = spawn_network(&storage, args.port, args.seeds);
    let reader = BlockReader::open(&storage).expect("failed to open block reader");
    let peer_table = PeerTable::open(&storage, MAX_KNOWN_HOSTS, MAX_HOST_FAILURES).expect("failed to open peer table");

    if !args.mine {
        println!("Following the network without mining -- press Ctrl+C to stop.\n");
        loop {
            // Block until something arrives, then handle it (and anything
            // else already waiting).
            let Ok((block, from)) = received.recv() else {
                eprintln!("network thread exited");
                return;
            };
            process_one(&mut chain, &reader, &commands, block, from);
            process_received(&mut chain, &reader, &received, &commands);
        }
    }

    println!("Mining -- press Ctrl+C to stop.\n");

    // Mixed into every reward key, so this node's keys differ from every
    // other node's (and from its own in any earlier run) even at the
    // same height.
    let key_salt = random_key();

    loop {
        process_received(&mut chain, &reader, &received, &commands);

        // A fresh miner address every block: a WOTS pubkey can only
        // ever sign once, so the reward address must be new each time,
        // not reused. Keyed off the upcoming height plus this run's
        // random salt.
        let next_height = {
            let rtxn = storage.read_txn().expect("failed to open read transaction");
            chain
                .height(&rtxn)
                .expect("failed to read chain height")
                .map(|h| h + 1)
                .unwrap_or(0)
        };
        let mut seed = key_salt;
        seed[..8].copy_from_slice(&next_height.to_be_bytes());
        let (_secret_key, public_key) = wots::keygen(&seed);

        let mut reward_tx = Transaction::new();
        reward_tx.add_output(Output::new(&public_key, REWARD)).expect("fresh transaction never finalized");
        let transactions = vec![reward_tx];

        let unproven = chain.build_block(&transactions).expect("build_block failed");
        let target = unproven.target;
        let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &transactions)
            .expect("prove_block failed (the stub prover should always succeed)");
        let mut block = unproven.finish(proof);

        let started = std::time::Instant::now();
        let mut full_batches: u64 = 0;
        let mined = loop {
            if mine_block(&mut block, &target, MINE_BATCH) {
                break true;
            }
            full_batches += 1;
            if process_received(&mut chain, &reader, &received, &commands) {
                break false; // the tip moved under us: this template is stale
            }
            // A fresh timestamp changes the preimage, opening up an
            // entirely new nonce space for the next batch.
            block.header.timestamp = now_millis();
        };
        if !mined {
            continue;
        }

        // `pow::mine` counts nonces up from 0, with the counter in the
        // nonce's first 8 bytes (little-endian) -- so the winning nonce
        // says exactly how many tries the final batch took.
        let last_batch = u64::from_le_bytes(block.header.nonce[..8].try_into().unwrap()) + 1;
        let hashes = full_batches * MINE_BATCH + last_batch;
        let elapsed = started.elapsed();

        match chain.accept_block(block.clone()) {
            Ok(AcceptOutcome::Applied) => {
                print_block(&block);
                print_mining_stats(hashes, elapsed, &target);
                let hosts = peer_table.all().expect("failed to read peer table");
                let verified = hosts.iter().filter(|(_, record)| record.is_verified()).count();
                println!("  peers:       {} known, {verified} verified", hosts.len());
                announce_tip(&reader, &commands, None);
            }
            other => println!("mined block #{} was not applied: {other:?}", block.header.height),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u256_to_f64_matches_small_values_exactly() {
        let mut value = [0u8; 32];
        value[30] = 1;
        value[31] = 2;
        assert_eq!(u256_to_f64(value), 258.0);
        assert_eq!(u256_to_f64([0u8; 32]), 0.0);
    }

    #[test]
    fn hash_rates_pick_a_readable_unit() {
        assert_eq!(format_hash_rate(950.0), "950.0 H/s");
        assert_eq!(format_hash_rate(812_345.0), "812.3 kH/s");
        assert_eq!(format_hash_rate(2_500_000.0), "2.5 MH/s");
    }

    #[test]
    fn durations_pick_a_readable_unit() {
        assert_eq!(format_duration(2.64), "2.6 s");
        assert_eq!(format_duration(252.0), "4.2 min");
        assert_eq!(format_duration(9000.0), "2.5 h");
    }

    #[test]
    fn epoch_is_new_years_day_1970() {
        assert_eq!(format_timestamp(0), "1970-01-01 00:00:00.000 UTC");
    }

    #[test]
    fn one_day_later_rolls_the_date_over() {
        assert_eq!(format_timestamp(86_400_000), "1970-01-02 00:00:00.000 UTC");
    }

    #[test]
    fn time_of_day_decomposes_into_hours_minutes_seconds() {
        // 1h, 1m, 1s past midnight -- same day as the epoch.
        assert_eq!(format_timestamp(3_661_000), "1970-01-01 01:01:01.000 UTC");
    }

    #[test]
    fn milliseconds_decompose_too() {
        assert_eq!(format_timestamp(1_234), "1970-01-01 00:00:01.234 UTC");
    }

    #[test]
    fn a_widely_cited_reference_timestamp_matches() {
        // 1_700_000_000 (seconds) is a commonly-referenced round value,
        // widely cited (independently of this code) as this exact
        // moment -- scaled up to milliseconds, `format_timestamp`'s
        // actual unit now.
        assert_eq!(format_timestamp(1_700_000_000_000), "2023-11-14 22:13:20.000 UTC");
    }
}
