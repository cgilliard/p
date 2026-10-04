mod bitmap;
mod block;
mod chain;
mod discovery;
mod e2e;
mod fri;
mod merkle;
mod output;
mod peers;
mod pmmr;
mod poseidon2;
mod pow;
mod prover;
mod storage;
mod transaction;
mod transcript;
mod utxo;
mod wots;

use block::{Block, mine_block, now_millis};
use chain::Chain;
use discovery::Discovery;
use output::Output;
use peers::PeerTable;
use storage::Storage;
use transaction::Transaction;

/// Every block's reward claim, in full -- arbitrary for now. Nothing
/// anywhere checks this is the "right" amount (see `docs/BLOCK_TODO.md`
/// #1): that's permanently the future ZK proof's job, not something
/// this driver or `chain`/`block` enforce in plaintext.
const REWARD: u64 = 50;

/// How many nonces to try before giving up on the current header
/// preimage and re-stamping it with a fresh timestamp (which changes
/// the preimage, opening up an entirely new, unexplored nonce space).
/// Comfortably above what `INITIAL_LEADING_ZERO_BITS` needs almost
/// always, so this is a generous margin, not a tight budget.
const MAX_MINE_ATTEMPTS: u64 = 10_000_000;

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
const INITIAL_LEADING_ZERO_BITS: u32 = 21;

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
const DISCOVERY_TICK_MS: u64 = 250;
/// How long one `recv_from` waits before `Node::poll` returns to tick --
/// well under `DISCOVERY_TICK_MS`, so ticks aren't delayed by it.
const SOCKET_READ_TIMEOUT_MS: u64 = 50;

fn default_data_dir() -> std::path::PathBuf {
    let home = std::env::var("HOME").expect("HOME environment variable must be set");
    std::path::PathBuf::from(home).join(".tabernacle").join("lmdb")
}

/// Command-line options. Hand-parsed -- there are only three, and this
/// crate takes on no dependencies it doesn't need.
struct Args {
    data_dir: std::path::PathBuf,
    port: u16,
    seeds: Vec<std::net::SocketAddrV4>,
}

const USAGE: &str = "usage: p [--data-dir PATH] [--port PORT] [--seed IPV4:PORT]...";

fn parse_args() -> Args {
    let mut args = Args {
        data_dir: default_data_dir(),
        port: DEFAULT_PORT,
        seeds: Vec::new(),
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

/// 32 fresh random bytes for `Discovery`'s nonce key, from the OS.
fn random_key() -> [u8; 32] {
    use std::io::Read;
    let mut key = [0u8; 32];
    std::fs::File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut key))
        .expect("failed to read /dev/urandom");
    key
}

/// Run peer discovery on its own thread for the life of the process.
fn spawn_discovery(storage: &Storage, port: u16, seeds: Vec<std::net::SocketAddrV4>) {
    let socket = std::net::UdpSocket::bind(("0.0.0.0", port)).unwrap_or_else(|e| {
        eprintln!("failed to bind UDP port {port}: {e}");
        std::process::exit(1);
    });
    socket
        .set_read_timeout(Some(std::time::Duration::from_millis(SOCKET_READ_TIMEOUT_MS)))
        .expect("failed to set socket read timeout");
    let table = PeerTable::open(storage, MAX_KNOWN_HOSTS, MAX_HOST_FAILURES).expect("failed to open peer table");
    let config = discovery::Config {
        seeds,
        share_limit: SHARE_LIMIT,
        probe_interval_ms: PROBE_INTERVAL_MS,
        response_timeout_ms: RESPONSE_TIMEOUT_MS,
    };
    let mut node = discovery::Node::new(Discovery::new(config, table, random_key()), socket, DISCOVERY_TICK_MS);
    // Debugging aid for now: log every datagram sent and received,
    // labeled with this node's port so several local nodes' logs are
    // easy to tell apart.
    node.log = Some(format!(":{port}"));
    std::thread::spawn(move || {
        static NEVER_STOP: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
        if let Err(e) = node.run(now_millis, &NEVER_STOP) {
            eprintln!("peer discovery stopped: {e:?}");
        }
    });
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
        println!("Discovery listening on UDP port {} (no seeds given).", args.port);
    } else {
        let seeds: Vec<String> = args.seeds.iter().map(|s| s.to_string()).collect();
        println!("Discovery listening on UDP port {}, seeds: {}.", args.port, seeds.join(", "));
    }
    spawn_discovery(&storage, args.port, args.seeds);
    let peer_table = PeerTable::open(&storage, MAX_KNOWN_HOSTS, MAX_HOST_FAILURES).expect("failed to open peer table");

    println!("Mining -- press Ctrl+C to stop.\n");

    loop {
        // A fresh miner address every block: a WOTS pubkey can only
        // ever sign once, so the reward address must be new each time,
        // not reused. Keying it off the upcoming height guarantees
        // that even across restarts of this process (which reload
        // real, persisted height), it's never reused.
        let next_height = {
            let rtxn = storage.read_txn().expect("failed to open read transaction");
            chain
                .height(&rtxn)
                .expect("failed to read chain height")
                .map(|h| h + 1)
                .unwrap_or(0)
        };
        let mut seed = [0u8; 32];
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

        while !mine_block(&mut block, &target, MAX_MINE_ATTEMPTS) {
            // Exhausted this preimage's nonce space at this difficulty --
            // a fresh timestamp changes the preimage, opening up an
            // entirely new space to search.
            block.header.timestamp = now_millis();
        }

        chain.apply_block(&block).expect("apply_block failed for a block this process just mined");

        print_block(&block);
        let hosts = peer_table.all().expect("failed to read peer table");
        let verified = hosts.iter().filter(|(_, record)| record.is_verified()).count();
        println!("  peers:       {} known, {verified} verified", hosts.len());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
