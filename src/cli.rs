//! The command line: a `>` prompt on the node's terminal (all logging goes
//! to the log file). Each command becomes a `node::Request`, sent to the
//! node's loop; the reply is printed.
//!
//! Payments are slates exchanged as files (`slate`): the sender runs
//! `send`, the receiver `receive`s that file, the sender `finalize`s the
//! one that comes back.

use std::io::{BufRead, Write};
use std::path::PathBuf;
use std::sync::mpsc::Sender;

use crate::node::{Reply, Request};
use crate::output::{UNITS_PER_COIN, parse_amount};

/// The fee `send` uses unless told otherwise: 0.0001 coins.
pub const DEFAULT_FEE: u64 = UNITS_PER_COIN / 10_000;

const HELP: &str = "commands:
  balance                        what the wallet holds
  outputs                        the wallet's outputs and their status
  send <amount> [fee] [file]     start a payment: writes a slate file for the receiver
                                 (fee defaults to 0.0001)
  receive <file>                 answer a payment's slate: writes one back for the sender
  finalize <file>                finish a payment from the receiver's slate and submit it
  cancel <slate id>              undo a payment that was never finalized
  slates                         payments in progress
  status                         chain height, peers, mempool, mining
  mine on|off                    start or stop mining
  seed                           show the wallet's 24 backup words (keep them secret!)
  help                           this
  quit                           stop the node

spending policies (for trying them out; see docs/CONTRACTS.md):
  key [height]                   a new key to list in a policy: one-time, or a key tree of
                                 2^height signatures (16 is the usual; it takes ~45 s)
  hashlock                       a fresh hash-lock preimage and its image
  lock <amount> <policy> [fee]   pay into an output locked to the policy in file <policy>,
                                 one line per branch: `branch threshold=2 keys=<id>,<id>
                                 [after_height=N] [after_age=N] [hashlock=<image>] [rebind=S]`
  spend <policy> <branch> <amount> [to=<policy>] [fee=F] [state=K] [preimage=P] [out=<file>]
                                 write an unsigned spend of a policy output (<amount>) by a
                                 branch (from 0), paying amount - fee to this wallet, or to
                                 another policy; a REBIND branch declares state K
  sign <file>                    sign a transaction file with this wallet's policy keys
  fee <file> <amount>            add a fee input and change from the wallet, signed
  rebind <file> <policy> <branch> <amount>
                                 re-point a REBIND input at another output (before `fee`)
  submit <file>                  submit a fully signed transaction file
  inspect <file>                 summarize a transaction file";

/// A file argument; a leading `~/` means the home directory (there's no
/// shell here to expand it).
fn path(arg: &str) -> PathBuf {
    match (arg.strip_prefix("~/"), std::env::var_os("HOME")) {
        (Some(rest), Some(home)) => PathBuf::from(home).join(rest),
        _ => PathBuf::from(arg),
    }
}

/// Parse one command line; `None` for a blank line.
pub fn parse(line: &str) -> Option<Result<Request, String>> {
    let words: Vec<&str> = line.split_whitespace().collect();
    let (&command, args) = words.split_first()?;
    let amount = |s: &str| parse_amount(s).ok_or_else(|| format!("not an amount: {s} (coins, up to 9 decimals)"));
    let usage = |u: &str| Err(format!("usage: {u}"));
    Some(match (command, args) {
        ("balance" | "bal", []) => Ok(Request::Balance),
        ("outputs", []) => Ok(Request::Outputs),
        ("send", [a, rest @ ..]) if rest.len() <= 2 => (|| {
            let amount = amount(a)?;
            if amount == 0 {
                return Err("the amount must be more than zero".into());
            }
            // An optional fee, then an optional file.
            let (fee, file) = match rest {
                [] => (DEFAULT_FEE, None),
                [x] => match parse_amount(x) {
                    Some(fee) => (fee, None),
                    None => (DEFAULT_FEE, Some(path(x))),
                },
                [fee, file] => (amount_or_err(fee)?, Some(path(file))),
                _ => unreachable!(),
            };
            Ok(Request::Send { amount, fee, file })
        })(),
        ("send", _) => usage("send <amount> [fee] [file]"),
        ("receive", [file]) => Ok(Request::Receive { file: path(file) }),
        ("receive", _) => usage("receive <file>"),
        ("finalize", [file]) => Ok(Request::Finalize { file: path(file) }),
        ("finalize", _) => usage("finalize <file>"),
        ("cancel", [id]) => parse_id(id).map(|id| Request::Cancel { id }),
        ("cancel", _) => usage("cancel <slate id>"),
        ("slates", []) => Ok(Request::Slates),
        ("status", []) => Ok(Request::Status),
        ("mine", ["on"]) => Ok(Request::Mine(true)),
        ("mine", ["off"]) => Ok(Request::Mine(false)),
        ("mine", _) => usage("mine on|off"),
        ("seed", []) => Ok(Request::Seed),
        ("key", []) => Ok(Request::ContractKey { height: 0 }),
        ("key", [h]) => match h.parse::<usize>() {
            Ok(height) if height <= crate::keytree::MAX_HEIGHT => Ok(Request::ContractKey { height }),
            _ => Err(format!("a key tree's height is 0 to {}", crate::keytree::MAX_HEIGHT)),
        },
        ("key", _) => usage("key [height]"),
        ("hashlock", []) => Ok(Request::Hashlock),
        ("lock", [a, policy, rest @ ..]) if rest.len() <= 1 => (|| {
            let fee = match rest {
                [] => DEFAULT_FEE,
                [f] => amount_or_err(f)?,
                _ => unreachable!(),
            };
            Ok(Request::LockFunds { amount: amount(a)?, fee, policy: path(policy) })
        })(),
        ("lock", _) => usage("lock <amount> <policy file> [fee]"),
        ("spend", [policy, branch, a, options @ ..]) => (|| {
            let branch = branch.parse::<u32>().map_err(|_| format!("not a branch number: {branch}"))?;
            let (mut to, mut fee, mut state, mut preimage, mut out) = (None, DEFAULT_FEE, 0, None, None);
            for option in options {
                match option.split_once('=') {
                    Some(("to", "self")) => to = None,
                    Some(("to", file)) => to = Some(path(file)),
                    Some(("fee", f)) => fee = amount_or_err(f)?,
                    Some(("state", k)) => state = k.parse::<u32>().map_err(|_| format!("not a state: {k}"))?,
                    Some(("preimage", p)) => preimage = Some(crate::contract::parse_hash(p)?),
                    Some(("out", file)) => out = Some(path(file)),
                    _ => return Err(format!("unknown option: {option} (to=, fee=, state=, preimage=, out=)")),
                }
            }
            Ok(Request::SpendPolicy { policy: path(policy), branch, amount: amount(a)?, to, fee, state, preimage, out })
        })(),
        ("spend", _) => usage("spend <policy> <branch> <amount> [to=<policy>] [fee=F] [state=K] [preimage=P] [out=<file>]"),
        ("sign", [file]) => Ok(Request::SignFile { file: path(file) }),
        ("sign", _) => usage("sign <file>"),
        ("fee", [file, f]) => amount_or_err(f).map(|fee| Request::AttachFee { file: path(file), fee }),
        ("fee", _) => usage("fee <file> <amount>"),
        ("rebind", [file, policy, branch, a]) => (|| {
            let branch = branch.parse::<u32>().map_err(|_| format!("not a branch number: {branch}"))?;
            Ok(Request::Rebind { file: path(file), policy: path(policy), branch, amount: amount(a)? })
        })(),
        ("rebind", _) => usage("rebind <file> <policy> <branch> <amount>"),
        ("submit", [file]) => Ok(Request::SubmitFile { file: path(file) }),
        ("submit", _) => usage("submit <file>"),
        ("inspect", [file]) => Ok(Request::Inspect { file: path(file) }),
        ("inspect", _) => usage("inspect <file>"),
        ("quit" | "exit", []) => Ok(Request::Quit),
        ("help" | "?", _) => Err(HELP.to_string()),
        _ => Err(format!("unknown command: {line} (try `help`)", line = line.trim())),
    })
}

fn amount_or_err(s: &str) -> Result<u64, String> {
    parse_amount(s).ok_or_else(|| format!("not an amount: {s}"))
}

/// A slate id: 32 hex characters.
fn parse_id(text: &str) -> Result<[u8; 16], String> {
    let bad = || format!("not a slate id: {text} (32 hex characters; see `slates`)");
    if text.len() != 32 || !text.is_ascii() {
        return Err(bad());
    }
    let mut id = [0u8; 16];
    for (i, byte) in id.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&text[2 * i..2 * i + 2], 16).map_err(|_| bad())?;
    }
    Ok(id)
}

/// Read commands from standard input until it closes (or `quit`), sending
/// each to the node and printing its reply. If standard input closes (a
/// node run in the background), the node keeps running without a prompt.
pub fn run(requests: Sender<(Request, Sender<Reply>)>) {
    println!("Type `help` for commands.");
    let stdin = std::io::stdin();
    let mut line = String::new();
    loop {
        print!("> ");
        let _ = std::io::stdout().flush();
        line.clear();
        match stdin.lock().read_line(&mut line) {
            Ok(0) | Err(_) => return,
            Ok(_) => {}
        }
        let request = match parse(&line) {
            None => continue,
            Some(Err(message)) => {
                println!("{message}");
                continue;
            }
            Some(Ok(request)) => request,
        };
        let quit = matches!(request, Request::Quit);
        let (reply_to, reply) = std::sync::mpsc::channel();
        if requests.send((request, reply_to)).is_err() {
            return;
        }
        match reply.recv() {
            Ok(Ok(text)) => println!("{text}"),
            Ok(Err(message)) => println!("error: {message}"),
            Err(_) => return,
        }
        if quit {
            return;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ok(line: &str) -> Request {
        parse(line).unwrap().unwrap()
    }

    #[test]
    fn commands_parse() {
        assert!(parse("   ").is_none());
        assert!(matches!(ok("balance"), Request::Balance));
        assert!(matches!(ok("  bal  "), Request::Balance));
        assert!(matches!(ok("send 2.5"), Request::Send { amount: 2_500_000_000, fee: DEFAULT_FEE, file: None }));
        assert!(matches!(ok("send 2.5 0.001"), Request::Send { amount: 2_500_000_000, fee: 1_000_000, file: None }));
        match ok("send 1 out.slate") {
            Request::Send { amount, fee, file } => {
                assert_eq!((amount, fee), (UNITS_PER_COIN, DEFAULT_FEE));
                assert_eq!(file.unwrap(), PathBuf::from("out.slate"));
            }
            other => panic!("{other:?}"),
        }
        assert!(matches!(ok("send 1 0 x.slate"), Request::Send { fee: 0, .. }));
        assert!(matches!(ok("receive a.s1.slate"), Request::Receive { .. }));
        assert!(matches!(ok("finalize a.s2.slate"), Request::Finalize { .. }));
        assert!(matches!(ok("cancel 00112233445566778899aabbccddeeff"), Request::Cancel { id } if id[15] == 0xff));
        assert!(matches!(ok("mine off"), Request::Mine(false)));
        assert!(matches!(ok("quit"), Request::Quit));
    }

    #[test]
    fn mistakes_explain_themselves() {
        let err = |line: &str| parse(line).unwrap().unwrap_err();
        assert!(err("send").starts_with("usage: send"));
        assert!(err("send abc").contains("not an amount"));
        assert!(err("send 0").contains("more than zero"));
        assert!(err("send 1 x.slate extra stuff").starts_with("usage"));
        assert!(err("cancel xyz").contains("not a slate id"));
        assert!(err("mine maybe").starts_with("usage"));
        assert!(err("fly").contains("unknown command"));
        assert!(err("help").contains("finalize <file>"));
    }

    #[test]
    fn policy_commands_parse() {
        assert!(matches!(ok("key"), Request::ContractKey { height: 0 }));
        assert!(matches!(ok("key 16"), Request::ContractKey { height: 16 }));
        assert!(parse("key 21").unwrap().is_err());
        assert!(matches!(ok("hashlock"), Request::Hashlock));
        assert!(matches!(ok("lock 2 p.txt"), Request::LockFunds { amount: 2_000_000_000, fee: DEFAULT_FEE, .. }));
        assert!(matches!(ok("lock 2 p.txt 0.01"), Request::LockFunds { fee: 10_000_000, .. }));
        match ok("spend p.txt 1 3 to=q.txt fee=0 state=7 out=u.tx") {
            Request::SpendPolicy { branch, amount, to, fee, state, preimage, out, .. } => {
                assert_eq!((branch, amount, fee, state, preimage), (1, 3 * UNITS_PER_COIN, 0, 7, None));
                assert_eq!(to.unwrap(), PathBuf::from("q.txt"));
                assert_eq!(out.unwrap(), PathBuf::from("u.tx"));
            }
            other => panic!("{other:?}"),
        }
        assert!(matches!(ok("spend p.txt 0 1"), Request::SpendPolicy { to: None, fee: DEFAULT_FEE, state: 0, .. }));
        assert!(parse("spend p.txt 0 1 colour=red").unwrap().unwrap_err().contains("unknown option"));
        assert!(parse("spend p.txt 0 1 preimage=zz").unwrap().is_err());
        assert!(matches!(ok("sign u.tx"), Request::SignFile { .. }));
        assert!(matches!(ok("fee u.tx 0.001"), Request::AttachFee { fee: 1_000_000, .. }));
        assert!(matches!(ok("rebind u.tx p.txt 0 5"), Request::Rebind { branch: 0, amount: 5_000_000_000, .. }));
        assert!(matches!(ok("submit u.tx"), Request::SubmitFile { .. }));
        assert!(matches!(ok("inspect u.tx"), Request::Inspect { .. }));
    }

    #[test]
    fn home_relative_paths_are_expanded() {
        let home = std::path::PathBuf::from(std::env::var_os("HOME").unwrap());
        match parse("receive ~/a.slate") {
            Some(Ok(Request::Receive { file })) => assert_eq!(file, home.join("a.slate")),
            other => panic!("{other:?}"),
        }
        match parse("finalize ./~/b") {
            Some(Ok(Request::Finalize { file })) => assert_eq!(file, std::path::PathBuf::from("./~/b")),
            other => panic!("{other:?}"),
        }
    }

}
