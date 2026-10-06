//! Which network this node is on: **main**, at the consensus proof
//! parameters, or **dev**, at much lighter ones -- for testing, where
//! proving at full strength (minutes per block on a laptop) gets in the
//! way. Chosen once at startup (`--network`); everything that differs
//! between them asks `current()`: the proof parameters and verifying keys
//! (`prover`), the genesis block, the wire protocol's magic bytes (so the
//! two never talk), and the default data directory.
//!
//! **Dev proofs are not secure** -- a few queries at a small blowup,
//! no grinding -- and must never hold anything of value.

#![allow(dead_code)]

use std::sync::OnceLock;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Network {
    Main,
    Dev,
}

impl Network {
    pub fn parse(name: &str) -> Option<Network> {
        match name {
            "main" => Some(Network::Main),
            "dev" => Some(Network::Dev),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Network::Main => "main",
            Network::Dev => "dev",
        }
    }
}

static NETWORK: OnceLock<Network> = OnceLock::new();

/// Choose the network, once, before anything uses it. Returns `false`
/// if one was already chosen (or used: `current` fixes main).
pub fn set(network: Network) -> bool {
    NETWORK.set(network).is_ok() || *NETWORK.get().unwrap() == network
}

/// The network in use: main unless `set` chose otherwise. (Tests can
/// pick dev with the `NETWORK=dev` environment variable.)
pub fn current() -> Network {
    *NETWORK.get_or_init(|| {
        if cfg!(test) && std::env::var("NETWORK").as_deref() == Ok("dev") {
            Network::Dev
        } else {
            Network::Main
        }
    })
}
