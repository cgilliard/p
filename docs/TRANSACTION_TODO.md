# Transactions: TODO

Status: **in progress** (2026-10-05). Decided: Grin-style **slates**,
exchanged as **files** to start (`send` / `receive` / `finalize`).
Built: `keychain.rs`, `slate.rs`, `wallet.rs`, transaction encoding,
the node loop (`node.rs`), the CLI (`cli.rs`), a minimal local mempool
(`mempool.rs`), and transaction relay between peers (`txrelay.rs`).

The chain can already *carry* transactions -- consensus validates spends,
blocks prove them (direct or tree proofs), and tests spend outputs end to
end -- but nothing lets a user actually make one. This document plans
everything between "I have coins" and "the recipient has them":

1. a node architecture that can do more than mine (phase 0)
2. a keychain and wallet (phases 1-2)
3. the miner paying its rewards into that wallet (phase 3)
4. a CLI in the node process (phase 4)
5. building and signing transactions (phase 5)
6. a mempool (phase 6)
7. relaying transactions between nodes (phase 7)
8. mining blocks from the mempool (phase 8)
9. receiving payments (phase 9)
10. end-to-end tests (phase 10)

Each phase is usable and testable on its own. Open questions are
collected at the end; several shape the later phases and should be
settled before we get there.

## Constraints that shape everything

These come from choices already made, and make this wallet unlike a
Bitcoin wallet in a few important ways:

- **Keys are one-time (WOTS).** A key can sign *one* message, ever.
  Signing two different messages with the same key leaks enough of the
  secret to forge. So: every output gets a fresh key; change goes to a
  fresh key; and once a wallet has signed a transaction spending an
  output, that exact transaction is the *only* one it may ever sign for
  that output -- rebroadcast it, never rebuild and re-sign it (no
  fee-bumping by re-signing). The wallet must persist a signature
  *before* releasing it.
- **No public key derivation.** Hash-based keys have no equivalent of
  BIP32's public (xpub) derivation, so "HD" here means deterministic
  *private* derivation from a seed: key `i` = `keygen(KDF(seed, i))`.
  Only the seed holder can generate addresses.
- **Amounts are hidden on chain.** An output is
  `commitment = H(pubkey_hash ‖ amount)`; nothing on chain says who it
  belongs to or how much it holds. A recipient can only find a payment by
  computing the exact commitment they expect, which requires knowing
  the amount. This drives the payment model (phase 9) and wallet
  recovery (open questions).
- **The miner proves transactions from plaintext.** A transaction
  travels as plaintext -- public keys, amounts, signatures -- because the
  miner needs the witness to prove it. Amounts are hidden *on chain*,
  but every node relaying a transaction sees it. See open questions
  ("client-side proving") for the path to fixing that.
- **Transactions are big.** A WOTS public key and a signature are about
  2 KB each, so an input is about 4.2 KB in plaintext; outputs are 40
  bytes. A typical transaction spans several UDP packets (≤ 1200 bytes
  each), so relay needs the chunked transfer blocks already use.
- **A transaction with more than 10 inputs** can't go into a tree-proven
  block (`prover::CHUNK_SHAPE`), only a direct one. Wallets should keep
  transactions within that (consolidating in steps if needed).

## Phase 0 -- node architecture (done: `node.rs`)

Today `main` owns the `Chain` and alternates mining batches with
handling received blocks. The CLI, the wallet and the mempool all need
the chain too, so make that explicit:

- [x] The **node loop** (on the main thread) owns `Chain`, `Mempool`
      and `Wallet` and handles network events, CLI requests and mining
      work one at a time. The CLI reads the terminal on its own thread and
      talks to the loop through a request + reply channel.
- [x] Mining stays interleaved (batches of nonces between events), but
      becomes something the loop does when enabled, not the loop itself
      -- so mining can be switched on and off at runtime.
- [x] Proving (2 s for a small block, minutes for a tree) shouldn't
      freeze the CLI: run it on a worker thread and hand the proof back
      as an event; a block that's gone stale by then is dropped.
- [x] `quit` stops the node (LMDB commits are already durable, so
      Ctrl+C is safe too).

## Phase 1 -- keychain (`keychain.rs`, `mnemonic.rs`: done)

- [x] `Keychain::random()` (production), `from_seed` / `from_seed_hex`
      (restore), `Keychain::test(label)` (reproducible, per-test keys);
      `derive(KeyId { account, index })`, `public_key`, `secret_key`,
      `output(id, amount)`. The seed is never printed (`Debug`) and is
      zeroed on drop.
- [x] **Seed**: 32 random bytes (from the OS), created on first run
      (`Wallet::open`); restore with `Wallet::open_with`.
- [x] **Mnemonic**: the seed as 24 BIP39 English words (`mnemonic.rs`);
      `seed` shows them; `--recover` restores a wallet from them alone
      (every output carries a recovery nonce -- see `docs/RECOVERY.md`).
- [x] **Derivation**: `key_seed = hash_bytes_32("tabernacle-keychain-v1" ‖
      seed ‖ account ‖ index)`, then `wots::keygen(key_seed)`. Keys are
      never stored, only the seed and the next unused index; any key can
      be re-derived.
- [x] **Index discipline**: an index is handed out exactly once (for an
      address, a change output, or a mining reward), and the next index
      is persisted *before* the key is used, so a crash can't hand the
      same key out twice.
- [x] **Seed at rest** (first step): in the wallet store, in a directory
      only the user can read (0700). Password encryption later (open
      question).

## Phase 2 -- wallet store (`wallet.rs`: done)

Outputs' chain status is *derived*, not replayed: on each `refresh` the
wallet checks whether each output is unspent on chain, and combines that
with whether it signed a spend (only we can spend our outputs). That
makes it self-healing across reorgs. The chain is seen through a small
`ChainView` trait (tip height, `is_unspent`).

- [x] Its own LMDB database(s) in the data directory (or `--wallet-dir`),
      separate from consensus state.
- [x] **Outputs** the wallet owns: commitment, amount, key index, and a
      status -- *expected* (we know it should appear: a reward we're
      mining, change, or an output we added when receiving), *confirmed* (in the active chain,
      at height h), *spending* (in a transaction we've signed),
      *spent* (that transaction confirmed).
- [x] **Signed transactions** we've released, by the outputs they spend
      (the one-time-key rule: this is what we rebroadcast, never
      re-sign).
- [x] **Follow the chain**: `refresh(&ChainView)` after every chain
      change re-derives each output's status (see above), so reorgs need
      no special handling. `Chain::view()` implements `ChainView`.
- [x] **Balance**: confirmed (with a confirmation count), pending
      (expected or unconfirmed), and locked (spending).

## Phase 3 -- mining to the wallet (done)

- [x] The node opens its wallet at startup (`<data-dir>/wallet`, or
      `--wallet-dir`), refreshes it after every chain change through
      `Chain::view()` (a `ChainView`), and logs the balance when it
      changes. A template abandoned before it's mined has its expected
      reward forgotten.
- [x] The reward output pays to a fresh wallet key; the wallet records
      it as *expected* (commitment and amount are both known) before the
      block is mined.
- [ ] Once blocks carry other transactions, the reward claims
      `REWARD + fees`, all to that key.
- [x] When our block is orphaned or loses a reorg, its reward output
      goes back to expected/unconfirmed (phase 2's unwinding).
- [x] **Coinbase maturity** (wallet policy, `COINBASE_MATURITY` = 10;
      whether consensus should enforce it stays an open question): Bitcoin forbids spending a
      reward for 100 blocks, so a reorg can't erase coins that were
      already spent onward. At minimum the wallet should not *spend* an
      immature reward; whether consensus should enforce it is a separate
      decision.

## Phase 4 -- CLI (done: `cli.rs`)

A prompt on the node's own terminal (all logging already goes to the log
file). Payments are slates passed as files (phase 5):

```
> balance
  confirmed: 12.000000000   (12 outputs, height 341)
  pending:    1.000000000
> send 2.5 [fee]
  wrote 3f2a….s1.slate      (give this to the receiver)
> receive 3f2a….s1.slate
  wrote 3f2a….s2.slate      (give this back to the sender)
> finalize 3f2a….s2.slate
  signed and submitted: txid 9c1e…
> outputs
> history
> status          (height, tip, peers, mempool size, mining on/off, hash rate)
> mine on | off
> mnemonic        (show the backup words, with a warning)
> help | quit
```

- [x] Line-oriented reader on stdin, commands as requests to the node
      (phase 0), replies printed: `balance`, `outputs`, `send <amount>
      [fee] [file]`, `receive <file>`, `finalize <file>`, `cancel <id>`,
      `slates`, `status`, `mine on|off`, `seed`, `help`, `quit`. If stdin
      closes (a node run in the background) the node keeps running.
- [x] Amounts in whole coins with 9 decimals (1 coin = 10^9 units, the
      reward is 1 coin), parsed and printed exactly (integer arithmetic,
      no floats).
- [ ] (Later) network transports for slates instead of files.
- [ ] Non-interactive use for scripts and tests (`--exec "balance"`, or
      the same requests over a local socket later).

## Phase 5 -- building transactions (slates)

The exchange (`slate.rs`, done): **send** -- the sender picks inputs,
change and fee and writes slate S1; **receive** -- the receiver adds one
output paying exactly the amount to a fresh key of theirs and writes S2;
**finalize** -- the sender checks S2 is exactly S1 plus that output
(`Slate::check_response`), signs every input, and submits. Only the
sender signs, once, at the end (signatures cover the whole transaction;
keys are one-time). Slates are armored text files: a readable summary
checked against the hex-encoded slate.

- [x] `Slate`: `send`, `receive`, `check_response`, `transaction`,
      `finalize`; strict binary and armored encodings; file I/O. Tests
      cover every tampering a receiver could try.
- [x] Wallet bookkeeping around it (`Wallet::send` / `receive` /
      `finalize` / `cancel`): on `send`, lock the inputs and record
      the slate and the change output (expected); on `receive`, record the
      new output (expected) and the slate; on `finalize`, persist the
      signed transaction *before* submitting, and if finalize runs again,
      reuse it (never sign a second transaction for the same slate or
      inputs); a way to cancel a slate that was never finalized (unlocks
      its inputs -- safe, since nothing was signed).

- [x] **Coin selection** (largest first): enough confirmed, mature, unlocked outputs to
      cover amount + fee; at most 10 inputs (chunk shape); prefer fewer
      inputs (each costs ~4.2 KB and ~13 s of the miner's proving).
- [x] **Change**: the remainder to a fresh wallet key, recorded as
      expected. (A zero change output is skipped.)
- [ ] **Fee**: explicit in the transaction's plaintext as
      `sum(inputs) - sum(outputs)`; the miner claims it in the reward.
      Policy: a minimum per transaction plus per input (inputs dominate
      both size and proving cost). See open questions.
- [x] **Signing**: derive each input's key, sign, persist the signed
      transaction, mark inputs *spending* -- then submit.
- [x] **Serialization**: `Transaction::to_bytes` / `from_bytes` (strict,
      canonical order), `id()` (hash of the encoding), `fee()`.

## Phase 6 -- mempool (minimal version done: `mempool.rs`)

`finalize` submits to this node's own mempool; its miner includes
waiting transactions in the next template (reward = `REWARD` + fees).
Transactions the wallet signed but that haven't confirmed are
resubmitted at startup.


- [x] **Admission** (each a test; minimum fee not yet):
  - well-formed, `verify()` passes (all signatures);
  - at most 10 inputs / 256 outputs (fits a chunk);
  - every input's commitment is unspent in the active chain;
  - no input already spent by another mempool transaction (first seen
    wins; no replacement, which WOTS makes unsafe anyway);
  - no output commitment already exists (chain or mempool);
  - fee ≥ the node's minimum;
  - total mempool size within its limit.
- [x] **Block applied**: drop transactions it confirmed, and any that
      now conflict (inputs spent by the block).
- [ ] **Reorg**: transactions from unwound blocks go back in (the
      wallet resubmits its own at startup; others' aren't kept) (if still
      valid against the new chain); the new chain's transactions come
      out.
- [ ] **Limits**: total bytes cap; evict lowest fee-per-input first;
      expire after N hours unconfirmed.
- [ ] Indexes: by txid, by input commitment (conflicts), by output
      commitment.

## Phase 7 -- propagation (done: `txrelay.rs`, wire version 4)

- [x] Wire messages (version 4): `TX_INV` (ids and sizes) announces,
      `GET_TX` (cookie-protected) requests, `TX_CHUNK`s carry the data --
      one request covers a whole transaction (at most 64 KB).
- [x] Announce new mempool transactions to peers; request ones we don't
      have; a download must hash to its announced id; only what our
      mempool accepted is relayed further.
- [x] Dedup (ids seen in the last 10 minutes aren't fetched again);
      cookie-protected replies; at most 32 downloads in flight.
- [ ] Per-peer rate limits, and dropping peers that send invalid
      transactions -- a transaction costs ~4 KB to receive and ~1 ms to
      verify, so it's a DoS surface.
- [x] Sync on connect: each newly verified peer is asked once for its
      transactions (`GET_TX_INV`).

## Phase 8 -- mining from the mempool

- [ ] **Template**: pick transactions by fee per input, within the 2 MB
      block cap, then the reward transaction claiming `REWARD + fees`.
- [ ] The prover then picks direct or tree as today
      (`prove_block_auto`): blocks with more than 10 inputs take the tree
      path, so a busy mempool makes proving much slower (minutes on a
      laptop). The template should be **frozen while proving**; new
      transactions wait for the next block.
- [ ] Rebuild the template when the tip moves, when the mempool changes
      substantially, or after a timeout -- without re-proving more often
      than proving takes.
- [ ] Incremental proving (later): prove chunks of mempool transactions
      ahead of time, so a block's proof is mostly done when it's mined.

## Phase 9 -- receiving payments

Solved by slates: the receiver creates their own output during
`receive`, so they know its exact commitment and amount and just watch
blocks for it (phase 2). No invoices, no scanning for unknown amounts.

- [ ] Confirmation tracking and display for received outputs.
- [ ] Later: slates over Tor (or another onion network), so neither
      party needs an open port. (Encrypted notes were decided against:
      open questions.)

## Phase 10 -- tests

- [ ] Unit tests per phase (keychain determinism and index discipline;
      wallet status transitions including reorgs; coin selection; tx
      serialization round trips and strict decoding; every mempool
      admission rule; template selection).
- [x] Two-node integration (real proofs; run live through the CLI,
      both directions, including relay from a non-mining node): A mines to its
      wallet, issues nothing; B issues an invoice; A pays it; the
      payment is relayed, mined, and B's balance shows it after
      confirmation; the spent output can't be spent again; a reorg
      unconfirms and re-confirms it.
- [x] **Real proofs, end to end** (`e2e::mine_then_spend_with_real_proofs`,
      release, ~10 minutes): a chain checking every proof; 10 blocks of
      rewards into a wallet, then 10 blocks of self-transfers from the
      mempool -- a split into 12 outputs, then 12 inputs in one block
      (**tree-proven**, accepted through consensus), then ordinary
      transfers. Every fee returns to the miner, and the wallet ends with
      exactly the 20 rewards.
- [ ] The same over the network (a tree-proven block accepted by
      peers).

## Open questions

- **Client-side proving.** Today every relaying node sees plaintext
  transactions. With our chunk design a wallet could instead prove its
  own transaction (a chunk proof whose net `b` is the fee) and relay
  only commitments + proof; the miner just wraps and aggregates. Costs:
  a chunk proof is ~130 s and ~4 GB at the current fixed chunk shape (a
  smaller per-transaction shape would need its own wrap key), and ~138
  KB per transaction vs ~4-8 KB plaintext. Big privacy win; decide when
  to do it.
- **Payment detection without invoices** (decided against, 2026-10-07).
  An encrypted note on each output (its amount and key index, encrypted
  to the recipient with ML-KEM) would let payers pay any address and
  recipients scan -- but it makes outputs ~830–1,150 bytes instead of 48
  (about 10× fewer transactions per block, ~5× the storage per unspent
  output), adds a lattice assumption, and still needs a fresh one-time
  WOTS key from the recipient. Payments stay interactive (slates); later,
  slates are exchanged over Tor or another onion network, so neither
  party needs an open port. Wallet software only, no consensus change.
- **Wallet recovery from the seed alone** (done: `docs/RECOVERY.md`).
  Every output carries a 16-byte recovery nonce, readable with the
  wallet's view key, so a scan of the chain finds every output with its
  exact amount.
- **Coinbase maturity** (decided, 2026-10-08): wallet-only, not
  consensus.
- **Fee policy**: per transaction + per input? Fees are public in
  plaintext transactions but hidden on chain (only the block total).
- **Seed encryption** and a password prompt.
- **Mnemonic**: BIP39 wordlist (2048 English words) vs our own encoding.
- **Stuck transactions.** A transaction that never confirms (fee too
  low, say) can't be replaced: spending its inputs any other way means
  signing those keys a second time (WOTS). The only way out is getting
  the original mined -- the wallet rebroadcasts it, and fee policy must
  make sure a transaction accepted once stays minable (e.g. mempools
  don't raise the minimum fee on already-relayed transactions, or
  expiry is long). Needs a deliberate answer before phase 6.
- **Slate transport** beyond files (direct node-to-node, or a relay) --
  later.
