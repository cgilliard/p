# Transactions: TODO

Status: **in progress** (2026-10-05). Decided: Grin-style **slates**,
exchanged as **files** to start (`send` / `receive` / `finalize`).
Built: `keychain.rs`, `slate.rs`, transaction encoding.

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

## Phase 0 -- node architecture

Today `main` owns the `Chain` and alternates mining batches with
handling received blocks. The CLI, the wallet and the mempool all need
the chain too, so make that explicit:

- [ ] One **node thread** owns `Chain`, `Mempool` and `Wallet` and runs
      an event loop over: network events (blocks, transactions), CLI
      requests, and mining work. Everything else talks to it through
      channels (request + reply), so there's no shared mutable state.
- [ ] Mining stays interleaved (batches of nonces between events), but
      becomes something the loop does when enabled, not the loop itself
      -- so mining can be switched on and off at runtime.
- [ ] Proving (2 s for a small block, minutes for a tree) shouldn't
      freeze the CLI: run it on a worker thread and hand the proof back
      as an event; a block that's gone stale by then is dropped.
- [ ] Clean shutdown (`quit`, Ctrl+C): stop mining, flush the wallet,
      close storage.

## Phase 1 -- keychain (`keychain.rs`: done, except mnemonic)

- [x] `Keychain::random()` (production), `from_seed` / `from_seed_hex`
      (restore), `Keychain::test(label)` (reproducible, per-test keys);
      `derive(KeyId { account, index })`, `public_key`, `secret_key`,
      `output(id, amount)`. The seed is never printed (`Debug`) and is
      zeroed on drop.
- [ ] **Seed**: 32 random bytes (from the OS), created on first run.
      Shown as a mnemonic for backup -- BIP39 English (24 words, with a
      checksum), so it's familiar and typo-resistant. Import from a
      mnemonic to restore.
- [x] **Derivation**: `key_seed = hash_bytes_32("tabernacle-keychain-v1" ‖
      seed ‖ account ‖ index)`, then `wots::keygen(key_seed)`. Keys are
      never stored, only the seed and the next unused index; any key can
      be re-derived.
- [ ] **Index discipline**: an index is handed out exactly once (for an
      address, a change output, or a mining reward), and the next index
      is persisted *before* the key is used, so a crash can't hand the
      same key out twice.
- [ ] **Seed at rest**: start with the seed in the wallet store,
      readable only by the user (file permissions); password-encrypted
      seed later (open question).

## Phase 2 -- wallet store

- [ ] Its own LMDB database(s) in the data directory (or `--wallet-dir`),
      separate from consensus state.
- [ ] **Outputs** the wallet owns: commitment, amount, key index, and a
      status -- *expected* (we know it should appear: a reward we're
      mining, an invoice we've issued), *confirmed* (in the active chain,
      at height h), *spending* (in a transaction we've signed),
      *spent* (that transaction confirmed).
- [ ] **Signed transactions** we've released, by the outputs they spend
      (the one-time-key rule: this is what we rebroadcast, never
      re-sign).
- [ ] **Follow the chain**: on every applied block, mark expected
      outputs whose commitments appear as confirmed and spending outputs
      whose commitments appear as inputs as spent; on every unwound block
      (reorg), undo exactly that. Driven by events from `Chain`, which
      needs a small hook for "applied block / unwound block".
- [ ] **Balance**: confirmed (with a confirmation count), pending
      (expected or unconfirmed), and locked (spending).

## Phase 3 -- mining to the wallet

- [ ] The reward output pays to a fresh wallet key; the wallet records
      it as *expected* (commitment and amount are both known) before the
      block is mined.
- [ ] Once blocks carry other transactions, the reward claims
      `REWARD + fees`, all to that key.
- [ ] When our block is orphaned or loses a reorg, its reward output
      goes back to expected/unconfirmed (phase 2's unwinding).
- [ ] **Coinbase maturity** (open question): Bitcoin forbids spending a
      reward for 100 blocks, so a reorg can't erase coins that were
      already spent onward. At minimum the wallet should not *spend* an
      immature reward; whether consensus should enforce it is a separate
      decision.

## Phase 4 -- CLI

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

- [ ] Line-oriented reader on stdin, commands as requests to the node
      thread (phase 0), replies printed.
- [ ] Amounts in whole coins with 9 decimals (1 coin = 10^9 units, the
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
- [ ] Wallet bookkeeping around it: on `send`, lock the inputs and record
      the slate and the change output (expected); on `receive`, record the
      new output (expected) and the slate; on `finalize`, persist the
      signed transaction *before* submitting, and if finalize runs again,
      reuse it (never sign a second transaction for the same slate or
      inputs); a way to cancel a slate that was never finalized (unlocks
      its inputs -- safe, since nothing was signed).

- [ ] **Coin selection**: enough confirmed, mature, unlocked outputs to
      cover amount + fee; at most 10 inputs (chunk shape); prefer fewer
      inputs (each costs ~4.2 KB and ~13 s of the miner's proving).
- [ ] **Change**: the remainder to a fresh wallet key, recorded as
      expected. (A zero change output is skipped.)
- [ ] **Fee**: explicit in the transaction's plaintext as
      `sum(inputs) - sum(outputs)`; the miner claims it in the reward.
      Policy: a minimum per transaction plus per input (inputs dominate
      both size and proving cost). See open questions.
- [ ] **Signing**: derive each input's key, sign, persist the signed
      transaction, mark inputs *spending* -- then submit.
- [x] **Serialization**: `Transaction::to_bytes` / `from_bytes` (strict,
      canonical order), `id()` (hash of the encoding), `fee()`.

## Phase 6 -- mempool

- [ ] **Admission** (each a test):
  - well-formed, `verify()` passes (all signatures);
  - at most 10 inputs / 256 outputs (fits a chunk);
  - every input's commitment is unspent in the active chain;
  - no input already spent by another mempool transaction (first seen
    wins; no replacement, which WOTS makes unsafe anyway);
  - no output commitment already exists (chain or mempool);
  - fee ≥ the node's minimum;
  - total mempool size within its limit.
- [ ] **Block applied**: drop transactions it confirmed, and any that
      now conflict (inputs spent by the block).
- [ ] **Reorg**: transactions from unwound blocks go back in (if still
      valid against the new chain); the new chain's transactions come
      out.
- [ ] **Limits**: total bytes cap; evict lowest fee-per-input first;
      expire after N hours unconfirmed.
- [ ] Indexes: by txid, by input commitment (conflicts), by output
      commitment.

## Phase 7 -- propagation

- [ ] Wire messages (version bump): `TX_INV(txids)` announces, `GET_TX
      (txid)` requests, and the transaction itself travels with the same
      chunking and reassembly as blocks (`transfer`).
- [ ] Announce new mempool transactions to peers; request ones we don't
      have; verify fully before relaying further (never relay what we
      wouldn't accept).
- [ ] Dedup (recently seen txids), per-peer rate limits, and dropping
      peers that send invalid transactions -- a transaction costs ~4 KB
      to receive and ~1 ms to verify, so it's a DoS surface.
- [ ] Sync on connect: exchange mempool txids so a new node's mempool
      fills.

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
- [ ] Later: paying someone *without* an interactive exchange would need
      encrypted notes (open questions).

## Phase 10 -- tests

- [ ] Unit tests per phase (keychain determinism and index discipline;
      wallet status transitions including reorgs; coin selection; tx
      serialization round trips and strict decoding; every mempool
      admission rule; template selection).
- [ ] Two-node integration (real proofs, release build): A mines to its
      wallet, issues nothing; B issues an invoice; A pays it; the
      payment is relayed, mined, and B's balance shows it after
      confirmation; the spent output can't be spent again; a reorg
      unconfirms and re-confirms it.
- [ ] A block of more than 10 inputs from the mempool, tree-proven,
      accepted by peers -- the full consensus path for tree proofs
      (`docs/BLOCK_TODO.md` notes it's only tested in isolation today).

## Open questions

- **Client-side proving.** Today every relaying node sees plaintext
  transactions. With our chunk design a wallet could instead prove its
  own transaction (a chunk proof whose net `b` is the fee) and relay
  only commitments + proof; the miner just wraps and aggregates. Costs:
  a chunk proof is ~130 s and ~4 GB at the current fixed chunk shape (a
  smaller per-transaction shape would need its own wrap key), and ~138
  KB per transaction vs ~4-8 KB plaintext. Big privacy win; decide when
  to do it.
- **Payment detection without invoices.** An encrypted note attached to
  each output (amount, encrypted to the recipient) would let payers pay
  any address and recipients scan. Post-quantum encryption (e.g.
  ML-KEM) adds ~1 KB per output and a key per address; and consensus
  would need to carry the notes (block space).
- **Wallet recovery from the seed alone.** Scanning needs amounts, so a
  seed alone can find only outputs whose amounts can be guessed (exact
  rewards). Options: back up the wallet store too; encrypted notes
  (above) would also solve this; or a deterministic amount rule for
  rewards (pay `REWARD` and fees to separate keys, so at least rewards
  are recoverable).
- **Coinbase maturity**: wallet-only, or a consensus rule?
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
