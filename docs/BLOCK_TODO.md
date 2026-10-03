# Block/chain TODO

Gaps identified after `chain.rs`/`block.rs`/`prover.rs` (stub) were wired
together and verified end-to-end (`e2e.rs`: a miner mining two blocks,
paying another user, the recipient spending onward, a double-spend
correctly rejected). The pipeline itself works. These are the things
still missing before it's a real chain, roughly ordered by how much they
matter — the first is worth settling on paper *before* the real ZK
circuit gets built, since the circuit's job is enforcing exactly that
rule, and building it against an unspecified rule means redoing it.

## 1. No economic enforcement (unbounded minting) -- this *is* the proof

**Status:** not started. This is the real proof's core job, not a
separate task alongside it.

Nothing anywhere checks that total output value is bounded by block
reward. Concretely, *today*, a block can contain any number of
zero-input "reward" transactions, minting any amount to any pubkey, and
nothing rejects it. This can't be fixed with ordinary plaintext
plumbing *at all* -- the chain only ever sees opaque commitments, never
the amounts behind them, so there is nothing for plaintext code to sum.
Checking this is exactly, and only, what the ZK proof is for.

This also subsumes fees as a separate concept (an earlier version of
this doc tracked "no fee mechanism" on its own). There's no need for a
dedicated fee field or convention: if the circuit checks the balance
equation across the *whole block* --

```
sum(all inputs in the block) + block_reward == sum(all outputs in the block)
```

-- then a transaction whose inputs exceed its outputs simply leaves
slack in that equation, which the miner's own reward output can be
sized to absorb. That slack *is* the fee; it falls out of the one
equation for free, with no separate mechanism.

What the circuit needs pinned down:

- A fixed (or schedule-based, see #3) block reward amount.
- A rule for how many reward-claiming transactions a block may contain
  (exactly one?).
- The one balance equation above.

What's still ordinary (non-proof) plumbing, once the circuit exists:
the miner needs to compute `sum(their plaintext inputs) -
sum(their plaintext outputs) + base_reward` themselves, in plaintext
(they have full visibility into their own candidate transactions), to
know how big to make their own reward output *before* asking the
circuit to confirm they got it right. Trivial arithmetic over data
they already have -- not a design question, just a small helper
somewhere in the build pipeline once there's a real circuit to feed.

## 2. No fork handling

**Status:** not started.

`Chain::apply_block` only accepts a block whose `prev_hash` matches the
*current* tip (see `chain.rs`'s `WrongParent` check) — there's no notion
of a competing block, an orphan waiting on a missing parent, or
switching to a heavier chain. Fine for a single-miner prototype; a real
multi-miner network needs this. Needs:

- Storing blocks that don't extend the current tip instead of just
  rejecting them.
- A fork-choice rule (heaviest/longest chain) -- needs #3 (height or
  cumulative work) to compare candidates.
- Reorg: unwinding `pmmr`/`bitmap`/`utxo` back to a common ancestor and
  reapplying the new best chain.

## 3. No block height or timestamp

**Status:** done, with one piece deliberately deferred.

- **Height** is deliberately *not* a header field -- it's just "how
  many blocks came before this one," fully recoverable without
  spending any of the header's own space on it. `Chain` tracks it as a
  side field instead: `Chain::height(&self, txn) -> Result<Option<u64>>`
  (`None` for an empty chain, `Some(0)` after the first block, and so
  on), backed by a `next_height` counter in `chain_meta` that advances
  by one in the same write transaction every successful `apply_block`
  commits (see `chain.rs`).
- **Timestamp** *is* a header field now: `BlockHeader::timestamp: u64`
  (Unix seconds), stamped with the current time in
  `UnprovenBlock::finish` and included in `pow_preimage` (so it can't
  be altered post-mining without redoing the proof of work, same as
  every other committed field). `HEADER_LEN` grew from 160 to 168
  bytes accordingly.
- **Deferred:** no validation of `timestamp` exists yet -- no
  monotonicity check against the previous block, no bound on how far
  into the future it can claim to be. Not yet needed with one miner;
  common once multiple miners exist. Revisit alongside #2 (fork
  handling), since a sensible bound (e.g. median-time-past) usually
  wants a short run of recent headers to compare against, which only
  matters once there's more than one chain to compare.

This also settles #1's dependency on a schedule-based reward (height
is now available to key a reward-halving schedule off of, whenever #1
gets built) and #2's need for a cheap tip-height comparison (now
available via `Chain::height`, though the harder part of #2 --
choosing between two competing chains, not just reading one's height
-- is still unstarted).

## 4. No wallet / payment-detection story

**Status:** not started.

`e2e.rs`'s test works because the sender is handed the recipient's
pubkey directly, in-process. A real recipient has no way to notice "a
payment landed for me": outputs are opaque `H(H(pubkey) || amount)`
commitments, so nothing short of being told the exact commitment (or
trial-checking candidates against known pubkeys/amounts) reveals it.
The "recipient hands the sender a fresh pubkey out of band" flow was
discussed conceptually (see the Grin-comparison discussion) but neither
side of that handoff has any code. Needs:

- A wallet type that holds keys (plausibly HD-derived, to get a fresh
  pubkey per expected payment without manual bookkeeping).
- Some mechanism (even an out-of-band one, like Grin's) for a sender to
  learn the recipient's next pubkey.
- A way for a wallet to notice which `pmmr`/`utxo` entries are actually
  its own, once it knows which (pubkey, amount) pairs it's expecting.

## 5. No real driver

**Status:** not started. Expected at this stage, not urgent.

`main.rs` still just prints "Hello world!". No CLI, no mempool, no
persistent/interruptible mining loop (today's `block::mine_block` just
takes a bounded attempt count for tests), no networking. This is the
difference between "a tested library" and "a thing you can run."

## 6. No pruning

**Status:** not started. Low urgency.

The PMMR is "prunable" by name only -- nothing ever removes spent-output
data, so storage grows forever. `bitmap` already tracks spent status
per position, which is the piece pruning would need; the actual removal
logic (and deciding what "removal" even means under LMDB, which doesn't
shrink files automatically) doesn't exist yet.
