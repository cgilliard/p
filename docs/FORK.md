# Fork handling: status

Progress on item #2 of `BLOCK_TODO.md` ("No fork handling"): side
branches, fork-choice by cumulative work, reorgs, and orphans. As of
this writing the work is uncommitted on top of `eda0bd6 add pmmr
truncate`; it builds cleanly and all 224 tests pass.

## Done

### Chain work (`pow.rs`)

- `work_for_target(target)` -- Bitcoin's `2^256 / (target + 1)`, computed
  exactly in fixed-width 256-bit arithmetic (`add256`, plus a schoolbook
  `divmod256`), wrapping on overflow the same way Bitcoin's
  `arith_uint256` does.
- Tested against hand-traced values (8 leading zero bits → 256, 16 →
  65536, half-range target → 2) and the two boundary targets (`0` and
  all-`0xff`).

### Undo data and unwinding (`chain.rs`)

- New LMDB databases, all keyed by header hash: `blocks` (full block
  bytes), `block_undo` (`UndoData`), `block_work` (cumulative work).
  `storage::MAX_DBS` raised from 8 to 16.
- `apply_block` split into `apply_block_in_txn`, so several blocks (plus
  unwinds) can share one atomic transaction.
- `UndoData` snapshots, at apply time, the previous tip header, previous
  `current_target` / `window_start_timestamp`, and each spent input's
  `(commitment, position)` -- none of which is recoverable afterwards.
- `unwind_tip` reverses one block: restores spent outputs (bitmap +
  utxo, at their original positions), removes the block's own outputs,
  truncates the PMMR, and restores tip/retargeting state.
- Tests: unwind restores the exact prior state (roots, tip, height,
  target), unwinding to empty, reversing a spend, and restoring
  difficulty across a retarget-window boundary. `bitmap.rs` and
  `utxo.rs` gained tests for the "undo == never having done it"
  property the unwind relies on.

### Fork-choice, reorg, orphans (`chain.rs`)

- `accept_block(block) -> AcceptOutcome`, one of `Applied`,
  `StoredAsSideBranch`, `Reorged { unwound, applied }`, `Orphaned`.
- Side-branch blocks are validated and stored (`store_side_branch_block`)
  in their own transaction, without touching live state.
- Reorg only on *strictly* more cumulative work. Unwind + replay run in a
  single write transaction; any replay failure aborts it, leaving the
  active chain untouched. This is safe because `Pmmr`, `Bitmap`, and
  `UtxoIndex` hold no in-memory state -- everything lives in LMDB.
- `find_fork_point` searches back at most `max_reorg_depth` blocks;
  beyond that, `Error::ReorgTooDeep`. `Chain::open` now takes
  `max_reorg_depth` (`main.rs`: 1000; tests: 5).
- In-memory orphan pool keyed by missing parent hash;
  `try_connect_orphans(hash)` retries waiting orphans transitively.
- Invalid-block tracking: a new `invalid_blocks` table. A reorg replay
  that fails on a block-level fault (`Error::is_block_fault`: bad
  validate, lineage, unresolved/duplicate input or output, root
  mismatch -- *not* storage errors or a future timestamp) records the
  failing block and everything after it in that branch. Blocks that
  are, or extend, a recorded block are refused with
  `Error::KnownInvalidBlock`, and a candidate branch containing one is
  rejected before anything is unwound.
- Duplicate detection: a block already stored, or already waiting in
  the orphan pool, returns `AcceptOutcome::AlreadyKnown` and is
  otherwise ignored.
- Tests: reorg aborted by a bad block after good blocks were already
  replayed (active chain unchanged, follow-up block refused without a
  retry); mid-chain fork whose winning branch spends a shared output
  differently (final roots match a node that only saw the winning
  branch); duplicate applied / side-branch / orphan blocks.

## Gaps / loose ends

1. **Side-branch blocks are validated against the active chain's
   target**, not a branch-specific recomputed one. Documented as a
   deliberate simplification; imprecise for forks straddling a
   retarget-window boundary.
2. **Orphan pool is unbounded** -- no size cap or expiry (memory DoS).
3. **`accept_block` doesn't call `try_connect_orphans` itself**; the
   caller must remember to.
4. **`max_reorg_depth` also bounds the candidate branch's length** past
   the fork point, so a long new branch is refused even if the unwind
   itself would be shallow.
5. **No pruning** of `blocks` / `block_undo` / `block_work` beyond
   `max_reorg_depth`.
6. **A block that fails to apply directly onto the tip isn't recorded
   as invalid** (it was never stored, so nothing can extend it; a
   resend just fails again the same way). Only reorg-replay failures
   are recorded.
