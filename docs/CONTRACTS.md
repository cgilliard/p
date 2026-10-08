# Contracts: spending policies and payment channels

Design for contracts on this chain, aimed first at payment channels with
more than two parties and a Lightning-like network of them. Status:
**design, nothing implemented** (2026-10-07).

## Goals

- **Multi-party payment channels from the start**, eltoo-style (LN-Symmetry):
  no penalty transactions, no "toxic" old states, constant storage per
  channel, channel factories. Up to **12 parties** (see "The 12-signature
  limit").
- **Routed payments** across channels (hash-locked, as in Lightning).
- A **general but small** set of spending conditions (approach A, below),
  not a channel-only special case, so escrow, vaults and similar contracts
  come with it.
- **No cost to ordinary transactions** beyond a few percent of proving, and
  no change to what validators download or verify.

## Background: why eltoo

Lightning as deployed (LN-penalty, Poon–Dryja) revokes each old state by
handing over a secret; publishing a revoked state forfeits the channel.
Every node and watchtower must keep revocation data for every past state,
restoring an old backup can lose the channel, each side holds different
transactions, and channels between more than two parties are
impractical.

eltoo (LN-Symmetry) replaces revocation with **replacement**: each update
transaction can spend the funding output or *any earlier update*, and
settlement waits a fixed delay after the last update, so a later state
always wins. Both sides hold the same transactions, only the latest state
matters, and it extends naturally to n parties. Its cost is that
publishing an old state is no longer punished; it's just replaced
(the cheater loses only fees).

On Bitcoin, eltoo needs a rebindable signature (`SIGHASH_ANYPREVOUT`, BIP
118), which has never activated; it exists only as a prototype. We have no
such constraint.

Not available to us: **PTLCs** (point time-locked contracts) rely on
Schnorr/ECDSA adaptor signatures, which have no mature post-quantum
equivalent. Routed payments use hash locks (HTLCs), as Lightning does
today. The miner sees transactions in the clear anyway (it proves them), so
the hop linkability HTLCs add matters less here than on Bitcoin.

## Spending policies (approach A)

### Locks

An output's commitment today is `H(DOMAIN_COMMITMENT, pubkey_hash ‖
amount)`. It becomes `H(DOMAIN_COMMITMENT, lock ‖ amount)`, where `lock`
is either:

- **a key hash**, exactly as today (`DOMAIN_PUBKEY`): a plain output,
  spent by one signature. Plain transactions are unchanged, at zero cost.
- **a policy root**: the root of a small Merkle tree of **branches**
  (`DOMAIN_POLICY_NODE` nodes over `DOMAIN_POLICY_LEAF` leaves), like
  Taproot's script tree. A spend reveals one branch and its path, and
  satisfies it. Unused branches stay hidden.

Domains keep the two kinds of lock distinct. On chain both are opaque
commitments, so contract outputs look like any others.

### Branches

A branch is a conjunction of conditions, encoded as field elements and
hashed into its leaf:

| Condition | Meaning | Circuit cost |
|---|---|---|
| `signers(k, keys)` | `k` signatures from distinct keys among `keys` (`k ≤ n ≤ 12`; threshold or all) | 278 blocks per signature (+16–20 for multi-use keys) |
| `after_height(h)` | Spending block's height `≥ h` | a comparison in spare rows |
| `after_age(n)` | Spending height `≥` the spent output's creation height `+ n` | a comparison in spare rows |
| `hashlock(x)` | A preimage `p` with `H(DOMAIN_HASHLOCK, p) = x` | 1 block |
| `rebind(tag, state)` | Signatures use **rebind mode** (below); the spending transaction's declared state is `> state` | a comparison in spare rows |

Branch path: +1 block per tree level (2–4 for typical policies).

### Signature modes

- **ALL** (today's): the signature covers every input `(lock, amount)` and
  every output of the transaction.
- **REBIND**: the signature covers the branch's `tag`, a **state number**
  declared by the transaction, and the outputs it names, **not** the input
  being spent and not other inputs or outputs. It can therefore spend
  *any* output whose revealed branch has the same tag and a lower state,
  and anyone may add other inputs and outputs, for example to attach a fee.
  This is the ANYPREVOUT-style rebinding eltoo needs.

Inputs here are already identified by `(lock, amount)` rather than by a
pointer to a previous transaction, so ALL-mode signatures already rebind to
any output with the same lock and amount. REBIND extends that to outputs
whose locks differ by state.

### Keys

- **One-time WOTS keys** (today's), for plain outputs and one-shot branches.
- **Multi-use keys** (XMSS-style): a Merkle tree of `2^h` WOTS keys whose
  root is the key hash, good for `2^h` signatures; a signature adds the leaf
  index and `h` path hashes. Channel keys sign every update, so they need
  these. With `h = 20`, about a million updates per channel; +20 blocks per
  signature (≈ 7%) and +640 bytes per signature.

Multi-use keys are **stateful**: signing twice with the same leaf leaks
the key. Wallets must never reuse a leaf, including after restoring a
backup; for example, reserve leaf ranges per device or backup epoch.
That's the main operational hazard of this design (eltoo's counterpart to
Lightning's toxic old states). Stateless hash-based signatures
(SPHINCS+-style) avoid it but cost thousands of hashes per signature in
the circuit, which is impractical here.

Signatures never go on chain (only the miner sees them), so their size
costs only bandwidth to the miner.

## Channels

An n-party channel (2 ≤ n ≤ 12), eltoo-style:

- **Funding output** `F`, with policy:
  - *update*: `signers(n, update_keys) ∧ rebind(0)`
  - *cooperative close*: `signers(n, close_keys)` (ALL mode)
- **Update transaction** `U_k` (state `k`): spends `F` or any `U_j` with
  `j < k`; one output with the same amount and policy:
  - *update*: `signers(n, update_keys) ∧ rebind(k)`
  - *settle*: `signers(n, settle_keys_k) ∧ after_age(delay) ∧ rebind(k − 1)`
- **Settlement transaction** `S_k`: spends `U_k` after `delay` blocks; pays
  each party's balance and each in-flight HTLC. Signed in REBIND mode
  (declaring state `k`, naming its outputs), so its fee is attached at
  publication like an update's; its keys are this state's alone, so it
  can only spend `U_k`.

To update, the parties sign `U_k` and `S_k` (both REBIND) together; only
the latest pair needs keeping. To close unilaterally, a party publishes
the latest `U_k`; anyone holding a later state publishes it within `delay`
blocks, and it replaces `U_k` on chain. A watchtower needs only the latest
pair per channel.

**HTLC outputs** in `S_k`:
- *claim*: `signers(1, payee) ∧ hashlock(x)`
- *refund*: `signers(1, payer) ∧ after_height(expiry)`

**Channel factories**: a funding output whose settlement pays into further
channel funding outputs. With REBIND, sub-channels can update without
touching the factory's state.

**Fees**: every channel transaction is REBIND-signed, so whoever publishes
it attaches a fee input and change output then (re-pointing an update at
the output it spends first, `Transaction::rebind`). Channel amounts don't
need to predict fees, and nothing needs a fee-paying child: the mempool
never accepts a transaction spending an unconfirmed output.

**An old update in the mempool** stays (first seen wins); once it
confirms, the latest update is published re-pointed at its output, well
within `delay`. Letting a later update replace an earlier one in the
mempool would save that block, but isn't needed.

## Costs

Measured against today's chunk circuit (`block_air`): a chunk is 4,096
blocks of 32 rows (2^17 rows, 231 columns). Spending an input costs about
**278 blocks** (224 WOTS chain steps, 33 for the key hash, 16 for the
Bible-passage path, and 5 more). An output costs about 2. A full chunk (8
inputs, 20 outputs) uses roughly 56%.

| | Effect |
|---|---|
| Published block proof size | **None.** The root proof's shape is fixed (2^19 rows on main, ~162 KB); contract logic lives in chunk proofs, which are never published. |
| Verification time | **None** (~10 ms on main): validators check only the root and chain proofs. |
| Proving ordinary transactions | About **+4%**, from new block kinds and a few columns (231 → about 240). |
| Proving contract spends | About one input's worth (278 blocks) per signature, plus a few blocks for paths and locks. |
| Wrap circuit | Verifies a slightly wider chunk proof; main has room, dev's wrap (94% of 2^17) needs checking. |
| Validators | Unchanged. |

### The 12-signature limit

A transaction must fit in one chunk. At 12 signatures with multi-use keys,
`12 × (278 + 20) ≈ 3,576` blocks, plus outputs and message blocks, is
about 89% of a chunk. So:

- **Limit: 12 signatures per transaction**, across all its inputs
  (alongside today's 8 inputs and 20 outputs per transaction). A
  standardness rule -- miners (`prover::plan_chunks`), mempools and
  wallets enforce it; validators see only proofs. Consensus bounds it by
  the chunk itself (a transaction must fit in one).
- A channel therefore has at most 12 parties, and any single transaction
  at most 12 signers.
- **The 20-output limit binds settlements:** with n parties, at most
  `20 − n` HTLCs can be in flight in one channel (8 with 12 parties; see
  "Decisions").

## State tree: creation height in every leaf

Relative timelocks (`after_age`) need each output's **creation height**,
proven from the state.

- **Width:** 32 bits. Heights are below 2^31 in the circuits (1,007 years
  of blocks is about 2^26). The delay itself is part of the policy, so it
  costs nothing per leaf.
- **In every leaf**, in the leaf hash's capacity: `compress(DOMAIN_STATE_LEAF
  ‖ height, commitment, nonce)`. Tree nodes already put their level there.
  **No extra permutations**, for spends and appends alike.
- **Privacy:** uniform leaves keep contract outputs indistinguishable from
  plain ones; a height only on contract leaves would mark them.
- **Circuits:** the wrap stamps appended leaves with the block height and
  opens spent leaves with theirs; the block height becomes one more public
  value up the tree, checked by the chain step against the header. Each
  input's creation height travels from the wrap to the chunk statement,
  for `after_age`.
- **Storage and sync:** nodes already record each output's origin height
  (`UtxoIndex::set_origin`). Snapshot leaf entries grow by 4 bytes (50 →
  54; the download goes from about 53 to 57 bytes per unspent output). Storage version and wire version bump; a
  new genesis.

## Step 2 encoding (policy outputs, ALL mode)

**Branch leaf** = a sponge (`DOMAIN_POLICY_LEAF`) over 16-element blocks:

- Block 0 (header): `[k, n, after_height, after_age, has_hash, rebind,
  state, 0, x₀ … x₇]`, where `x` is the hash lock (zeros if `has_hash = 0`)
  and `rebind`, `state` are reserved for step 4 (zero until then).
- Then the `n` key hashes, two per block (a lone last key's other half
  zero).

Rules: `1 ≤ k ≤ n ≤ 12` (every branch needs a signer: without one, the
miner, who sees the spend, could redirect it); `after_height` and
`after_age` are below 2^31, `0` meaning no lock.

**Policy root** = a Merkle tree over the branch leaves
(`DOMAIN_POLICY_NODE + level` nodes), depth ≤ 8 (up to 256 branches).
A one-branch policy's root is its leaf. A plain output's lock stays its
key hash (`DOMAIN_PUBKEY`), so the domains keep the two kinds apart.

**Hash lock**: `H(DOMAIN_HASHLOCK, p) = x` for a preimage `p` of 8 elements.

**In the chunk circuit (`block_air`)**, a policy input is:

- one **signature section** per signer, as today's input section (digits,
  Bible-passage binding, chains, key hash), but sending its key hash on the
  bus as `(input, key index, key hash)` instead of feeding a commitment;
- a **policy section**: the leaf sponge, whose key blocks receive each
  half's `(input, index, key hash)` when that key signed (a flag per half;
  the flags sum to `k`, and since each index is received at most once,
  the signers are distinct); a hash-lock block when `has_hash`; and the
  path to the root, which becomes the input commitment's lock;
- the timelocks, checked in the header block's spare rows: `height −
  after_height` and `height − created − after_age` each as two 16-bit
  limbs, range-checked (columns the commitment blocks already have).

The message is sent to every signature section (not once per input), and
signatures per chunk are capped at 12 (`CHUNK_SHAPE`), along with today's
8 inputs and 20 outputs.

**Public statement**: the block's height joins the amounts tuple, and each
input's creation height its input tuple. The wrap takes each input's
height from the statement (not a free witness) and checks it against the
spent leaf, so a timelock can't be satisfied with a false creation height.

## Step 3 design (multi-use keys)

A channel's update keys sign every update, so they can't be one-time
WOTS keys. A **multi-use key** is a Merkle tree of `2^h` WOTS keys: its
key hash (what an output's lock or a branch lists) is the tree's root,
and a signature is a WOTS signature by one leaf key, plus the leaf's index
and path.

- **One kind of key.** A one-time key is the `h = 0` case: its hash is its
  root. So every signature section in the chunk circuit gets an optional
  path: after the key-hash sponge (`PK`), `h` key-node blocks (`KNODE`,
  `DOMAIN_KEY_NODE + level`, like `PNODE`) climb to the root, which is
  what the input's lock or the branch's key receives. Plain outputs can
  use multi-use keys too, at the same cost.
- **Cost:** `h` blocks per signature (+7% at `h = 20`), and `32·h` more
  bytes per signature (only the miner sees them).
- **Key generation is the real cost.** Each leaf is a full WOTS key
  (about 480 permutations), so a tree of `2^h` leaves takes `2^h` key
  generations: about 45 s for `h = 16` (65,536 updates) and about 12
  minutes for `h = 20`, per party per channel. **Default `h = 16`; at most
  `h = 20`** (decided 2026-10-07): a standardness rule (miners,
  mempools, wallets), like the 12-key and 12-signature limits --
  validators see only proofs. The circuit needs no cap of its own -- each level hashes
  under its own domain, and the chunk bounds `h` anyway: twelve
  signatures at `278 + h` blocks plus a worst-case transaction's other
  ~200 blocks fit up to `h ≈ 46`, so 20 uses about 89%. (A tree of trees
  would make generation lazy, but each layer adds a whole WOTS signature,
  about 278 blocks; not worth it at these sizes.)
- **Statefulness:** a leaf must never sign twice. Wallet-only (see
  "Decisions").

## Step 4 design (REBIND signatures)

What eltoo needs: a signature for update `k` that can spend the funding
output **or any earlier update's output**, each of which carries a
different state number in its policy.

- **The branch:** `rebind = 1` and `state = s` in the header (reserved since
  step 2). Its signatures must be REBIND signatures, and the spending
  input declares a state `k > s`.
- **The message:** `H(DOMAIN_REBIND, k, the outputs it names)`, each named
  output's commitment and nonce. Not the input, nor any other input or
  output, so it spends any output whose branch has the same keys and a
  lower state, and anyone can add an input and change output to pay the
  fee. No channel tag is needed: update keys are fresh per channel, so
  their signatures can only spend that channel's outputs.
- **Amounts:** every update output carries the channel's full amount; the
  input's amount isn't signed, but all candidate outputs hold the same
  amount, so nothing can be skimmed.
- **In the chunk circuit:** a REBIND input's signers receive the REBIND
  message instead of the transaction's. It's computed by its own sponge
  in the branch's section, after the input commitment (`RHDR`: `[m, k]`,
  range-checked; then `m` `RITEM` blocks, each receiving a named output
  from its `COUT` over the bus -- an output sends once per REBIND
  message naming it). Each signature section carries its mode (`RB`) and
  branch section (`GROUP`); a REBIND signer takes `(TAG_RMSG, section)`
  instead of `(TAG_MSG, transaction)`, and the key it sends its branch
  carries the mode, so a REBIND signature satisfies only a REBIND branch
  and an ordinary one only an ordinary branch. The header checks `k > s`
  in the lane freed by dropping its creation-height range check (the wrap
  ties the creation height to the spent leaf, whose block proved its
  height below 2^30). Cost: `1 + m` blocks per REBIND input (`m` is 1 for
  an update).
- **Fees, and order:** REBIND signatures don't finalize a transaction, so
  the publisher can add a fee input and change. But an ordinary signature
  covers what each input spends, so the publisher re-points the update
  at the earlier one it will spend (`Transaction::rebind`) first, then
  adds and signs the fee.
- **Native:** a policy spend gains the declared state; `verify` checks
  REBIND signatures against the REBIND message.
- **Settlement** transactions use ALL signatures, so each spends exactly
  the update output it was made for.

## Implementation order

1. **Creation height in leaves** (state tree, wrap, chain step, snapshot,
   storage). Consensus-only; no new features yet. *Done (2026-10-07):*
   `state_tree::leaf(commitment, nonce, height)`, the height in the
   capacity; leaf records and snapshot entries carry it (storage version
   3, wire version 11); the wrap stamps appended leaves with the block's
   height, carried up the tree in `product`'s octet (`[product, height,
   0, 0, 0]`) and checked by the chain step against the header, and opens
   spent leaves with their own (a witness the leaf binds). A fast sync
   now records each output's true creation height. The geneses are
   unchanged (an empty tree's root doesn't depend on leaves).
2. **Policy outputs**, ALL mode: locks, branch encoding, `signers`,
   `after_height`, `after_age`, `hashlock`; the 12-signature limit. Wallet
   support for building and spending policy outputs. *Done (2026-10-07),
   but for the wallet:* `policy` (branches, trees, hash locks, native
   checks); an output's `lock` (a key hash or a policy root); a
   transaction's inputs are a key spend or a policy spend (branch, path,
   preimage, signers), ordered by commitment (encoding version 4;
   `add_policy_input`, `sign_policy_input`, `locks_hold`,
   `signature_count`). In `block_air`, the `PHDR`/`PKEY`/`HLOCK`/`PNODE`
   blocks as specified above (240 columns, was 231); signatures per chunk
   and per transaction capped at 12 (`prover::CHUNK_SIGNATURES`, the
   mempool). `Chain::build_block` publishes the block's and its inputs'
   creation heights (`block_air::Heights`) and refuses a spend whose
   timelocks don't hold yet (`Error::LockNotMet`); so does the mempool, for
   the next block. The wrap reads each input's creation height from the
   chunk's statement. Tested: honest spends of every branch kind satisfy
   every constraint; too few signers, a wrong key, a wrong preimage, and
   early or too-young spends are each refused by the circuit, laid out as
   a forger would. Dev's wrap: 124,117 rows (95% of 2^17). Wallet support
   (holding and building policy outputs) comes with the channel protocol
   (step 6).
3. **Multi-use keys** (XMSS-style): circuit path check, wallet key
   management with leaf-reuse protection. See "Step 3 design". *Done
   (2026-10-07), but for the wallet:* `keytree` (trees, proofs, `h ≤ 20`);
   a key spend or policy signer carries its key's place (`KeyProof`;
   encoding version 5); in `block_air`, `KNODE` blocks climb from the
   signing key's hash to the root, which feeds the input commitment or
   the branch (241 columns). Tested: a tree-locked output spent by a leaf,
   and a branch mixing a tree key and a one-time key; a leaf key with
   another leaf's path refused.
4. **REBIND mode and `rebind` branches**: the state comparison, signatures
   naming outputs, fee inputs. See "Step 4
   design". *Done (2026-10-07):* `Branch::rebind`, a policy
   spend's declared state and named outputs, `rebind_message`,
   `Transaction::rebind`, per-input messages (encoding version 6); in
   `block_air`, `RHDR`/`RITEM` blocks and the `RB`/`GROUP`/`NAMED` columns
   (245 columns). Tested: an update spends an earlier one with a fee added
   afterwards, and the same signatures spend another earlier update when
   re-pointed; an update at the same or a later state, signatures over
   the transaction's message instead, or a named output changed, each
   refused. Dev's wrap: 124,872 rows (95% of 2^17).
5. **Mempool**: *not needed* (2026-10-07). Every channel transaction is
   REBIND-signed, with its fee attached at publication, so no packages;
   an old update is answered after it confirms, so no replacement (see
   "Channels"). The mempool's part -- timelocks and the signature cap --
   came with step 2.
6. **Commands for trying the primitives** (done, 2026-10-07): a thin layer
   in the node's wallet and command line (`contract`, `Wallet::
   new_contract_key`/`sign_contract`/`lock_funds`/`attach_fee`), with no
   channel logic -- see "Trying it out".
7. **Channel protocol and routing** (n-party updates and closes, the
   watchtower format, HTLC forwarding): *deferred*; not part of this node
   for now.

## Trying it out

Policies are text files, one branch per line; transactions pass between
signers as files, like slates. Alice and Bob fund a 2-of-2 and spend it:

```text
alice> key                       # a one-time key: prints its id, A
bob>   key                       # B
# p.txt:  branch threshold=2 keys=A,B
alice> lock 5 p.txt              # funds the output, submitted
alice> spend p.txt 0 5 out=s.tx  # pays 5 - fee back to Alice's wallet
alice> sign s.tx
bob>   sign s.tx
alice> submit s.tx
```

An eltoo-style update, with key trees (`key 16`, about 45 s, blocks the
node meanwhile; `key 4` for a quick test) and REBIND:

```text
# u3.txt: branch threshold=2 keys=TA,TB rebind=3   (likewise u4.txt, u5.txt)
alice> spend u3.txt 0 5 to=u5.txt fee=0 state=5 out=u.tx
alice> sign u.tx
bob>   sign u.tx
alice> rebind u.tx u4.txt 0 5    # spend the update at state 4 instead
alice> fee u.tx 0.001            # the fee, from Alice's wallet, last
alice> submit u.tx
```

Hash locks: `hashlock` prints a preimage and its image; the image goes in
a branch (`hashlock=`), the preimage in its spend (`preimage=`).
Timelocks (`after_height=`, `after_age=`) are checked when a block is
built: a spend submitted too early is refused until they hold.

## Decisions (2026-10-07)

- **HTLCs per channel:** at most `20 − n` in flight (8 with 12 parties):
  that many payments in progress through a channel at once. An HTLC lasts
  only until its payment completes, so this caps concurrency, not volume.
- **Threshold signers** (`k` of `n`, `k < n`): included at launch.
- **Hash locks:** Poseidon2 only; no SHA-256 (no swaps with Bitcoin's hash
  locks).
- **Multi-use key reuse:** prevented in the wallet; no consensus impact.
- **Delays and expiries** are per-channel choices, written into each
  channel's policies, not consensus constants. Defaults, on ten-minute
  blocks:

  | | Default | Why |
  |---|---|---|
  | Settlement delay (`after_age` on updates) | 72 blocks (12 h) | Time for a party or its watchtower to replace an old published state; eltoo watchtowers store one state per channel, so a shorter window than Lightning's penalty window is safe. |
  | Per-hop expiry margin | 108 blocks (18 h) | The settlement delay plus 36 blocks to confirm the update and settlement under fee pressure. In eltoo, enforcing an HTLC on chain waits out the settlement delay first, so each hop's margin must exceed it. |
  | Final-hop minimum expiry | 36 blocks (6 h) | Time to claim on chain. |
  | Maximum total expiry | 2,016 blocks (2 weeks) | Caps how long a stuck payment can lock funds (about 18 hops). |

  A failed 5-hop payment can lock funds for up to about 4 days; a normal
  one settles in seconds.
