# Executive Summary

As of 2026-10-08.

A proof-of-work chain that is post-quantum end to end, verifies every block with one small proof, and syncs new nodes from the unspent set instead of the history. It carries roughly twice Bitcoin's transactions per second at 2 MiB blocks, hides amounts and transaction boundaries on chain, and supports multi-party payment channels without new consensus rules.

## At a glance

Bitcoin figures are approximate, for the same transaction shape (2.5 inputs, 2.5 outputs).

| | This chain | Bitcoin |
| --- | --- | --- |
| Block time | 10 minutes, ASERT retargeting every block | 10 minutes, retarget every 2,016 blocks |
| Block limit | 2 MiB, proofs included | 4M weight units (about 1.6–1.9 MB of raw data typical) |
| Throughput | about 14.8 tx/s (about 8,900 tx per block) | about 6.5 tx/s |
| Signatures | hash-based (Winternitz one-time), never published | ECDSA / Schnorr, published |
| Quantum resistance | yes: hash-based signatures and STARK proofs | no: elliptic-curve keys are breakable |
| Checking a block | one proof, about 10 ms, whatever the block holds | every signature, about 0.6–0.9 s of CPU per equivalent block |
| Joining the network | one chain proof plus the unspent set | the full history, about 768 GB |
| Amounts on chain | hidden | public |
| Contract spends | look like any payment | script or Taproot path visible |
| Supply | 735,840 coins, issued over 1,007 years | 21 million coins |

## Quantum resistance

Nothing in the chain rests on elliptic curves or factoring: every primitive is a hash. A quantum computer gains only Grover's square-root speedup, which leaves about 64 bits of work against the proofs: centuries of runtime per attack, not a practical threat.

- **Signatures.** Winternitz one-time signatures (64 chains, base 8, target-sum encoding) over the Poseidon2 hash. Reusable keys are Merkle trees of one-time keys, 2^16 by default and up to 2^20.
- **Proofs.** STARKs, which rely only on hashing. Main-network proofs target 128-bit conjectured security (26 queries, blowup 16, 24 grinding bits).
- **Hashing.** Poseidon2 over the BabyBear field everywhere: outputs, state tree, transcripts, Merkle commitments.
- **Signature size doesn't matter.** Signatures are checked inside the block proof and never reach the chain, so post-quantum signatures cost no block space. Bitcoin adopting post-quantum signatures of several kilobytes each would cut its throughput by roughly 10–50×.

## Throughput and proving

A full 2 MiB block holds about 8,900 transactions, about 14.8 per second: roughly 2.3× Bitcoin for the same transaction shape. Blocks are small per transaction because they carry only commitments; the miner's proof stands in for everything else.

| Per block | Bytes |
| --- | --- |
| Each transaction (2.5 inputs × 32 + 2.5 outputs × 48) | about 200 |
| Block proof (main) | about 162 KB |
| Parent's chain proof (main) | about 161 KB |
| Header and counts | about 210 |

The miner pays for this in proving. On a 12-thread laptop CPU, a block of one chunk (0–about 3 transactions) takes about 5 minutes to prove plus about 2.5 minutes for its chain proof, inside the 10-minute block time. Full blocks need parallel or GPU proving, which the design keeps possible.

## Verification and fast sync

Checking a block costs the same whatever it contains: one block proof and one chain proof, about 10 ms each on a laptop. The chain proof is recursive, so one proof attests that the whole chain up to the parent is valid, proof of work and retargeting included.

- **Joining the network.** A new node verifies one chain proof and downloads the unspent set (54 bytes per output), not the history. At Bitcoin's unspent-set size that is an order of magnitude or more less data than Bitcoin's full download (about 768 GB); 20× is a conservative figure. Bitcoin's assumeUTXO snapshots are similar in size but trust a hash shipped in the software; here the snapshot is proven.
- **Disk.** Nodes keep the unspent set and recent blocks. Reclaiming space means resyncing; only archives keep full history, and nothing depends on them.
- **Small validators.** Checking proofs needs no proof-of-work dataset and no unspent set, so a proof-only validator fits on very small hardware. A second, non-mining node written in Forth for bootstrappable RV32I systems is being built for this.
- **Full nodes.** A node that also maintains the unspent set spends roughly as much per full block as Bitcoin does (estimated, not yet measured): it updates a Poseidon2 state tree instead of checking signatures.

## Privacy

The goal is solid everyday privacy, not Monero's: the public chain reveals little, and stronger privacy lives on layer 2.

| Who | What they see |
| --- | --- |
| The public | Commitments only: no amounts, keys, addresses, signatures or contract terms. Each block is one sorted list of inputs and one of outputs, so transactions are not separated (in effect a CoinJoin of the whole block). Visible: which earlier outputs a block spends, and the block's total reward and fees. |
| The miner | Each transaction in full, since it proves them. A user who submits to one miner or pool privately is known only to that miner. |
| Whoever paid you | Your output's commitment, so when it is spent. |
| A channel partner | Payments inside the channel; the chain sees only opens and closes, which look like ordinary payments. |

At scale, a block of thousands of transactions leaves little to work with. Early on, blocks with few transactions mix less. Hiding how a block's transactions are grouped is best-effort rather than proven: the published tree proofs are made without zero-knowledge blinding, a deliberate trade to stay within the 10-minute proving budget.

## Contracts and layer 2

Outputs can be locked by spending policies, enough to build multi-party payment channels in the style of eltoo without further consensus changes.

- **Policies.** A tree of up to 256 branches (depth 8). Each branch can require a threshold of up to 12 keys, an absolute or relative timelock, and a Poseidon2 hash lock.
- **REBIND.** A signature can cover a channel state and its outputs without naming the input it spends, so any later state replaces any earlier one. There are no penalty transactions and no toxic old states.
- **Channels.** Channels can have up to 12 parties, though updates need every party's signature. Channel factories split one shared output into two-party channels, so routine payments need only two signers.
- **Watchtowers.** A tower only needs to hold the latest state, and can be paid a small fixed output in each state.
- **Cost.** Contract logic is proven, not published: a 12-of-12 channel close takes the same 200 bytes as a simple payment.

The channel protocol and routing are not built yet; the node has command-line tools to exercise the primitives.

## Monetary policy and consensus

The supply is fixed at 735,840 coins in two equal halves: 7 years of 1 coin per block, then 1,000 years of 0.007 coin per block, after which the chain ends.

| Era | Blocks | Reward per block | Coins issued |
| --- | --- | --- | --- |
| Years 1–7 | 367,920 | 1 coin | 367,920 |
| Years 8–1,007 | 52,560,000 | 0.007 coin | 367,920 |

- **Security budget.** The long, small reward keeps paying miners for 1,000 years, so security never rests on fees alone.
- **Block time.** 10 minutes, retargeted every block by ASERT (Bitcoin Cash's aserti3-2d) with a two-day half-life.
- **Proof of work.** Memory-bound, over a 64 MiB dataset derived from the King James Bible text. Validators check it without the dataset.
- **Text binding.** Every signature also binds a block of that text, chosen by the signer's randomness.
- **Header.** A version field, plus an auxiliary hash miners can use (zero for now).
- **Consensus limits.** A transaction must fit in one proof chunk: 8 inputs, 20 outputs. The 12-signature cap is a standardness rule, not consensus.

## Status

Consensus is implemented and tested on a main and a dev network. The Forth validator already verifies real block proofs.

| Area | State |
| --- | --- |
| Rust mining node | Consensus complete: block and chain proofs, ASERT, supply schedule, header version, policies, key trees, REBIND; 455 tests pass |
| Wallet | Basic wallet plus command-line tools for contracts; no channel protocol yet |
| Forth validator | Poseidon2, WOTS, transcript, FRI and STARK verification match the Rust node; verifies a real dev block's proof |
| Next for the validator | Body hash and structural checks, proof of work, the chain proof, header rules |
| Open | An independent review of the block circuit's new constraints before launch |
