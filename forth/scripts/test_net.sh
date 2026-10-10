#!/bin/sh
# The node against a real Rust node: one serving the main fixture chain (block
# 1, then the 2b/3b branch -- `cargo test --release -- --ignored
# forth_peer_data`) on host UDP port 47701, reached from the test VM through
# QEMU's gateway (10.0.2.2).  The Forth node syncs from it block by block,
# reorganizes onto its branch, and fast-syncs from it (tests/net_sync.fam).
# A few minutes; the Rust node's log is tmp/peer.log.
set -e
SRC="src/fence.fam src/text.fam src/disk.fam src/poseidon2.fam src/wots.fam src/ext.fam src/transcript.fam src/merkle.fam src/fri.fam src/stark.fam src/circuit.fam src/block.fam src/chain.fam src/pow.fam src/diff.fam src/header.fam src/log.fam src/store.fam src/pager.fam src/btree.fam src/state.fam src/blocks.fam src/accept.fam src/snap.fam src/net.fam src/peer.fam"
D=tests/fixtures/main
(cd ../rust && cargo build --release -q && cargo test --release -q -- --ignored forth_peer_data >/dev/null)
# Its console's stdin: a pipe held open (an ended stdin would stop it).
rm -f tmp/peer.in && mkfifo tmp/peer.in && exec 3<>tmp/peer.in
../rust/target/release/p --data-dir tmp/peer-main --no-mine --port 47701 --network main --log-stdout --log-level debug <tmp/peer.in >tmp/peer.log 2>&1 &
PEER=$!
trap 'kill $PEER 2>/dev/null; rm -f tmp/peer.in' EXIT
./tools/fxinfo main > $D/info.fam
./tools/fxpack tmp/main.pack $D/block0.bin $D/block1.bin $D/block2.bin $D/chain2.bin $D/block2b.bin $D/block3b.bin $D/chain3b.bin $D/snap1.bin $D/snap2.bin
rm -f tmp/net.img && truncate -s 4G tmp/net.img
./tools/fam --test --net --append=../data/akjv.txt.gz --load=tmp/main.pack@0x87000000 --disk=tmp/net.img $SRC tests/fx.fam $D/info.fam tests/net_sync.fam
