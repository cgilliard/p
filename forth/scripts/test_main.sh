#!/bin/sh
# The main-network tests: a real chain from the Rust node (tests/fixtures/main,
# made by `cargo test --release -- --ignored forth_fixtures`), loaded into the
# test VM as a pack rather than compiled in. Then the benches.
set -e
SRC="src/fence.fam src/text.fam src/disk.fam src/poseidon2.fam src/wots.fam src/ext.fam src/transcript.fam src/merkle.fam src/fri.fam src/stark.fam src/circuit.fam src/block.fam src/chain.fam src/pow.fam src/diff.fam src/header.fam src/store.fam src/pager.fam src/btree.fam src/state.fam src/blocks.fam src/accept.fam src/snap.fam"
D=tests/fixtures/main
./tools/fxinfo main > $D/info.fam
./tools/fxpack tmp/main.pack $D/block0.bin $D/block1.bin $D/block2.bin $D/chain2.bin $D/block2b.bin $D/block3b.bin $D/chain3b.bin $D/snap1.bin $D/snap2.bin
rm -f tmp/store.img && truncate -s 4G tmp/store.img
RUN="--append=../data/akjv.txt.gz --load=tmp/main.pack@0x87000000 --disk=tmp/store.img"
./tools/fam --test $RUN $SRC tests/fx.fam $D/info.fam tests/main.fam
./tools/fam --bench $RUN $SRC tests/fx.fam $D/info.fam tests/main.fam | grep "bench main_"
