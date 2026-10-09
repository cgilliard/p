#!/bin/sh

set -e

# Two programs, not one: the compiler takes at most 65,536 call sites in a
# program (its call-site table), and the node with every test is past that.
# The chain's and network's tests build without the wallet's sources; the
# wallet's tests build with everything.
WALLET="src/sha.fam src/bip39.fam src/rng.fam src/wallet.fam src/slate.fam src/txrelay.fam src/wapi.fam src/full_node.fam"
CORE=$(for f in `cat scripts/files.txt`; do case " $WALLET " in *" $f "*) ;; *) printf '%s ' "$f" ;; esac; done)
TESTS=$(for f in `cat scripts/tests.txt`; do [ "$f" = tests/wallet.fam ] || printf '%s ' "$f"; done)

disk() { rm -f ./tmp/test_disk.img && truncate -s 4G ./tmp/test_disk.img; }   # sparse: room for the state pages and their journal (src/pager.fam)
disk
./tools/fam --test --net --hostfwd=udp::47653-:47653 --disk=./tmp/test_disk.img --append=../data/akjv.txt.gz $CORE $TESTS
disk
./tools/fam --test --net --disk=./tmp/test_disk.img --append=../data/akjv.txt.gz `cat scripts/files.txt` tests/wallet.fam
