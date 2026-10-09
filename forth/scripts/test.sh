#!/bin/sh

set -e

rm -f ./tmp/test_disk.img && truncate -s 4G ./tmp/test_disk.img   # sparse: room for the state pages and their journal (src/pager.fam)
./tools/fam --test --net --hostfwd=udp::47653-:47653 --disk=./tmp/test_disk.img --append=../data/akjv.txt.gz `cat scripts/files.txt` `cat scripts/tests.txt`
