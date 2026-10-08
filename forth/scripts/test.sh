#!/bin/sh

set -e

dd if=/dev/zero of=./tmp/test_disk.img bs=1M count=1 2>/dev/null
./tools/fam --test --net --hostfwd=udp::47653-:47653 --disk=./tmp/test_disk.img `cat scripts/files.txt`
