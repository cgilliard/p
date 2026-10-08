#!/bin/sh

set -e

# 64 MiB: the device benches stride 0x40 sectors apart over 1000 requests, so they
# span ~31 MiB (see "bench sector geometry" in src/disk.fam).  Sized with headroom;
# shrink this and bfits skips the device benches rather than letting them benchmark
# out-of-range requests that fail fast and look like a speedup.
#
# conv=fdatasync matters as much as the size.  Without it dd leaves all 64 MiB
# dirty in the host page cache, and NEITHER writeback trigger fires before the
# run: dirty_expire_centisecs is 30s and the whole suite finishes in a fraction
# of that, while dirty_background_ratio needs ~10% of RAM, which 64 MiB never
# approaches.  The benches then contend with that backlog on top of their own
# writes, and the bill lands on whichever one happens to flush first — which
# showed up as batch1k/pipe1k and durable1k moving in opposite directions run to
# run.  fdatasync (rather than a bare sync) flushes only this file, so the script
# never blocks on unrelated dirty data.
dd if=/dev/zero of=./tmp/bench_disk.img bs=1M count=64 conv=fdatasync 2>/dev/null
./tools/fam --bench --net --hostfwd=udp::47653-:47653 `cat scripts/files.txt` --disk=./tmp/bench_disk.img
