#!/bin/sh
# Write the node (bin/full_node.bin, from scripts/build.sh) to the start of the
# disk image tabernacle boots from (data/disk.img).  The image is sparse, 4 GiB:
# the node keeps its chain and state 32 MiB in (src/store.fam's dbbase), and
# rewriting the boot image leaves them alone -- a new build keeps its chain.
set -e
IMG=./data/disk.img
N=$(wc -c < bin/full_node.bin | tr -d ' \t')
[ "$N" -lt 33554432 ] || { echo "bin/full_node.bin is over 32 MiB: it would overrun the chain"; exit 1; }
[ -e "$IMG" ] || truncate -s 4G "$IMG"
[ $(wc -c < "$IMG" | tr -d ' \t') -ge 4294967296 ] || truncate -s 4G "$IMG"
dd if=bin/full_node.bin of="$IMG" conv=notrunc 2>/dev/null
echo "$IMG: $N bytes written"
