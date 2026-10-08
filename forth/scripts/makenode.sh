#!/bin/sh
set -e
IMG=./data/disk.img
dd if=/dev/zero of="$IMG" bs=1M count=64 2>/dev/null
dd if=bin/full_node.bin of="$IMG" conv=notrunc 2>/dev/null
echo "$IMG: $(wc -c < bin/full_node.bin | tr -d ' \t') bytes written"
