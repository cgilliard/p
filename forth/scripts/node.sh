#!/bin/sh
# Run the node: tabernacle boots bin/full_node.bin from data/disk.img, and the
# node syncs from its seed, keeping its chain on the disk between runs.
#
#   SEED   host:port to start from (127.0.0.1: this machine; default
#          127.0.0.1:7701, a Rust node's default port)
#   DEPTH  fast sync: start this many blocks behind the seed on a new chain
#          (default 25: a few minutes of replay under QEMU; 0 syncs every block)
#   PORT   our UDP port, forwarded from this machine (default 47653)
#   NET    main or dev (default dev, for now); a disk holds one network's
#          chain, so switching means a new disk image
#
# After scripts/build.sh, it rewrites the boot image (scripts/makenode.sh) so
# tabernacle boots the new build.  To start the chain over: rm data/disk.img.
set -e
SEED=${SEED:-127.0.0.1:7701}
DEPTH=${DEPTH:-25}
PORT=${PORT:-47653}
NET=${NET:-dev}
./scripts/makenode.sh
# Two lines on the serial input: tabernacle's (its port, debug, timeout, and
# the hosts it would fetch the node from if the disk's copy were bad), then
# the node's own (src/full_node.fam).
printf '3737 0 10000 159.54.172.190:3737 146.235.230.124:3737\004seed=%s depth=%s port=%s net=%s\004' "$SEED" "$DEPTH" "$PORT" "$NET" | \
	./tools/q32 bin/tabernacle \
	--disk=./data/disk.img \
	--net \
	--hostfwd=udp::$PORT-:$PORT
