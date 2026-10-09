#!/bin/sh
# Run the node: tabernacle boots bin/full_node.bin from data/disk.img, and the
# node syncs from its seed, keeping its chain and wallet on the disk between
# runs.
#
#   node.sh [--recover] [--passphrase] [--api-key]
#
#   --recover     restore the wallet from its 24 backup words, typed when the
#                 node asks (on a disk without a wallet: a new data/disk.img)
#   --passphrase  a new wallet's passphrase, or the restored one's, typed when
#                 the node asks
#   --api-key     show the wallet's API key (tools/wallet asks for it once)
#
# The first run makes a wallet and shows its backup words once.  Words and
# passphrases go straight to the node over the console, never in settings or
# the environment; what you type isn't shown.
#
#   SEED   host:port to start from (127.0.0.1: this machine; default
#          127.0.0.1:7701, a Rust node's default port)
#   DEPTH  fast sync: start this many blocks behind the seed on a new chain
#          (default 25: a few minutes of replay under QEMU; 0 syncs every block)
#   PORT   our UDP port, forwarded from this machine (default 47653)
#   API    the wallet API's UDP port, forwarded from 127.0.0.1 only (default
#          PORT + 1); tools/wallet talks to it
#   NET    main or dev (default dev, for now); a disk holds one network's
#          chain, so switching means a new disk image
#
# After scripts/build.sh, it rewrites the boot image (scripts/makenode.sh) so
# tabernacle boots the new build.  To start over: rm data/disk.img -- which
# deletes the wallet too (restore it with --recover).
set -e
SEED=${SEED:-127.0.0.1:7701}
DEPTH=${DEPTH:-25}
PORT=${PORT:-47653}
NET=${NET:-dev}
API=${API:-$((PORT + 1))}
WALLET=""
for arg in "$@"; do
	case "$arg" in
		--recover) WALLET="$WALLET recover" ;;
		--passphrase) WALLET="$WALLET passphrase" ;;
		--api-key) WALLET="$WALLET apikey" ;;
		*) echo "usage: $0 [--recover] [--passphrase] [--api-key]" >&2; exit 1 ;;
	esac
done
./scripts/makenode.sh
# The console: the settings, then the keyboard (for the wallet), through a
# fifo so the node runs in the foreground (Ctrl-C stops it).  What's typed
# isn't echoed (words, passphrases); the terminal is put back however the
# node ends.
mkdir -p tmp
FIFO=tmp/console.$$
rm -f "$FIFO" && mkfifo "$FIFO"
CAT=""
STTY=""
cleanup() {
	[ -n "$CAT" ] && kill "$CAT" 2>/dev/null
	[ -n "$STTY" ] && stty "$STTY"
	rm -f "$FIFO"
}
trap cleanup EXIT
trap 'exit 130' INT TERM
if [ -t 0 ]; then
	STTY=$(stty -g)
	stty -echo
fi
# Two lines first: tabernacle's (its port, debug, timeout, and the hosts it
# would fetch the node from if the disk's copy were bad), then the node's own
# (src/full_node.fam).
exec 3<&0
{
	printf '3737 0 10000 159.54.172.190:3737 146.235.230.124:3737\004seed=%s depth=%s port=%s api=%s net=%s%s\004' \
		"$SEED" "$DEPTH" "$PORT" "$API" "$NET" "$WALLET"
	exec cat <&3
} > "$FIFO" &
CAT=$!
./tools/q32 bin/tabernacle \
	--disk=./data/disk.img \
	--net \
	--hostfwd=udp::$PORT-:$PORT,hostfwd=udp:127.0.0.1:$API-:$API < "$FIFO"
