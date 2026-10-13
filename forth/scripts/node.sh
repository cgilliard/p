#!/bin/sh
# Run the node: tabernacle boots bin/full_node.bin from data/disk.img, and the
# node syncs from its seed, keeping its chain and wallet on the disk between
# runs.
#
#   node.sh [--recover] [--passphrase] [--api-key]
#           [--log-dest webui|console|both] [--log-max-entries N]
#           [--debug-disable-verification] [--relay] [--relay-addr IP]
#           [--mix-delay MS]
#           [--direct] [--seed-mode]
#
#   --recover     restore the wallet from its 24 backup words, typed when the
#                 node asks (on a disk without a wallet: a new data/disk.img)
#   --passphrase  a new wallet's passphrase, or the restored one's, typed when
#                 the node asks
#   --api-key     show the wallet's API key (tools/wallet asks for it once) and
#                 exit: read from data/disk.img, so the node may be running
#   --log-dest D  where the node's log goes: webui (the default: the web
#                 wallet's Log tab, kept on the disk), console (here), or both
#   --log-max-entries N
#                 the most log lines kept for the Log tab, the oldest dropped
#                 as new ones come (default 10000; at most 1000000)
#   --relay       serve as a payment relay: keep wallets' records (their
#                 payment addresses' keys, where they're reached), answer
#                 lookups and relay their messages -- for the seed nodes
#                 (src/relay.fam; --gateway, its old name, works too)
#   --relay-addr IP
#                 a relay (as --relay) reached at this public IPv4 address,
#                 on PORT: the node makes its own signed entry for
#                 consensus.txt (good for 30 days, made again with 7 left)
#                 and prints the line on the console, alone, starting
#                 "relay " -- also in the web wallet, and from
#                 `tools/wallet relay-entry` (docs/RELAYS.md)
#   --mix-delay MS
#                 a relay: hold each cell it passes on a random 0 .. MS ms
#                 first (at most 10000), so cells in and out are harder to
#                 match by time (docs/RELAYS.md)
#   --direct      testing: no circuits -- lookups and payments go straight to
#                 the receiver's home relays
#   --seed-mode   testing: the seeds (or relays set) as relays, even when the
#                 chain lists relays
#   --debug-disable-verification
#                 don't check blocks' proofs (everything else is checked), to
#                 time what a big block costs: only with a private network --
#                 SEED a Rust miner run with --debug-disable-verification, on
#                 a disk of its own (its chain is that network's)
#
# The first run makes a wallet and shows its backup words once.  Words and
# passphrases go straight to the node over the console, never in settings or
# the environment; what you type isn't shown.
#
#   SEED   the hosts to start from, space-separated: A.B.C.D:PORT, or by
#          name, NAME:PORT -- looked up by the node when it starts and every
#          hour -- or NAME:PORT/A.B.C.D, falling back on that address if the
#          name gets no answer (default the two public seeds, by name only:
#          a DNS server must answer;
#          127.0.0.1 is this machine -- a Rust node here is 127.0.0.1:3739)
#   DNS    the DNS server the node asks, A.B.C.D (default 10.0.2.3: QEMU's
#          own, which asks this machine's -- whatever /etc/resolv.conf says)
#   DEPTH  fast sync: start this many blocks behind the seed on a new chain
#          (default 25: a few minutes of replay under QEMU; 0 syncs every block)
#   PORT   our UDP port, forwarded from this machine (default 3737)
#   API    the wallet API's UDP port, forwarded from 127.0.0.1 only (default
#          PORT + 1); tools/wallet talks to it
#   NET    main or dev (default dev, for now); a disk holds one network's
#          chain, so switching means a new disk image
#   PEERS  the most hosts the node keeps (default 256)
#   PROBE  how often every known host is asked for hosts, in seconds
#          (default 60); a silent host is kept and asked again (hourly after
#          a day; removed after a week, or after 3 tries if it never answered)
#   PERIP  the most hosts kept with one IP address (default 4)
#   DISK   the disk image (default data/disk.img): another runs a second node
#          (with its own PORT and API), and its own wallet
#   BOOT   the seeds tabernacle starts from when the disk's copy isn't the
#          build it expects: it finds peers through them and fetches the node
#          from the peers holding it, the seeds only if no one else does
#          (default SEED's, as addresses: names looked up here, on this
#          machine -- tabernacle has no DNS of its own)
#
# To boot a new build from the disk without fetching it, run
# scripts/makenode.sh after scripts/build.sh.  To start over: rm
# data/disk.img -- which deletes the wallet too (restore it with --recover).
set -e
DISK=${DISK:-./data/disk.img}
SEED=${SEED:-tabernacle1.root.sx:3737 tabernacle2.root.sx:3737}
DEPTH=${DEPTH:-25}
PORT=${PORT:-3737}
NET=${NET:-dev}
API=${API:-$((PORT + 1))}
# boot_of: SEED as A.B.C.D:PORT, for tabernacle.
boot_of() {
	for s in $SEED; do
		hp=${s%%/*}; host=${hp%:*}; port=${hp##*:}
		case $host in
		*[!0-9.]*)
			ip=$(getent ahostsv4 "$host" 2>/dev/null | awk 'NR == 1 { print $1 }')
			[ -n "$ip" ] || case $s in */*) ip=${s#*/} ;; esac
			[ -n "$ip" ] && printf '%s:%s ' "$ip" "$port" ;;
		*) printf '%s ' "$hp" ;;
		esac
	done
}
BOOT=${BOOT:-$(boot_of | sed "s/ *$//")}
WALLET=""
APIKEY=""
LOGDEST=""
LOGMAX=""
NOVERIFY=""
RELAY=""
MIXDELAY=""
RELAYADDR=""
DIRECT=""
SEEDMODE=""
usage() {
	echo "usage: $0 [--recover] [--passphrase] [--api-key] [--log-dest webui|console|both] [--log-max-entries N] [--debug-disable-verification] [--relay] [--relay-addr IP] [--mix-delay MS] [--direct] [--seed-mode]" >&2
	exit 1
}
while [ $# -gt 0 ]; do
	case "$1" in
		--recover) WALLET="$WALLET recover" ;;
		--passphrase) WALLET="$WALLET passphrase" ;;
		--api-key) APIKEY=1 ;;
		--log-dest=*) LOGDEST=${1#*=} ;;
		--log-dest) [ $# -ge 2 ] || usage; LOGDEST=$2; shift ;;
		--log-max-entries=*) LOGMAX=${1#*=} ;;
		--log-max-entries) [ $# -ge 2 ] || usage; LOGMAX=$2; shift ;;
		--debug-disable-verification) NOVERIFY=1 ;;
		--relay|--gateway) RELAY=1 ;;
		--relay-addr=*) RELAYADDR=${1#*=}; RELAY=1 ;;
		--relay-addr) [ $# -ge 2 ] || usage; RELAYADDR=$2; RELAY=1; shift ;;
		--mix-delay=*) MIXDELAY=${1#*=} ;;
		--mix-delay) [ $# -ge 2 ] || usage; MIXDELAY=$2; shift ;;
		--direct) DIRECT=1 ;;
		--seed-mode) SEEDMODE=1 ;;
		*) usage ;;
	esac
	shift
done
case "$LOGDEST" in
	""|webui|console|both) ;;
	*) echo "node.sh: --log-dest: webui, console or both" >&2; exit 1 ;;
esac
# --relay-addr: A.B.C.D, each part 0 to 255; not 0.x, nor 10.0.2.x (QEMU's
# own network, which the node sees: never the public address).  127.x is
# this machine, for a test network on one host.
if [ -n "$RELAYADDR" ]; then
	ok=$(echo "$RELAYADDR" | awk -F. 'NF == 4 { for (i = 1; i <= 4; i++) if ($i !~ /^[0-9]+$/ || $i > 255) exit; print "y" }')
	case "$RELAYADDR" in 0.*|10.0.2.*) ok="" ;; esac
	[ -n "$ok" ] || { echo "node.sh: --relay-addr: the relay's public IPv4 address, A.B.C.D" >&2; exit 1; }
fi
case "$MIXDELAY" in
	"") ;;
	*[!0-9]*) echo "node.sh: --mix-delay: a number of ms, 0 to 10000" >&2; exit 1 ;;
	*) [ "$MIXDELAY" -le 10000 ] || { echo "node.sh: --mix-delay: at most 10000" >&2; exit 1; } ;;
esac
case "$LOGMAX" in
	"") ;;
	*[!0-9]*|0) echo "node.sh: --log-max-entries: a number, 1 to 1000000" >&2; exit 1 ;;
	*) [ "$LOGMAX" -le 1000000 ] || { echo "node.sh: --log-max-entries: at most 1000000" >&2; exit 1; } ;;
esac
# --api-key: the node (this build, loaded directly -- not booted from the
# disk's image, which may be another build), with the disk read only and no
# network, shows the key and stops (src/full_node.fam, fnkey).  The node itself
# may be running.
if [ -n "$APIKEY" ]; then
	[ -e "$DISK" ] || { echo "node.sh: no $DISK yet (start the node first)" >&2; exit 1; }
	printf 'apikey net=%s\004' "$NET" | ./tools/q32 bin/full_node.bin --disk-ro="$DISK"
	exit 0
fi
mkdir -p data
# Sparse: it takes only what the node writes.  The first 2.5 GiB are its
# boot image, tip log and journal; the rest holds the chain (blocks are kept
# whole).  A disk made smaller grows, with the node stopped: truncate -s 128G
# data/disk.img.
[ -e "$DISK" ] || truncate -s 128G "$DISK"
# QEMU can't forward a port something else holds, and quits without a word.
if command -v ss >/dev/null; then
	if ss -Huln "sport = :$PORT" | grep -q .; then
		echo "node.sh: UDP port $PORT is in use (another node? set PORT)" >&2
		exit 1
	fi
	if ss -Htln "sport = :$API" | grep -q .; then
		echo "node.sh: TCP port $API is in use (the web wallet's: set API)" >&2
		exit 1
	fi
fi
echo "node.sh: the web wallet: http://127.0.0.1:$API/ (once the node is up)" >&2
# The console: two lines of settings first -- tabernacle's (its port, debug,
# timeout, network, and the seeds it would fetch the node from if the disk's
# copy were bad), then the node's own (src/full_node.fam).
settings() {
	printf '%s 0 10000 %s %s\004%sdepth=%s port=%s api=%s net=%s%s%s%s%s%s%s%s%s%s%s%s%s\004' \
		"$PORT" "$([ "$NET" = dev ] && echo 1 || echo 0)" "$BOOT" "$(for s in $SEED; do printf 'seed=%s ' "$s"; done)" "$DEPTH" "$PORT" "$API" "$NET" "$WALLET" \
		"${PEERS:+ peers=$PEERS}" "${PROBE:+ probe=$PROBE}" "${PERIP:+ perip=$PERIP}" \
		"${LOGDEST:+ log=$LOGDEST}" "${LOGMAX:+ logmax=$LOGMAX}" "${NOVERIFY:+ noverify}" "${RELAY:+ relay}${RELAYADDR:+ relayaddr=$RELAYADDR}" "${DNS:+ dns=$DNS}" \
		"${MIXDELAY:+ mixdelay=$MIXDELAY}" "${DIRECT:+ direct}" "${SEEDMODE:+ seedmode}"
}
# QEMU's output goes through a pipe (| cat): QEMU makes its output
# non-blocking, and on a terminal that would be the keyboard's too.
run() {
	./tools/q32 bin/tabernacle \
		--disk="$DISK" \
		--net \
		--hostfwd=udp::$PORT-:$PORT,hostfwd=tcp:127.0.0.1:$API-:$API | cat
}
if [ -z "$WALLET" ]; then
	# Nothing to type: the terminal is left alone (Ctrl-C stops the node).
	settings | run
	exit 0
fi
# --recover / --passphrase: then the keyboard, for the words or passphrase,
# through a fifo so the node runs in the foreground; what's typed isn't
# echoed, and the terminal is put back however the node ends.
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
exec 3<&0
{
	settings
	exec cat <&3
} > "$FIFO" &
CAT=$!
run < "$FIFO"
