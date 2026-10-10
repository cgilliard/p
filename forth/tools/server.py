#!/usr/bin/env python3
"""Boot image server -- serves a node build to tabernacle, the way a node
does (src/image.fam), for running on a seed without a node.

Usage: server.py [binary_path] [port] [--net main|dev]
  Default binary: bin/full_node.bin
  Default port:   3737
  Default net:    dev

The file is re-read (and re-hashed) whenever its mtime changes, so you can
overwrite it in place without restarting the server.  It's served only to
tabernacles built for it: their ask names the image's hash (Gimli, as
tabernacle computes it).

Protocol (the node's, src/peer.fam): magic "TBRN" ("TBRD" on dev), version
12, type, body; numbers big-endian.
  GET_HOSTS (1)   nonce u64, max u16, zero padding
  HOSTS (2)       nonce u64, cookie u64, count u16 (0: no hosts shared)
  GET_BIN (15)    cookie u64, hash (32), first u32, count u16
  BIN_CHUNK (16)  hash (32), index u32, up to 1024 bytes
The cookie (from HOSTS) proves the asker's address; at most 32 chunks an ask.
"""
import hashlib
import hmac
import os
import socket
import struct
import sys
import time

CHUNK = 1024
WINDOW = 32
VERSION = 12
BINARY = 'bin/full_node.bin'
PORT = 3737
NET = 'dev'
VERBOSE = os.environ.get('VERBOSE', '') != ''

args = sys.argv[1:]
if '--net' in args:
    i = args.index('--net')
    NET = args[i + 1]
    del args[i:i + 2]
if NET not in ('main', 'dev'):
    sys.exit("server.py: --net is main or dev")
if len(args) > 0:
    BINARY = args[0]
if len(args) > 1:
    PORT = int(args[1])
MAGIC = b'TBRD' if NET == 'dev' else b'TBRN'
KEY = os.urandom(32)  # for cookies


def gimli(s):
    """The Gimli permutation on 12 little-endian u32 words, in place."""
    M = 0xFFFFFFFF
    for r in range(24, 0, -1):
        for c in range(4):
            x = ((s[c] << 24) | (s[c] >> 8)) & M
            y = ((s[c + 4] << 9) | (s[c + 4] >> 23)) & M
            z = s[c + 8]
            s[c + 8] = (x ^ (z << 1) ^ ((y & z) << 2)) & M
            s[c + 4] = (y ^ x ^ ((x | z) << 1)) & M
            s[c] = (z ^ y ^ ((x & y) << 3)) & M
        if r % 4 == 0:
            s[0], s[1], s[2], s[3] = s[1], s[0], s[3], s[2]
            s[0] ^= 0x9E377900 | r
        elif r % 4 == 2:
            s[0], s[1], s[2], s[3] = s[2], s[3], s[0], s[1]


def gimli_hash(data):
    """Tabernacle's hash (src/tabernacle.S, gimli_hash)."""
    s = [0] * 12
    n = len(data) // 16 * 16
    for i in range(0, n, 16):
        for j, w in enumerate(struct.unpack('<4I', data[i:i + 16])):
            s[j] ^= w
        gimli(s)
    b = bytearray(struct.pack('<12I', *s))
    for j, x in enumerate(data[n:]):
        b[j] ^= x
    b[len(data) - n] ^= 0x01
    b[15] ^= 0x80
    b[47] ^= 0x01
    s = list(struct.unpack('<12I', b))
    gimli(s)
    out = struct.pack('<4I', *s[:4])
    gimli(s)
    return out + struct.pack('<4I', *s[:4])


state = {'mtime': None, 'data': b'', 'hash': b''}


def reload_if_changed():
    try:
        mtime = os.path.getmtime(BINARY)
    except OSError as e:
        print(f"Warning: cannot stat {BINARY}: {e}")
        return
    if mtime == state['mtime']:
        return
    with open(BINARY, 'rb') as f:
        data = f.read()
    state.update(mtime=mtime, data=data, hash=gimli_hash(data))
    print(f"Loaded {BINARY}: {len(data)} bytes, {(len(data) + CHUNK - 1) // CHUNK} chunks, "
          f"hash {state['hash'].hex()}")


def cookie(addr):
    msg = socket.inet_aton(addr[0]) + struct.pack('>H', addr[1])
    return hmac.new(KEY, msg, hashlib.sha256).digest()[:8]


reload_if_changed()

sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
sock.bind(('0.0.0.0', PORT))
print(f"Listening on UDP :{PORT} ({NET})...")

while True:
    pkt, addr = sock.recvfrom(65535)
    if len(pkt) < 6 or pkt[:4] != MAGIC or pkt[4] != VERSION:
        continue
    kind, body = pkt[5], pkt[6:]
    now = time.monotonic()
    if kind == 1 and len(body) >= 10 and not any(body[10:]):  # GET_HOSTS
        sock.sendto(MAGIC + bytes([VERSION, 2]) + body[:8] + cookie(addr) + b'\0\0', addr)
        print(f"[{now:.3f}] GET_HOSTS from {addr}")
    elif kind == 15 and len(body) == 46:  # GET_BIN
        reload_if_changed()
        data, h = state['data'], state['hash']
        if body[:8] != cookie(addr) or body[8:40] != h:
            print(f"[{now:.3f}] GET_BIN from {addr}: wrong cookie or another build; ignored")
            continue
        first, count = struct.unpack('>IH', body[40:46])
        n = (len(data) + CHUNK - 1) // CHUNK
        end = min(first + min(count, WINDOW), n)
        for c in range(first, end):
            sock.sendto(MAGIC + bytes([VERSION, 16]) + h + struct.pack('>I', c)
                        + data[c * CHUNK:(c + 1) * CHUNK], addr)
            if VERBOSE:
                print(f"  sent chunk {c}")
        print(f"[{now:.3f}] GET_BIN {first}..{end - 1} from {addr}")
