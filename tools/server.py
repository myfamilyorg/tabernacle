#!/usr/bin/env python3
"""FAMC chunk server -- serves a binary file over the FAMC UDP protocol.

Usage: server.py [binary_path] [--port PORT]
  Default binary: tmp/node.bin
  Default port:   3737

Protocol:
  REQ_RANGE: "FAMC" + 0x02 + start(BE u16) + end(BE u16)
  RSP_CHUNK: "FAMC" + 0x82 + seq(BE u16) + data (up to 1400 bytes)
"""
import os
import socket
import struct
import sys

CHUNK_SIZE = 1400
PORT = 3737
BINARY = 'tmp/node.bin'
VERBOSE = os.environ.get('VERBOSE', '') == '1'

# Parse args
args = [a for a in sys.argv[1:] if not a.startswith('-')]
flags = [a for a in sys.argv[1:] if a.startswith('-')]
if args:
    BINARY = args[0]
for i, f in enumerate(flags):
    if f == '--port' and i + 1 < len(flags):
        PORT = int(flags[i + 1])

with open(BINARY, 'rb') as f:
    data = f.read()

chunks = [data[i:i+CHUNK_SIZE] for i in range(0, len(data), CHUNK_SIZE)]
if VERBOSE:
    print(f"Loaded {len(data)} bytes, {len(chunks)} chunks of up to {CHUNK_SIZE} bytes",
          file=sys.stderr)

sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
sock.bind(('0.0.0.0', PORT))
if VERBOSE:
    print(f"Listening on UDP {PORT}...", file=sys.stderr)

while True:
    pkt, addr = sock.recvfrom(65535)
    if len(pkt) < 9 or pkt[:4] != b'FAMC':
        continue
    cmd = pkt[4]
    if cmd == 0x02:  # REQ_RANGE
        start, end = struct.unpack('>HH', pkt[5:9])
        if VERBOSE:
            print(f"REQ_RANGE {start}..{end} from {addr}", file=sys.stderr)
        for seq in range(start, min(end + 1, len(chunks))):
            payload = b'FAMC' + bytes([0x82]) + struct.pack('>H', seq) + chunks[seq]
            sock.sendto(payload, addr)
            if VERBOSE:
                print(f"  sent chunk {seq} ({len(chunks[seq])} bytes)", file=sys.stderr)
