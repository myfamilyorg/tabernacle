#!/usr/bin/env python3
"""FAMC chunk server -- serves a binary file over the FAMC UDP protocol.

Usage: server.py [binary_path] [port]
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
BINARY = 'tmp/node.bin'
PORT = 3737
VERBOSE = os.environ.get('VERBOSE', '') != ''

if len(sys.argv) > 1:
    BINARY = sys.argv[1]
if len(sys.argv) > 2:
    PORT = int(sys.argv[2])

with open(BINARY, 'rb') as f:
    data = f.read()

chunks = [data[i:i+CHUNK_SIZE] for i in range(0, len(data), CHUNK_SIZE)]
print(f"Loaded {BINARY}: {len(data)} bytes, {len(chunks)} chunk(s)")

sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
sock.bind(('0.0.0.0', PORT))
print(f"Listening on UDP :{PORT}...")

while True:
    pkt, addr = sock.recvfrom(65535)
    if len(pkt) < 9 or pkt[:4] != b'FAMC':
        continue
    cmd = pkt[4]
    if cmd == 0x02:  # REQ_RANGE
        start, end = struct.unpack('>HH', pkt[5:9])
        print(f"REQ_RANGE {start}..{end} from {addr}")
        for seq in range(start, min(end + 1, len(chunks))):
            payload = b'FAMC' + bytes([0x82]) + struct.pack('>H', seq) + chunks[seq]
            sock.sendto(payload, addr)
            if VERBOSE:
                print(f"  sent chunk {seq} ({len(chunks[seq])} bytes)")
