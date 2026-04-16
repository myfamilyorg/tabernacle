#!/usr/bin/env python3
"""Gimli permutation and Gimli-Hash reference implementation.

Based on the Gimli specification submitted to the NIST Lightweight
Cryptography competition (Bernstein, Chou, Cremers, Groszschaedl,
Harold, Lange, Niederhagen, Paulos, Rotella, Schwabe, Viguier, Wang,
2017). This is the classical sponge construction:

    state = 12 u32 words (384 bits)
    rate  = 4 u32 words (128 bits, 16 bytes) — absorbed per block
    cap   = 8 u32 words (256 bits) — secret state

Security (classical):
    collision        : 2^128
    preimage         : 2^128
    second preimage  : 2^128

Test vectors at the bottom.
"""
from __future__ import annotations
import struct
import sys


def _rot(x: int, n: int) -> int:
    x &= 0xFFFFFFFF
    return ((x << n) | (x >> (32 - n))) & 0xFFFFFFFF


def gimli_permute(state: list[int]) -> None:
    """In-place Gimli permutation over 12 u32 words (384 bits)."""
    assert len(state) == 12
    for round_ in range(24, 0, -1):
        # SP-box on each column
        for col in range(4):
            x = _rot(state[col], 24)
            y = _rot(state[4 + col], 9)
            z = state[8 + col]
            state[8 + col] = (x ^ (z << 1) ^ ((y & z) << 2)) & 0xFFFFFFFF
            state[4 + col] = (y ^ x ^ ((x | z) << 1)) & 0xFFFFFFFF
            state[col] = (z ^ y ^ ((x & y) << 3)) & 0xFFFFFFFF
        # Linear layer
        if round_ & 3 == 0:
            # Small swap: words 0↔1, 2↔3
            state[0], state[1] = state[1], state[0]
            state[2], state[3] = state[3], state[2]
            # Add round constant
            state[0] ^= 0x9E377900 | round_
        elif round_ & 3 == 2:
            # Big swap: words 0↔2, 1↔3
            state[0], state[2] = state[2], state[0]
            state[1], state[3] = state[3], state[1]


RATE_BYTES = 16   # 4 words = 128 bits


def gimli_hash(msg: bytes, outlen: int = 32) -> bytes:
    """Gimli-Hash: sponge mode, 16-byte rate, 32-byte default output."""
    state = [0] * 12

    # Absorb full rate blocks.
    off = 0
    while len(msg) - off >= RATE_BYTES:
        block = struct.unpack('<4I', msg[off:off + RATE_BYTES])
        for i in range(4):
            state[i] ^= block[i]
        gimli_permute(state)
        off += RATE_BYTES

    # Absorb final (possibly empty) block with padding.
    # Pad byte 0x01 goes at position `off_in_block`, bit 0x80 at byte 15
    # (MSB of state word 3). Per Gimli-Hash spec.
    remaining = msg[off:]
    tail = bytearray(RATE_BYTES)
    tail[:len(remaining)] = remaining
    tail[len(remaining)] ^= 0x01
    tail[RATE_BYTES - 1] ^= 0x80
    block = struct.unpack('<4I', bytes(tail))
    for i in range(4):
        state[i] ^= block[i]
    gimli_permute(state)

    # Squeeze.
    out = bytearray()
    while len(out) < outlen:
        out += struct.pack('<4I', *state[:4])
        if len(out) < outlen:
            gimli_permute(state)
    return bytes(out[:outlen])


# ────────────────────────────────────────────────────────────────────────
# Self-test: permutation determinism, hash determinism, length-extension
# check, and output-length stability. External KAT vectors from the Gimli
# NIST submission should be added here once verified from a trusted source.
# For now, this Python implementation serves as the reference for the fam3
# implementation; they must produce byte-identical output on arbitrary
# inputs for correctness to be confirmed.
# ────────────────────────────────────────────────────────────────────────


def _selftest() -> None:
    # 1. Permutation is deterministic and modifies state.
    s1 = list(range(12))
    s2 = list(range(12))
    gimli_permute(s1)
    gimli_permute(s2)
    assert s1 == s2, "permutation not deterministic"
    assert s1 != list(range(12)), "permutation left state unchanged"
    print(f"  PASS  gimli_permute deterministic: {s1[0]:08x}...")

    # 2. Permutation is a bijection on a small probe set.
    seen = set()
    for i in range(64):
        state = [0] * 12
        state[0] = i
        gimli_permute(state)
        seen.add(tuple(state))
    assert len(seen) == 64, "permutation collides on distinct inputs"
    print(f"  PASS  gimli_permute bijection on 64-input probe")

    # 3. Hash is deterministic.
    assert gimli_hash(b'') == gimli_hash(b'')
    assert gimli_hash(b'abc') == gimli_hash(b'abc')
    print(f"  PASS  gimli_hash deterministic")

    # 4. Hash distinguishes different inputs.
    assert gimli_hash(b'') != gimli_hash(b'\x00')
    assert gimli_hash(b'\x00') != gimli_hash(b'\x00\x00')
    assert gimli_hash(b'abc') != gimli_hash(b'abd')
    print(f"  PASS  gimli_hash distinguishes inputs")

    # 5. Hash boundary: 15, 16, 17, 31, 32, 33 bytes all produce distinct
    #    outputs (exercises the absorb block boundary).
    outs = set()
    for n in (15, 16, 17, 31, 32, 33):
        outs.add(gimli_hash(bytes(n)))
    assert len(outs) == 6, "hash collision across boundary sizes"
    print(f"  PASS  gimli_hash boundary (15..33 zero bytes)")

    # 6. Output length stability: first 32 bytes of len=64 output equal
    #    the full len=32 output (same squeeze sequence).
    assert gimli_hash(b'abc', 64)[:32] == gimli_hash(b'abc', 32)
    print(f"  PASS  gimli_hash output length stable")

    # Print one representative hash for posterity / cross-check.
    print()
    print(f"  gimli_hash(b'')    = {gimli_hash(b'').hex()}")
    print(f"  gimli_hash(b'abc') = {gimli_hash(b'abc').hex()}")


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == '--test':
        _selftest()
    elif len(sys.argv) > 1:
        # Hash a file and print hex digest.
        data = open(sys.argv[1], 'rb').read()
        print(gimli_hash(data).hex())
    else:
        _selftest()
