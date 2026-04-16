#!/usr/bin/env python3
"""Generate bin_config.inc from a binary file.

Hashes the target binary with Gimli-Hash (see tools/gimli.py) and emits
the hash + size as fam3 `.equ` directives that famchain.fam3 includes
(via a build-time concatenation, since fam3 has no .include).

Usage: python3 tools/gen_bin_config.py <binary> [output_dir]

If output_dir is specified, writes bin_config.inc there.
Otherwise writes to stdout.
"""
import os
import struct
import sys

# Import the reference Gimli from sibling tools/gimli.py.
_here = os.path.dirname(os.path.abspath(__file__))
if _here not in sys.path:
    sys.path.insert(0, _here)
import gimli  # noqa: E402


def main() -> None:
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <binary> [output_dir]", file=sys.stderr)
        sys.exit(1)

    binary_path = sys.argv[1]
    data = open(binary_path, 'rb').read()
    digest = gimli.gimli_hash(data, 32)
    words = struct.unpack('<8I', digest)

    lines = [
        f"# bin_config.inc — auto-generated from {os.path.basename(binary_path)}",
        f"# Hash function: gimli-hash (rate=16, capacity=32, output=32)",
        f".equ\tBIN_SIZE,\t\t{len(data)}",
    ]
    for i, w in enumerate(words):
        lines.append(f".equ\tBIN_HASH{i},\t\t0x{w:08X}")

    output = '\n'.join(lines) + '\n'

    if len(sys.argv) >= 3:
        path = os.path.join(sys.argv[2], 'bin_config.inc')
        with open(path, 'w') as f:
            f.write(output)
        if os.environ.get('VERBOSE') == '1':
            print(f"Wrote {path}", file=sys.stderr)
    else:
        sys.stdout.write(output)


if __name__ == '__main__':
    main()
