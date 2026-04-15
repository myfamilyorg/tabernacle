#!/usr/bin/env python3
"""Format assembly source to the famc tab convention.

Convention:
  - Labels at column 0 (no indent), optional  # comment after space
  - Instructions: TAB mnemonic TAB operands TAB TAB # comment
  - Pure comment lines: # at column 0
  - Hex data lines: TAB hex bytes TAB TAB # comment
  - Blank lines preserved
  - Section dividers (# ===...) preserved at column 0

Usage: python3 tools/fmt_asm.py < input.S > output.S
       python3 tools/fmt_asm.py file.S  (in-place)
"""

import sys
import re


COMMENT_COL = 40  # target column for comments (tab stop 5)
TAB = 8            # tab stop width


def tabs_to(col, target):
    """Return enough tabs to advance from col to at least target."""
    if col >= target:
        return '\t'  # at least one tab
    n = 0
    while col < target:
        col = (col // TAB + 1) * TAB
        n += 1
    return '\t' * n


def is_hex_byte(tok):
    """Check if token is a 2-char hex byte."""
    return len(tok) == 2 and all(c in '0123456789ABCDEFabcdef' for c in tok)


def format_line(line):
    """Format a single line to the tab convention."""
    stripped = line.rstrip()

    # Blank line
    if stripped == '':
        return ''

    # Split code and comment (careful with strings)
    code = stripped
    comment = ''
    in_string = False
    for i, c in enumerate(stripped):
        if c == '"':
            in_string = not in_string
        elif c == '#' and not in_string:
            code = stripped[:i].rstrip()
            comment = stripped[i:]
            break

    # Pure comment line (no code before #)
    if code == '' and comment:
        # Preserve indentation: if original line was indented, keep one tab
        if stripped[0] in (' ', '\t'):
            return '\t' + comment
        return comment

    # Label line: starts with non-whitespace, contains ':'
    code_stripped = code.strip()

    if code_stripped and not code_stripped[0].isspace():
        m = re.match(r'^(\w+:)(.*)', code_stripped)
        if m:
            label = m.group(1)
            rest = m.group(2).strip()
            if rest:
                # Label with trailing instruction (unusual, keep on one line)
                return label + ' ' + rest + (tabs_to(len(label) + 1 + len(rest), COMMENT_COL) + comment if comment else '')
            elif comment:
                return label + tabs_to(len(label), COMMENT_COL) + comment
            else:
                return label

    # Definition directives: no indent (like labels)
    DEFS = ('.equ', '.set', '.macro')
    for d in DEFS:
        if code_stripped.startswith(d + ' ') or code_stripped.startswith(d + '\t'):
            parts = code_stripped.split(None, 1)
            directive = parts[0]
            args = parts[1] if len(parts) > 1 else ''
            line_out = directive + '\t' + args if args else directive
            if comment:
                col = ((len(directive) // TAB) + 1) * TAB + len(args) if args else len(directive)
                return line_out + tabs_to(col, COMMENT_COL) + comment
            return line_out

    # Instruction or hex data line
    if not code_stripped:
        # Whitespace-only line with comment
        return comment if comment else ''

    # Parse: mnemonic/first-token + operands
    tokens = code_stripped.split(None, 1)
    mnemonic = tokens[0]
    operands = tokens[1] if len(tokens) > 1 else ''

    # Clean up operand spacing: normalize to single spaces after commas
    if operands:
        operands = re.sub(r'\s*,\s*', ', ', operands)

    # Check if this is a hex data line (first token is hex byte)
    if is_hex_byte(mnemonic):
        hex_part = code_stripped
        if comment:
            return '\t' + hex_part + tabs_to(8 + len(hex_part), 40) + comment
        return '\t' + hex_part

    # Regular instruction
    # Mnemonic starts at col 8, operands at col 16. Align comments to col 40.
    instr = '\t' + mnemonic + '\t' + operands if operands else '\t' + mnemonic
    if comment:
        # Compute current column: 8 + mnemonic rounded to next tab + operands
        col = 16 + len(operands) if operands else 8 + len(mnemonic)
        return instr + tabs_to(col, 40) + comment
    return instr


def main():
    if len(sys.argv) > 1 and sys.argv[1] != '-':
        filename = sys.argv[1]
        with open(filename) as f:
            lines = f.readlines()
        inplace = '--check' not in sys.argv
    else:
        lines = sys.stdin.readlines()
        inplace = False

    formatted = []
    for line in lines:
        formatted.append(format_line(line))

    # Collapse consecutive blank lines: max 1
    out = []
    for line in formatted:
        if line == '' and out and out[-1] == '':
            continue  # skip consecutive blank
        out.append(line)

    result = '\n'.join(out)
    if not result.endswith('\n'):
        result += '\n'

    if inplace and len(sys.argv) > 1 and sys.argv[1] != '-':
        with open(filename, 'w') as f:
            f.write(result)
    else:
        sys.stdout.write(result)


if __name__ == '__main__':
    main()
