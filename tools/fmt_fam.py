#!/usr/bin/env python3
"""Format .fam source files to consistent tab-indented style.

Convention:
  - Tabs for indentation (1 tab per nesting level)
  - { at end of line increases indent for following lines
  - } decreases indent (placed at current-1 level)
  - Short single-line blocks left as-is (e.g. |x| { expr })
  - // comments preserved
  - Blank lines preserved
  - Semicolons preserved as-is

Usage: python3 tools/fmt_fam.py < input.fam > output.fam
       python3 tools/fmt_fam.py file.fam  (in-place)
"""

import sys


def count_braces(line):
    """Count net brace change, ignoring braces in strings/chars/comments."""
    opens = 0
    closes = 0
    i = 0
    in_string = False
    in_char = False
    while i < len(line):
        c = line[i]
        if in_string:
            if c == '\\':
                i += 1  # skip escaped char
            elif c == '"':
                in_string = False
        elif in_char:
            if c == '\\':
                i += 1
            elif c == "'":
                in_char = False
        elif c == '/' and i + 1 < len(line) and line[i + 1] == '/':
            break  # rest is comment
        elif c == '"':
            in_string = True
        elif c == "'":
            in_char = True
        elif c == '{':
            opens += 1
        elif c == '}':
            closes += 1
        i += 1
    return opens, closes


def format_fam(text):
    lines = text.split('\n')
    result = []
    indent = 0

    for line in lines:
        stripped = line.strip()

        # Blank lines
        if not stripped:
            result.append('')
            continue

        opens, closes = count_braces(stripped)

        # Determine indent for this line:
        # Lines starting with } get dedented first
        leading_closes = 0
        s = stripped
        while s and s[0] == '}':
            leading_closes += 1
            s = s[1:].lstrip(';').lstrip().lstrip(',').lstrip()
            if not s:
                break

        this_indent = max(0, indent - leading_closes)
        result.append('\t' * this_indent + stripped)

        # Update indent for next line
        # Leading closes already accounted for in this_indent
        remaining_closes = closes - leading_closes
        indent = this_indent + opens - remaining_closes

        # Clamp
        indent = max(0, indent)

    # Collapse consecutive blank lines to at most one
    collapsed = []
    prev_blank = False
    for line in result:
        if line == '':
            if not prev_blank:
                collapsed.append(line)
            prev_blank = True
        else:
            collapsed.append(line)
            prev_blank = False
    result = collapsed

    # Remove trailing blank lines
    while result and result[-1] == '':
        result.pop()

    return '\n'.join(result) + '\n'


def main():
    if len(sys.argv) > 1:
        fname = sys.argv[1]
        with open(fname, 'r') as f:
            text = f.read()
        formatted = format_fam(text)
        with open(fname, 'w') as f:
            f.write(formatted)
    else:
        text = sys.stdin.read()
        sys.stdout.write(format_fam(text))


if __name__ == '__main__':
    main()
