#!/bin/sh
# Build and optionally run tabsimple.
# Usage: buildtabsimple.sh [--run]
set -e

SELF="$0"
[ -L "$SELF" ] && SELF="$(readlink -f "$SELF")"
SCRIPT_DIR="$(cd "$(dirname "$SELF")" && pwd)"
ROOT_DIR="$(dirname "$SCRIPT_DIR")"

CONFIG="$ROOT_DIR/src/tabsimple_config.inc"
SRC="$ROOT_DIR/src/tabsimple.fam3"
TMP="$ROOT_DIR/tmp/tabsimple_full.fam3"
OUT="$ROOT_DIR/bin/tabsimple"
DISK="$ROOT_DIR/tmp/test.img"

cat "$CONFIG" "$SRC" > "$TMP"
"$SCRIPT_DIR/fam3" "$TMP" "$OUT"

if [ "$1" = "--run" ]; then
	"$SCRIPT_DIR/q32" --disk="$DISK" "$OUT"
fi
