#!/bin/sh
# Build and optionally run tabsimple.
# Usage: buildtabsimple.sh [--payload] [--run]
#   --payload  Build payload, generate config and disk image first
#   --run      Run tabsimple after building
set -e

SELF="$0"
[ -L "$SELF" ] && SELF="$(readlink -f "$SELF")"
SCRIPT_DIR="$(cd "$(dirname "$SELF")" && pwd)"
ROOT_DIR="$(dirname "$SCRIPT_DIR")"

PAYLOAD_SRC="$ROOT_DIR/src/tabsimple_payload.fam3"
PAYLOAD_BIN="$ROOT_DIR/bin/tabsimple_payload"
CONFIG="$ROOT_DIR/src/tabsimple_config.inc"
SRC="$ROOT_DIR/src/tabsimple.fam3"
TMP="$ROOT_DIR/tmp/tabsimple_full.fam3"
OUT="$ROOT_DIR/bin/tabsimple"
DISK="$ROOT_DIR/tmp/test.img"

BUILD_PAYLOAD=0
RUN=0
for arg in "$@"; do
	case "$arg" in
		--payload) BUILD_PAYLOAD=1 ;;
		--run) RUN=1 ;;
	esac
done

if [ "$BUILD_PAYLOAD" = "1" ]; then
	"$SCRIPT_DIR/fam3" "$PAYLOAD_SRC" "$PAYLOAD_BIN"
	dd if="$PAYLOAD_BIN" of="$DISK" bs=512 conv=sync 2>/dev/null
	SIZE=$(wc -c < "$PAYLOAD_BIN")
	{
		for i in 0 8 16 24; do
			byte=$(( (SIZE >> i) & 0xFF ))
			printf "\\$(printf '%03o' $byte)"
		done
		dd if=/dev/zero bs=1 count=508 2>/dev/null
		cat "$PAYLOAD_BIN"
	} > "$ROOT_DIR/tmp/tabsimple_payload.img"
	"$SCRIPT_DIR/q32" --disk="$ROOT_DIR/tmp/tabsimple_payload.img" "$ROOT_DIR/bin/gen_bin_config" > "$CONFIG"
	rm -f "$ROOT_DIR/tmp/tabsimple_payload.img"
fi

cat "$CONFIG" "$SRC" > "$TMP"
"$SCRIPT_DIR/fam3" "$TMP" "$OUT"

if [ "$RUN" = "1" ]; then
	"$SCRIPT_DIR/q32" --disk="$DISK" "$OUT"
fi
