#!/usr/bin/sh
# Bootstrap build. Each stage compiles the next from source using only the
# previous stage's binary. Nothing here depends on anything except QEMU —
# no python, no external assemblers, no libc.
#
# Stages:
#   fam0 → fam1 → fam2 → fam3 → famc    (compiler toolchain)
#   gen_bin_config                      (self-hosted gimli-hash + config
#                                        generator, used by
#                                        tools/refresh_bin_config)
#   full_node                           (the node image, compiled from
#                                        src/full_node.fam via famc)
#   tabernacle                          (node loader, assembled by fam3
#                                        against the current bin_config.inc)
#
# Usage: run <assembler> <source...>
# Multiple source files are concatenated before piping to the assembler.
# This is how tabernacle gets bin_config.inc in scope without .include.
set -e

CPU="rv32,m=false,a=false,f=false,d=false,c=false,\
zawrs=false,zfa=false,zfh=false,zfhmin=false,zcb=false,\
zcd=false,zcf=false,zcmp=false,zcmt=false,zicsr=false,zifencei=false"

run() {
	asm="$1"
	shift
	echo "Compiling $*" >&2
	(cat "$@"; printf '\004') | qemu-system-riscv32 \
		-machine virt -cpu "$CPU" \
		-nographic -bios none \
		-device loader,file="$asm",addr=0x80000000
}

run fam0.seed src/fam0.fam0 > bin/fam0
cmp ./bin/fam0 ./fam0.seed || { echo "fam0: binaries don't match!"; exit 1; }
run bin/fam0 src/fam1.fam0 > bin/fam1
run bin/fam1 src/fam2.fam1 > bin/fam2
run bin/fam2 src/fam3.fam2 > bin/fam3
run bin/fam3 src/famc.fam3 > bin/famc

# Self-hosted gimli-hash + bin_config generator (used by
# tools/refresh_bin_config to regenerate src/bin_config.inc without python).
run bin/fam3 src/gen_bin_config.fam3 > bin/gen_bin_config

# Compile the node binary with the freshly-built famc. Pass the source
# directly (no stdlib prepend) — full_node.fam emits its own UART helper
# and doesn't need stdlib's puts.
run bin/famc src/full_node.fam > bin/full_node

# Tabernacle is compiled against the checked-in src/bin_config.inc. If
# full_node.fam has changed in a way that shifts its hash or size, the
# checked-in bin_config is stale — run tools/refresh_bin_config and then
# re-run build.sh.
run bin/fam3 src/bin_config.inc src/tabernacle.fam3 > bin/tabernacle

# Stage the node binary where tools/server.py looks for it by default.
mkdir -p tmp
cp bin/full_node tmp/node.bin
echo "Staged tmp/node.bin ($(wc -c < tmp/node.bin) bytes)" >&2

echo "Success!"
