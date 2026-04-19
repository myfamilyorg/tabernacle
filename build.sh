#!/usr/bin/sh
# Bootstrap build. Each stage compiles the next from source using only the
# previous stage's binary. Nothing here depends on anything except QEMU —
# no python, no external assemblers, no libc.
#
# Stages:
#   fam0 → fam1 → fam2 → fam3 → famc    (compiler toolchain)
#   gen_bin_config                      (gimli-hash config generator;
#                                        reads full_node from virtio-blk)
#   full_node                           (the node image, compiled from
#                                        src/full_node.fam via famc)
#   tabernacle                          (node loader, assembled by fam3
#                                        against the current bin_config.inc)
#
# Usage: run <assembler> [--disk <image>] <source...>
# Multiple source files are concatenated before piping to the assembler.
# --disk attaches a raw disk image via virtio-blk.
set -e

CPU="rv32,m=false,a=false,f=false,d=false,c=false,\
zawrs=false,zfa=false,zfh=false,zfhmin=false,zcb=false,\
zcd=false,zcf=false,zcmp=false,zcmt=false,zicsr=false,zifencei=false"

run() {
	asm="$1"
	shift
	disk_args=""
	if [ "$1" = "--disk" ]; then
		disk_args="-drive file=$2,format=raw,if=none,id=hd0 -device virtio-blk-device,drive=hd0"
		shift 2
	fi
	echo "Compiling $*" >&2
	([ $# -gt 0 ] && cat "$@"; printf '\004') | qemu-system-riscv32 \
		-machine virt -cpu "$CPU" \
		-nographic -bios none \
		-device loader,file="$asm",addr=0x80000000 \
		$disk_args
}

# Build bootstrap tool chain
run fam0.seed src/fam0.fam0 > bin/fam0
cmp ./bin/fam0 ./fam0.seed || { echo "fam0: binaries don't match!"; exit 1; }
run bin/fam0 src/fam1.fam0 > bin/fam1
run bin/fam1 src/fam2.fam1 > bin/fam2
run bin/fam2 src/fam3.fam2 > bin/fam3
run bin/fam3 src/famc.fam3 > bin/famc

# Build config and full node
run bin/fam3 src/gen_bin_config.fam3 > bin/gen_bin_config
run bin/famc src/full_node.fam src/init.fam > bin/full_node

# Append compressed bible payload.
cat ./resources/bible.compressed >> ./bin/full_node

# Build raw disk image: sector 0 = 4-byte LE size header, sectors 1+ = payload.
echo "Generating src/bin_config.inc" >&2
SIZE=$(wc -c < bin/full_node)
{
	for i in 0 8 16 24; do
		byte=$(( (SIZE >> i) & 0xFF ))
		printf "\\$(printf '%03o' $byte)"
	done
	dd if=/dev/zero bs=1 count=508 2>/dev/null
	cat bin/full_node
} > tmp/full_node.img

run bin/gen_bin_config --disk tmp/full_node.img > src/bin_config.inc

rm -f tmp/full_node.img

# Rebuild tabernacle against the updated bin_config.
run bin/fam3 src/bin_config.inc src/tabernacle.fam3 > bin/tabernacle

echo "Success!"
