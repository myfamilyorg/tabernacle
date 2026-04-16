#!/usr/bin/sh
# Bootstrap build. Each stage compiles the next from source using only the
# previous stage's binary. No external tools other than QEMU.
#
# Stages:
#   fam0 → fam1 → fam2 → fam3 → famc    (compiler toolchain)
#   famchain                             (node loader, assembled by fam3)
#
# Usage: run <assembler> <source...>
# Multiple source files are concatenated before piping to the assembler.
# This is how famchain gets bin_config.inc in scope without .include.
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
run bin/fam3 src/bin_config.inc src/famchain.fam3 > bin/famchain

echo "Success!"
