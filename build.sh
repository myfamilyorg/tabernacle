#!/usr/bin/env sh
# Bootstrap build. Each stage compiles the next from source using only the
# previous stage's binary. No external tools other than QEMU.
set -e
run() {
	(cat "$2"; printf '\004') | qemu-system-riscv32 \
		-machine virt \
		-cpu rv32,\
m=false,a=false,f=false,d=false,c=false,zawrs=false,zfa=false,\
zfh=false,zfhmin=false,zcb=false,zcd=false,zcf=false,zcmp=false,\
zcmt=false,zicsr=false,zifencei=false \
		-nographic \
		-bios none \
		-device loader,file="$1",addr=0x80000000
}
run fam0.seed src/fam0.fam0 > bin/fam0
cmp ./bin/fam0 ./fam0.seed || { echo "fam0: binaries don't match!"; exit 1; }
run bin/fam0 src/fam1.fam0 > bin/fam1
run bin/fam1 src/fam2.fam1 > bin/fam2
run bin/fam2 src/fam3.fam2 > bin/fam3
run bin/fam3 src/famc.fam3 > bin/famc

echo "Success!";
