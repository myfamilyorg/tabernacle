# MIT License
#
# Copyright (c) 2026 Christopher Gilliard
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

# ──────────────────────────────────────────────────────────────────────────────
# file: fam1.S - stage 1 bootstrap assembler (GNU as reference)
# RISC-V 32-bit Hex-to-Binary with Labels and Branch Fixups
# ──────────────────────────────────────────────────────────────────────────────
#
# Input format (superset of fam0):
#   Hex bytes:   "13 05 A0 00"      (same as fam0)
#   :NAME        define 4-char label at current output offset
#   @NAME        patch previous 4 bytes: encode B-type (0x63) or
#                J-type (0x6F) immediate to point to NAME
#   # ...        line comments       (same as fam0)
#   EOT (^D)     end of input        (same as fam0)
#
# After EOT, all @-fixups are resolved (supports forward references),
# then the assembled binary is output via UART.
#
# Memory layout (QEMU virt, loaded at 0x80000000):
#   0x80000000  code
#   0x80001000  label table   (512 entries × 8 bytes)
#   0x80002000  fixup table   (512 entries × 8 bytes)
#   0x80003000  output buffer
#
# Register map:
#   s1  = output buffer base / read ptr (output phase)
#   s2  = output buffer write ptr
#   s3  = nibble toggle (1=high expected, 0=low expected)
#   s4  = comment flag (0=no, 1=yes)
#   s5  = UART base (0x10000000)
#   s6  = constant 10 ('\n' and hex digit limit)
#   s7  = label table base
#   s8  = label table write ptr
#   s9  = fixup table base
#   s10 = fixup table write ptr
#   t4  = high nibble accumulator (across loop iterations)

_start:
	nop				# q32 magic
	# ── Constants ──
	li	s6, 10			# '\n' and hex limit
	lui	s5, 0x10000		# UART base 0x10000000

	# ── State ──
	li	s4, 0			# Comment flag off
	li	s3, 1			# Nibble toggle (1=high)

	# ── Memory regions ──
	lui	s7, 0x80001		# Label table  @ 0x80001000
	mv	s8, s7
	lui	s9, 0x80002		# Fixup table  @ 0x80002000
	mv	s10, s9
	lui	s1, 0x80003		# Output buffer @ 0x80003000
	mv	s2, s1

# ─── Main Input Loop ─────────────────────────────────────────────────
loop:
	lbu	t5, 5(s5)		# UART status
	andi	t5, t5, 1		# Data ready?
	beqz	t5, loop
	lbu	t1, 0(s5)		# Read character

	# Newline clears comment
	bne	t1, s6, not_nl
	li	s4, 0
not_nl:
	# '#' starts comment
	li	t3, '#'
	bne	t1, t3, not_hash
	li	s4, 1
not_hash:

	# EOT → resolve fixups and output
	li	t3, 4
	beq	t1, t3, resolve

	# In comment → skip
	bnez	s4, loop

	# ':' → label definition
	li	t3, ':'
	beq	t1, t3, label_def

	# '@' → fixup reference
	li	t3, '@'
	beq	t1, t3, fixup_ref

	# Whitespace / control → skip
	li	t3, 33
	blt	t1, t3, loop

	# Hex conversion
	addi	t1, t1, -48		# '0' → 0
	bltu	t1, s6, store		# 0–9 valid
	addi	t1, t1, -7		# 'A' → 10
	li	t3, 16
	bltu	t1, t3, store		# 10–15 valid
	j	loop			# invalid → skip

# ─── Nibble Packing ──────────────────────────────────────────────────
store:
	xori	s3, s3, 1		# Toggle high/low
	bnez	s3, store_low		# Was high → now store low
	slli	t4, t1, 4		# Save high nibble
	j	loop
store_low:
	or	t4, t4, t1		# Pack high | low
	sb	t4, 0(s2)		# Write byte
	addi	s2, s2, 1
	j	loop

# ─── Label Definition ────────────────────────────────────────────────
# Read 4 chars from UART, store (name, output_addr) in label table
label_def:
	li	t3, 0			# Byte counter
ld_poll:
	lbu	t5, 5(s5)
	andi	t5, t5, 1
	beqz	t5, ld_poll
	lbu	t1, 0(s5)		# Read name char
	add	t0, s8, t3
	sb	t1, 0(t0)		# Store in table entry
	addi	t3, t3, 1
	li	t0, 4
	bne	t3, t0, ld_poll
	sw	s2, 4(s8)		# Record current output address
	addi	s8, s8, 8		# Advance table pointer
	j	loop

# ─── Fixup Reference ─────────────────────────────────────────────────
# Read 4 chars from UART, store (name, instr_addr) in fixup table
fixup_ref:
	li	t3, 0			# Byte counter
fu_poll:
	lbu	t5, 5(s5)
	andi	t5, t5, 1
	beqz	t5, fu_poll
	lbu	t1, 0(s5)		# Read name char
	add	t0, s10, t3
	sb	t1, 0(t0)		# Store in table entry
	addi	t3, t3, 1
	li	t0, 4
	bne	t3, t0, fu_poll
	addi	t0, s2, -4		# Instruction = last 4 bytes written
	sw	t0, 4(s10)		# Record instruction address
	addi	s10, s10, 8		# Advance table pointer
	j	loop

# ─── Resolve Fixups ──────────────────────────────────────────────────
# Iterate fixup table, look up each name, patch the instruction
resolve:
	mv	t6, s9			# t6 = fixup iterator

res_loop:
	beq	t6, s10, output		# All fixups done → output

	lw	t3, 0(t6)		# Fixup name (as word)
	lw	t2, 4(t6)		# Instruction address in output buf

	# Search label table for name
	mv	t0, s7			# t0 = label table scan ptr
search:
	beq	t0, s8, res_next	# End of table → not found, skip
	lw	t1, 0(t0)		# Label name (as word)
	beq	t1, t3, found
	addi	t0, t0, 8
	j	search

found:
	lw	t1, 4(t0)		# t1 = label address
	sub	t1, t1, t2		# t1 = offset (label − instruction)

	# Determine type from opcode byte
	lbu	t3, 0(t2)		# Opcode byte of instruction
	andi	t3, t3, 0x7F

	li	t0, 0x63
	beq	t3, t0, patch_b		# B-type branch
	li	t0, 0x6F
	beq	t3, t0, patch_j		# J-type jump
	j	res_next		# Unknown → skip

# ─── Patch B-type Immediate ──────────────────────────────────────────
# B-type: imm[12|10:5] rs2 rs1 funct3 imm[4:1|11] opcode
patch_b:
	lw	t0, 0(t2)		# Load instruction
	li	t3, 0			# Build encoded immediate

	srli	t4, t1, 12		# imm[12] → inst[31]
	andi	t4, t4, 1
	slli	t4, t4, 31
	or	t3, t3, t4

	srli	t4, t1, 5		# imm[10:5] → inst[30:25]
	andi	t4, t4, 0x3F
	slli	t4, t4, 25
	or	t3, t3, t4

	srli	t4, t1, 1		# imm[4:1] → inst[11:8]
	andi	t4, t4, 0xF
	slli	t4, t4, 8
	or	t3, t3, t4

	srli	t4, t1, 11		# imm[11] → inst[7]
	andi	t4, t4, 1
	slli	t4, t4, 7
	or	t3, t3, t4

	or	t0, t0, t3		# Merge immediate into instruction
	sw	t0, 0(t2)		# Store patched instruction
	j	res_next

# ─── Patch J-type Immediate ──────────────────────────────────────────
# J-type: imm[20|10:1|11|19:12] rd opcode
patch_j:
	lw	t0, 0(t2)		# Load instruction
	li	t3, 0			# Build encoded immediate

	srli	t4, t1, 20		# imm[20] → inst[31]
	andi	t4, t4, 1
	slli	t4, t4, 31
	or	t3, t3, t4

	srli	t4, t1, 1		# imm[10:1] → inst[30:21]
	andi	t4, t4, 0x3FF
	slli	t4, t4, 21
	or	t3, t3, t4

	srli	t4, t1, 11		# imm[11] → inst[20]
	andi	t4, t4, 1
	slli	t4, t4, 20
	or	t3, t3, t4

	srli	t4, t1, 12		# imm[19:12] → inst[19:12]
	andi	t4, t4, 0xFF
	slli	t4, t4, 12
	or	t3, t3, t4

	or	t0, t0, t3		# Merge immediate into instruction
	sw	t0, 0(t2)		# Store patched instruction
	# fall through

res_next:
	addi	t6, t6, 8
	j	res_loop

# ─── Output ──────────────────────────────────────────────────────────
output:
	beq	s1, s2, shutdown	# Empty → exit
	lbu	t3, 0(s1)		# Load byte
	addi	s1, s1, 1
tx_poll:
	lbu	t1, 5(s5)		# UART status
	andi	t1, t1, 0x20		# TX ready?
	beqz	t1, tx_poll
	sb	t3, 0(s5)		# Send byte
	j	output

# ─── Shutdown ────────────────────────────────────────────────────────
shutdown:
	lui	s5, 0x100		# QEMU virt test device 0x100000
	lui	t1, 0x5			# 0x5000
	addi	t1, t1, 0x555		# 0x5555 (power off)
	sw	t1, 0(s5)
