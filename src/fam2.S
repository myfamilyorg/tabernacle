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
# fam2.S — RV32I mnemonic assembler (third-stage bootstrap)
# ──────────────────────────────────────────────────────────────────────────────
#
# Reads text from UART (terminated by EOT = 0x04), emits a RISC-V binary
# back over UART, then poweroffs.
#
# Grammar:
#   # ... \n                    comment (to end of line)
#   whitespace / comma          token separators (interchangeable)
#   name:                       label definition (name <= 31 ASCII chars)
#   XX                          passthrough hex byte (exactly 2 uppercase hex)
#   mnemonic operands           RV32I instruction or pseudo
#
# Supported mnemonics (RV32I base, minus jalr — static jumps only):
#   R-type:  add sub and or xor sll srl sra slt sltu
#   I-type:  addi andi ori xori slti sltiu slli srli srai
#   Load:    lb lh lw lbu lhu
#   Store:   sb sh sw
#   Branch:  beq bne blt bge bltu bgeu
#   U-type:  lui auipc
#   Jump:    jal
# Pseudos:  nop li mv j beqz bnez
#
# Register convention:
#   s0  = token length          s1  = output buf base
#   s2  = output write ptr      s3  = symtab base
#   s4  = symtab write ptr      s5  = UART base (0x10000000)
#   s6  = 10 (constant)         s7  = fixup base
#   s8  = fixup write ptr       s9  = mnem_table base
#   s10 = token buf base        s11 = reg_table base
#   sp  = descending stack      t0-t6, a0-a7, ra = scratch
#   gp  = return-site ID for currently-executing callee's dispatcher
#
# Memory layout:
#   0x80000000  code + data tables (~5 KB)
#   +0x10000    output buffer (64 KB)
#   +0x20000    symtab  (40-byte entries: 32-byte name + 4 offset + 4 pad)
#   +0x30000    fixup   (40-byte entries: 32-byte name + 4 instr_addr + 4 pad)
#   +0x40000    token buffer (64 bytes)
#   +0x50000    stack top (grows down)
#
# Calling convention (static jumps only — no jalr/ret):
#   - Caller sets gp = <site-id>, then `j callee`
#   - Non-leaf callees save/restore gp on stack across sub-calls
#   - Callee ends with `j <callee>_disp`; dispatcher enumerates direct callers
#   - args in a0..a5, returns in a0 (a1 for two-value)
#   - s-regs are global; subroutines must not clobber

.section .text
.globl _start

# ═══════════════════════════════════════════════════════════════════════
# Format codes (in mnemonic table byte 12)
# ═══════════════════════════════════════════════════════════════════════
.equ FMT_R,     0
.equ FMT_I,     1
.equ FMT_S,     2
.equ FMT_B,     3
.equ FMT_U,     4
.equ FMT_J,     5
.equ FMT_PSEUDO,6
.equ FMT_LOAD,  7	# I-type with load parse pattern: rd, imm(rs1)

# Pseudo IDs (in mnemonic table byte 14)
.equ PS_NOP,    0
.equ PS_LI,     1
.equ PS_MV,     2
.equ PS_J,      3
.equ PS_BEQZ,   5
.equ PS_BNEZ,   6

# Token types (returned by next_token in a0)
.equ TOK_EOL,   0
.equ TOK_IDENT, 1
.equ TOK_NUM,   2
.equ TOK_LPAREN,4
.equ TOK_RPAREN,5
.equ TOK_LABEL, 6	# identifier followed by ':'
.equ TOK_EOT,   7

# ═══════════════════════════════════════════════════════════════════════
#  Initialization
# ═══════════════════════════════════════════════════════════════════════
_start:
	nop				# q32 magic

	# Constants
	li	s6, 10
	lui	s5, 0x10000		# UART 0x10000000

	# Compute base address
	auipc	a0, 0			# a0 = PC of this instruction
	addi	a0, a0, -16		# a0 = _start (back up past nop+li+lui)

	# Output buffer at _start + 0x10000
	lui	t0, 0x10
	add	s1, a0, t0
	mv	s2, s1

	# Symtab at _start + 0x20000
	lui	t0, 0x20
	add	s3, a0, t0
	mv	s4, s3

	# Fixup table at _start + 0x30000
	lui	t0, 0x30
	add	s7, a0, t0
	mv	s8, s7

	# Token buffer at _start + 0x40000
	lui	t0, 0x40
	add	s10, a0, t0

	# Stack at _start + 0x50000
	lui	t0, 0x50
	add	sp, a0, t0

	# Data tables (embedded in code section)
	la	s9, mnem_table
	la	s11, reg_table

	# Putback character (0 = none)
	# We use the word just before the token buffer for this
	sw	zero, -4(s10)

# ═══════════════════════════════════════════════════════════════════════
#  Main Loop
# ═══════════════════════════════════════════════════════════════════════
main_loop:
	li	gp, 0			# next_token site 0
	j	next_token
nt_rs0:

	# Dispatch on token type
	li	t0, TOK_EOT
	beq	a0, t0, resolve		# EOT → resolve fixups

	li	t0, TOK_EOL
	beq	a0, t0, main_loop	# skip blank/separator

	li	t0, TOK_LABEL
	beq	a0, t0, handle_label

	# Must be TOK_IDENT — mnemonic or hex passthrough
	# First try hex passthrough: exactly 2 chars, both valid uppercase hex
	li	t0, 2
	bne	s0, t0, try_mnemonic

	# Check if both chars are uppercase hex (0-9, A-F)
	lbu	t0, 0(s10)
	li	gp, 0			# is_upper_hex site 0
	j	is_upper_hex
iuh_rs0:
	beqz	a0, try_mnemonic
	lbu	t0, 1(s10)
	li	gp, 1			# is_upper_hex site 1
	j	is_upper_hex
iuh_rs1:
	beqz	a0, try_mnemonic

	# Hex passthrough: decode two hex chars → byte
	lbu	t0, 0(s10)
	li	gp, 0			# hex_val site 0
	j	hex_val
hv_rs0:
	mv	t1, a0
	slli	t1, t1, 4
	lbu	t0, 1(s10)
	li	gp, 1			# hex_val site 1
	j	hex_val
hv_rs1:
	or	t1, t1, a0
	sb	t1, 0(s2)
	addi	s2, s2, 1
	j	main_loop

try_mnemonic:
	li	gp, 0			# lookup_mnem site 0
	j	lookup_mnem
lm_rs0:
	beqz	a0, error_halt		# Unknown mnemonic

	mv	a5, a0			# a5 = mnemonic table entry ptr
	lw	a4, 8(a5)		# a4 = opcode template
	lbu	a3, 12(a5)		# a3 = format type

	# Dispatch on format
	li	t0, FMT_R
	beq	a3, t0, do_r_type
	li	t0, FMT_I
	beq	a3, t0, do_i_type
	li	t0, FMT_S
	beq	a3, t0, do_s_type
	li	t0, FMT_B
	beq	a3, t0, do_b_type
	li	t0, FMT_U
	beq	a3, t0, do_u_type
	li	t0, FMT_J
	beq	a3, t0, do_j_type
	li	t0, FMT_LOAD
	beq	a3, t0, do_load_type
	li	t0, FMT_PSEUDO
	beq	a3, t0, do_pseudo
	j	error_halt

# ═══════════════════════════════════════════════════════════════════════
#  Label Definition
# ═══════════════════════════════════════════════════════════════════════
handle_label:
	# Zero 40 bytes at s4
	mv	t0, s4
	addi	t1, s4, 40
hl_zero:
	sw	zero, 0(t0)
	addi	t0, t0, 4
	bne	t0, t1, hl_zero

	# Copy token buffer to symtab entry (up to 31 chars)
	mv	t0, s4			# dest
	mv	t1, s10			# src
	add	t2, s10, s0		# src end
hl_copy:
	beq	t1, t2, hl_store
	lbu	t3, 0(t1)
	sb	t3, 0(t0)
	addi	t0, t0, 1
	addi	t1, t1, 1
	j	hl_copy

hl_store:
	# Store output offset (address relative to output base)
	sub	t0, s2, s1
	sw	t0, 32(s4)
	addi	s4, s4, 40
	j	main_loop

# ═══════════════════════════════════════════════════════════════════════
#  Format Handlers
# ═══════════════════════════════════════════════════════════════════════

# ─── R-type: rd, rs1, rs2 ────────────────────────────────────────────
do_r_type:
	addi	sp, sp, -16
	sw	a4, 8(sp)		# save template

	li	gp, 0
	j	expect_reg
er_rs0:
	sw	a0, 4(sp)		# rd
	li	gp, 1
	j	expect_reg
er_rs1:
	sw	a0, 0(sp)		# rs1
	li	gp, 2
	j	expect_reg
er_rs2:
	mv	a3, a0			# rs2

	lw	a0, 8(sp)		# template
	lw	a1, 4(sp)		# rd
	lw	a2, 0(sp)		# rs1
	li	gp, 0
	j	encode_r
enc_r_rs0:
	addi	sp, sp, 16
	j	main_loop

# ─── I-type: rd, rs1, imm ────────────────────────────────────────────
do_i_type:
	addi	sp, sp, -16
	sw	a4, 8(sp)

	li	gp, 3
	j	expect_reg
er_rs3:
	sw	a0, 4(sp)		# rd
	li	gp, 4
	j	expect_reg
er_rs4:
	sw	a0, 0(sp)		# rs1
	li	gp, 0
	j	expect_imm
ei_rs0:
	mv	a3, a0			# imm

	lw	a0, 8(sp)		# template
	lw	a1, 4(sp)		# rd
	lw	a2, 0(sp)		# rs1
	li	gp, 0
	j	encode_i
enc_i_rs0:
	addi	sp, sp, 16
	j	main_loop

# ─── Load: rd, imm(rs1) ──────────────────────────────────────────────
do_load_type:
	addi	sp, sp, -16
	sw	a4, 8(sp)

	li	gp, 5
	j	expect_reg
er_rs5:
	sw	a0, 4(sp)		# rd
	li	gp, 1
	j	expect_imm
ei_rs1:
	sw	a0, 0(sp)		# imm
	li	gp, 0
	j	expect_lparen
elp_rs0:
	li	gp, 6
	j	expect_reg
er_rs6:
	mv	a2, a0			# rs1
	li	gp, 0
	j	expect_rparen
erp_rs0:

	lw	a0, 8(sp)		# template
	lw	a1, 4(sp)		# rd
	# a2 = rs1
	lw	a3, 0(sp)		# imm
	li	gp, 1
	j	encode_i
enc_i_rs1:
	addi	sp, sp, 16
	j	main_loop

# ─── S-type: rs2, imm(rs1) ───────────────────────────────────────────
do_s_type:
	addi	sp, sp, -16
	sw	a4, 8(sp)

	li	gp, 9
	j	expect_reg
er_rs9:
	sw	a0, 4(sp)		# rs2
	li	gp, 3
	j	expect_imm
ei_rs3:
	sw	a0, 0(sp)		# imm
	li	gp, 2
	j	expect_lparen
elp_rs2:
	li	gp, 10
	j	expect_reg
er_rs10:
	mv	a1, a0			# rs1
	li	gp, 2
	j	expect_rparen
erp_rs2:

	lw	a0, 8(sp)		# template
	# a1 = rs1
	lw	a2, 4(sp)		# rs2
	lw	a3, 0(sp)		# imm
	li	gp, 0
	j	encode_s
enc_s_rs0:
	addi	sp, sp, 16
	j	main_loop

# ─── B-type: rs1, rs2, label/imm ─────────────────────────────────────
do_b_type:
	addi	sp, sp, -20
	sw	a4, 12(sp)

	li	gp, 11
	j	expect_reg
er_rs11:
	sw	a0, 8(sp)		# rs1
	li	gp, 12
	j	expect_reg
er_rs12:
	sw	a0, 4(sp)		# rs2

	# Third operand: label or immediate
	li	gp, 2
	j	next_token
nt_rs2:
	li	gp, 1
	j	is_tok_numeric
itn_rs1:
	bnez	a0, b_imm

	# Identifier → label reference
	li	gp, 0
	j	lookup_label
ll_rs0:
	bltz	a0, b_forward		# not found → forward ref

	# Backward ref: compute offset
	sub	a3, a0, t1		# t1 = current output offset (set by lookup_label helper)
	j	b_encode

b_forward:
	# Add fixup, emit with imm=0
	li	a1, FMT_B
	li	gp, 0
	j	add_fixup
af_rs0:
	li	a3, 0
	j	b_encode

b_imm:
	li	gp, 2
	j	parse_num
pn_rs2:
	mv	a3, a0			# numeric immediate

b_encode:
	lw	a0, 12(sp)		# template
	lw	a1, 8(sp)		# rs1
	lw	a2, 4(sp)		# rs2
	li	gp, 0
	j	encode_b
enc_b_rs0:
	addi	sp, sp, 20
	j	main_loop

# ─── U-type: rd, imm ─────────────────────────────────────────────────
do_u_type:
	addi	sp, sp, -16
	sw	a4, 8(sp)

	li	gp, 13
	j	expect_reg
er_rs13:
	sw	a0, 4(sp)		# rd
	li	gp, 4
	j	expect_imm
ei_rs4:
	mv	a2, a0			# imm20

	lw	a0, 8(sp)		# template
	lw	a1, 4(sp)		# rd
	li	gp, 0
	j	encode_u
enc_u_rs0:
	addi	sp, sp, 16
	j	main_loop

# ─── J-type: rd, label/imm ───────────────────────────────────────────
do_j_type:
	addi	sp, sp, -16
	sw	a4, 8(sp)

	li	gp, 14
	j	expect_reg
er_rs14:
	sw	a0, 4(sp)		# rd

	# Next operand: label or immediate
	li	gp, 3
	j	next_token
nt_rs3:
	li	gp, 2
	j	is_tok_numeric
itn_rs2:
	bnez	a0, j_imm

	# Identifier → label
	li	gp, 1
	j	lookup_label
ll_rs1:
	bltz	a0, j_forward

	sub	a2, a0, t1		# offset
	j	j_encode

j_forward:
	li	a1, FMT_J
	li	gp, 1
	j	add_fixup
af_rs1:
	li	a2, 0
	j	j_encode

j_imm:
	li	gp, 3
	j	parse_num
pn_rs3:
	mv	a2, a0

j_encode:
	lw	a0, 8(sp)		# template
	lw	a1, 4(sp)		# rd
	li	gp, 0
	j	encode_j
enc_j_rs0:
	addi	sp, sp, 16
	j	main_loop

# ═══════════════════════════════════════════════════════════════════════
#  Pseudo Instructions
# ═══════════════════════════════════════════════════════════════════════
do_pseudo:
	lbu	a3, 14(a5)		# pseudo ID

	li	t0, PS_NOP
	beq	a3, t0, ps_nop
	li	t0, PS_LI
	beq	a3, t0, ps_li
	li	t0, PS_MV
	beq	a3, t0, ps_mv
	li	t0, PS_J
	beq	a3, t0, ps_j
	li	t0, PS_BEQZ
	beq	a3, t0, ps_beqz
	li	t0, PS_BNEZ
	beq	a3, t0, ps_bnez
	j	error_halt

# nop → addi x0, x0, 0
ps_nop:
	li	a0, 0x00000013
	li	gp, 6
	j	emit_word
ew_rs6:
	j	main_loop

# li rd, imm
ps_li:
	addi	sp, sp, -16

	li	gp, 15
	j	expect_reg
er_rs15:
	sw	a0, 8(sp)		# rd
	li	gp, 5
	j	expect_imm
ei_rs5:
	sw	a0, 4(sp)		# imm

	# Check if imm fits in 12-bit signed (-2048..2047)
	lw	t0, 4(sp)
	li	t1, 2047
	bgt	t0, t1, li_two_insn
	li	t1, -2048
	blt	t0, t1, li_two_insn

	# Single addi rd, x0, imm
	li	a0, 0x00000013		# addi template
	lw	a1, 8(sp)		# rd
	li	a2, 0			# rs1 = x0
	lw	a3, 4(sp)		# imm
	li	gp, 4
	j	encode_i
enc_i_rs4:
	j	li_done

li_two_insn:
	# lui rd, upper + addi rd, rd, lower
	lw	t0, 4(sp)		# imm
	li	t1, 0x800
	add	t2, t0, t1		# imm + 0x800
	srai	t2, t2, 12		# upper20

	# lui rd, upper
	li	a0, 0x00000037		# lui template
	lw	a1, 8(sp)		# rd
	mv	a2, t2
	li	gp, 1
	j	encode_u
enc_u_rs1:

	# addi rd, rd, lower
	lw	t0, 4(sp)
	slli	t0, t0, 20
	srai	t0, t0, 20

	li	a0, 0x00000013		# addi template
	lw	a1, 8(sp)		# rd
	lw	a2, 8(sp)		# rs1 = rd
	mv	a3, t0
	li	gp, 5
	j	encode_i
enc_i_rs5:

li_done:
	addi	sp, sp, 16
	j	main_loop

# mv rd, rs → addi rd, rs, 0
ps_mv:
	addi	sp, sp, -8
	li	gp, 16
	j	expect_reg
er_rs16:
	sw	a0, 4(sp)		# rd
	li	gp, 17
	j	expect_reg
er_rs17:
	mv	a2, a0			# rs
	lw	a1, 4(sp)		# rd
	li	a0, 0x00000013		# addi template
	li	a3, 0			# imm = 0
	li	gp, 6
	j	encode_i
enc_i_rs6:
	addi	sp, sp, 8
	j	main_loop

# j label → jal x0, label
ps_j:
	li	gp, 4
	j	next_token
nt_rs4:
	li	gp, 3
	j	is_tok_numeric
itn_rs3:
	bnez	a0, j_ps_imm

	# Label
	li	gp, 2
	j	lookup_label
ll_rs2:
	bltz	a0, j_ps_fwd

	sub	a2, a0, t1
	j	j_ps_enc

j_ps_fwd:
	li	a1, FMT_J
	li	gp, 2
	j	add_fixup
af_rs2:
	li	a2, 0
	j	j_ps_enc

j_ps_imm:
	li	gp, 4
	j	parse_num
pn_rs4:
	mv	a2, a0

j_ps_enc:
	li	a0, 0x0000006F		# jal template
	li	a1, 0			# rd = x0
	li	gp, 1
	j	encode_j
enc_j_rs1:
	j	main_loop

# beqz rs, label → beq rs, x0, label
ps_beqz:
	addi	sp, sp, -8

	li	gp, 18
	j	expect_reg
er_rs18:
	sw	a0, 4(sp)		# rs1

	li	gp, 5
	j	next_token
nt_rs5:
	li	gp, 4
	j	is_tok_numeric
itn_rs4:
	bnez	a0, beqz_imm

	li	gp, 3
	j	lookup_label
ll_rs3:
	bltz	a0, beqz_fwd
	sub	a3, a0, t1
	j	beqz_enc

beqz_fwd:
	li	a1, FMT_B
	li	gp, 3
	j	add_fixup
af_rs3:
	li	a3, 0
	j	beqz_enc

beqz_imm:
	li	gp, 5
	j	parse_num
pn_rs5:
	mv	a3, a0

beqz_enc:
	li	a0, 0x00000063		# beq template
	lw	a1, 4(sp)		# rs1
	li	a2, 0			# rs2 = x0
	li	gp, 1
	j	encode_b
enc_b_rs1:
	addi	sp, sp, 8
	j	main_loop

# bnez rs, label → bne rs, x0, label
ps_bnez:
	addi	sp, sp, -8

	li	gp, 19
	j	expect_reg
er_rs19:
	sw	a0, 4(sp)		# rs1

	li	gp, 6
	j	next_token
nt_rs6:
	li	gp, 5
	j	is_tok_numeric
itn_rs5:
	bnez	a0, bnez_imm

	li	gp, 4
	j	lookup_label
ll_rs4:
	bltz	a0, bnez_fwd
	sub	a3, a0, t1
	j	bnez_enc

bnez_fwd:
	li	a1, FMT_B
	li	gp, 4
	j	add_fixup
af_rs4:
	li	a3, 0
	j	bnez_enc

bnez_imm:
	li	gp, 6
	j	parse_num
pn_rs6:
	mv	a3, a0

bnez_enc:
	li	a0, 0x00001063		# bne template
	lw	a1, 4(sp)		# rs1
	li	a2, 0			# rs2 = x0
	li	gp, 2
	j	encode_b
enc_b_rs2:
	addi	sp, sp, 8
	j	main_loop

# ═══════════════════════════════════════════════════════════════════════
#  Instruction Encoders
# ═══════════════════════════════════════════════════════════════════════

# encode_r: a0=template, a1=rd, a2=rs1, a3=rs2
encode_r:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	slli	t0, a1, 7		# rd
	or	a0, a0, t0
	slli	t0, a2, 15		# rs1
	or	a0, a0, t0
	slli	t0, a3, 20		# rs2
	or	a0, a0, t0
	li	gp, 0
	j	emit_word
ew_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	encode_r_disp

encode_r_disp:
	j	enc_r_rs0

# encode_i: a0=template, a1=rd, a2=rs1, a3=imm12
encode_i:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	slli	t0, a1, 7		# rd
	or	a0, a0, t0
	slli	t0, a2, 15		# rs1
	or	a0, a0, t0
	slli	t0, a3, 20		# imm[11:0]
	or	a0, a0, t0
	li	gp, 1
	j	emit_word
ew_rs1:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	encode_i_disp

encode_i_disp:
	bnez	gp, 1f
	j	enc_i_rs0
1:	addi	gp, gp, -1
	bnez	gp, 2f
	j	enc_i_rs1
2:	addi	gp, gp, -1
	bnez	gp, 3f
	j	error_halt		# enc_i_rs2 was do_jalr_type (removed)
3:	addi	gp, gp, -1
	bnez	gp, 4f
	j	error_halt		# enc_i_rs3 was do_jalr_type (removed)
4:	addi	gp, gp, -1
	bnez	gp, 5f
	j	enc_i_rs4
5:	addi	gp, gp, -1
	bnez	gp, 6f
	j	enc_i_rs5
6:	addi	gp, gp, -1
	bnez	gp, 7f
	j	enc_i_rs6
7:	j	error_halt		# enc_i_rs7 was ps_ret (removed)

# encode_s: a0=template, a1=rs1, a2=rs2, a3=imm12
encode_s:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	slli	t0, a1, 15		# rs1
	or	a0, a0, t0
	slli	t0, a2, 20		# rs2
	or	a0, a0, t0
	# imm[4:0] → bits[11:7]
	andi	t0, a3, 0x1F
	slli	t0, t0, 7
	or	a0, a0, t0
	# imm[11:5] → bits[31:25]
	srai	t0, a3, 5
	andi	t0, t0, 0x7F
	slli	t0, t0, 25
	or	a0, a0, t0
	li	gp, 2
	j	emit_word
ew_rs2:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	encode_s_disp

encode_s_disp:
	j	enc_s_rs0

# encode_b: a0=template, a1=rs1, a2=rs2, a3=imm13
encode_b:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	slli	t0, a1, 15		# rs1
	or	a0, a0, t0
	slli	t0, a2, 20		# rs2
	or	a0, a0, t0

	# imm[12] → bit[31]
	srli	t0, a3, 12
	andi	t0, t0, 1
	slli	t0, t0, 31
	or	a0, a0, t0
	# imm[10:5] → bits[30:25]
	srli	t0, a3, 5
	andi	t0, t0, 0x3F
	slli	t0, t0, 25
	or	a0, a0, t0
	# imm[4:1] → bits[11:8]
	srli	t0, a3, 1
	andi	t0, t0, 0xF
	slli	t0, t0, 8
	or	a0, a0, t0
	# imm[11] → bit[7]
	srli	t0, a3, 11
	andi	t0, t0, 1
	slli	t0, t0, 7
	or	a0, a0, t0

	li	gp, 3
	j	emit_word
ew_rs3:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	encode_b_disp

encode_b_disp:
	bnez	gp, 1f
	j	enc_b_rs0
1:	addi	gp, gp, -1
	bnez	gp, 2f
	j	enc_b_rs1
2:	j	enc_b_rs2

# encode_u: a0=template, a1=rd, a2=imm20
encode_u:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	slli	t0, a1, 7		# rd
	or	a0, a0, t0
	slli	t0, a2, 12		# imm[31:12]
	or	a0, a0, t0
	li	gp, 4
	j	emit_word
ew_rs4:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	encode_u_disp

encode_u_disp:
	bnez	gp, 1f
	j	enc_u_rs0
1:	j	enc_u_rs1

# encode_j: a0=template, a1=rd, a2=imm21
encode_j:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	slli	t0, a1, 7		# rd
	or	a0, a0, t0

	# imm[20] → bit[31]
	srli	t0, a2, 20
	andi	t0, t0, 1
	slli	t0, t0, 31
	or	a0, a0, t0
	# imm[10:1] → bits[30:21]
	srli	t0, a2, 1
	andi	t0, t0, 0x3FF
	slli	t0, t0, 21
	or	a0, a0, t0
	# imm[11] → bit[20]
	srli	t0, a2, 11
	andi	t0, t0, 1
	slli	t0, t0, 20
	or	a0, a0, t0
	# imm[19:12] → bits[19:12]
	srli	t0, a2, 12
	andi	t0, t0, 0xFF
	slli	t0, t0, 12
	or	a0, a0, t0

	li	gp, 5
	j	emit_word
ew_rs5:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	encode_j_disp

encode_j_disp:
	bnez	gp, 1f
	j	enc_j_rs0
1:	j	enc_j_rs1

# emit_word: a0=32-bit word, store at s2, advance s2 (leaf)
emit_word:
	sw	a0, 0(s2)
	addi	s2, s2, 4
	j	emit_word_disp

emit_word_disp:
	bnez	gp, 1f
	j	ew_rs0
1:	addi	gp, gp, -1
	bnez	gp, 2f
	j	ew_rs1
2:	addi	gp, gp, -1
	bnez	gp, 3f
	j	ew_rs2
3:	addi	gp, gp, -1
	bnez	gp, 4f
	j	ew_rs3
4:	addi	gp, gp, -1
	bnez	gp, 5f
	j	ew_rs4
5:	addi	gp, gp, -1
	bnez	gp, 6f
	j	ew_rs5
6:	j	ew_rs6

# ═══════════════════════════════════════════════════════════════════════
#  Tokenizer
# ═══════════════════════════════════════════════════════════════════════

# read_char: returns char in a0. Uses putback slot at s10-4. (leaf)
read_char:
	lw	a0, -4(s10)		# check putback
	beqz	a0, rc_poll
	sw	zero, -4(s10)		# clear putback
	j	read_char_disp
rc_poll:
	lbu	a0, 5(s5)		# UART LSR
	andi	a0, a0, 1
	beqz	a0, rc_poll
	lbu	a0, 0(s5)		# read char
	j	read_char_disp

read_char_disp:
	bnez	gp, 1f
	j	rc_rs0
1:	addi	gp, gp, -1
	bnez	gp, 2f
	j	rc_rs1
2:	j	rc_rs2

# putback_char: store a0 into putback slot (leaf)
putback_char:
	sw	a0, -4(s10)
	j	putback_char_disp

putback_char_disp:
	j	pb_rs0

# next_token:
#   returns: a0 = token type
#   token text in buffer at s10, length in s0
next_token:
	addi	sp, sp, -4
	sw	gp, 0(sp)

nt_skip:
	li	gp, 0
	j	read_char
rc_rs0:

	# Whitespace: space, tab, CR, comma → skip
	li	t0, ' '
	beq	a0, t0, nt_skip
	li	t0, '\t'
	beq	a0, t0, nt_skip
	li	t0, 13			# CR
	beq	a0, t0, nt_skip
	li	t0, ','
	beq	a0, t0, nt_skip

	# Newline → EOL
	li	t0, '\n'
	beq	a0, t0, nt_eol

	# Comment
	li	t0, '#'
	beq	a0, t0, nt_comment

	# EOT
	li	t0, 4
	beq	a0, t0, nt_eot

	# Open/close paren
	li	t0, '('
	beq	a0, t0, nt_lparen
	li	t0, ')'
	beq	a0, t0, nt_rparen

	# Everything else (digits, letters, '-', '_') → identifier
	j	nt_ident

nt_eol:
	li	a0, TOK_EOL
	j	nt_ret

nt_comment:
	# Skip to end of line
	li	gp, 1
	j	read_char
rc_rs1:
	li	t0, '\n'
	bne	a0, t0, nt_comment
	li	a0, TOK_EOL
	j	nt_ret

nt_eot:
	li	a0, TOK_EOT
	j	nt_ret

nt_lparen:
	li	a0, TOK_LPAREN
	j	nt_ret

nt_rparen:
	li	a0, TOK_RPAREN
	j	nt_ret

# ─── Identifier parsing ──────────────────────────────────────────────
nt_ident:
	# a0 has first char
	# Zero token buffer (8 words = 32 bytes, enough for lookup)
	sw	zero, 0(s10)
	sw	zero, 4(s10)
	sw	zero, 8(s10)
	sw	zero, 12(s10)
	sw	zero, 16(s10)
	sw	zero, 20(s10)
	sw	zero, 24(s10)
	sw	zero, 28(s10)

	li	s0, 0			# length
nt_id_loop:
	# Store char if room
	li	t0, 31
	bge	s0, t0, nt_id_skip	# truncate at 31
	add	t0, s10, s0
	sb	a0, 0(t0)
	addi	s0, s0, 1
nt_id_skip:
	li	gp, 2
	j	read_char
rc_rs2:

	# Check if char continues identifier: [A-Za-z0-9_.\-]
	li	t0, '-'
	beq	a0, t0, nt_id_loop
	li	t0, '_'
	beq	a0, t0, nt_id_loop
	li	t0, '.'
	beq	a0, t0, nt_id_loop
	li	t0, '0'
	blt	a0, t0, nt_id_end
	li	t0, '9'
	ble	a0, t0, nt_id_loop
	li	t0, 'A'
	blt	a0, t0, nt_id_end
	li	t0, 'Z'
	ble	a0, t0, nt_id_loop
	li	t0, 'a'
	blt	a0, t0, nt_id_end
	li	t0, 'z'
	ble	a0, t0, nt_id_loop

nt_id_end:
	# a0 has the char after the identifier
	# Check for ':' → label definition
	li	t0, ':'
	beq	a0, t0, nt_label_def

	# Put back the lookahead char
	li	gp, 0
	j	putback_char
pb_rs0:
	li	a0, TOK_IDENT
	j	nt_ret

nt_label_def:
	li	a0, TOK_LABEL
	j	nt_ret

nt_ret:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	next_token_disp

next_token_disp:
	bnez	gp, 1f
	j	nt_rs0
1:	addi	gp, gp, -1
	bnez	gp, 2f
	j	error_halt		# nt_rs1 was do_jalr_type (removed)
2:	addi	gp, gp, -1
	bnez	gp, 3f
	j	nt_rs2
3:	addi	gp, gp, -1
	bnez	gp, 4f
	j	nt_rs3
4:	addi	gp, gp, -1
	bnez	gp, 5f
	j	nt_rs4
5:	addi	gp, gp, -1
	bnez	gp, 6f
	j	nt_rs5
6:	addi	gp, gp, -1
	bnez	gp, 7f
	j	nt_rs6
7:	addi	gp, gp, -1
	bnez	gp, 8f
	j	nt_rs7
8:	addi	gp, gp, -1
	bnez	gp, 9f
	j	nt_rs8
9:	addi	gp, gp, -1
	bnez	gp, 10f
	j	nt_rs9
10:	j	nt_rs10

# ═══════════════════════════════════════════════════════════════════════
#  Helper Functions
# ═══════════════════════════════════════════════════════════════════════

# is_tok_numeric: check if token buffer starts with digit or '-'
#   returns a0=1 if numeric, 0 if not (leaf)
is_tok_numeric:
	lbu	t0, 0(s10)
	li	t1, '-'
	beq	t0, t1, itn_yes
	li	t1, '0'
	blt	t0, t1, itn_no
	li	t1, '9'
	ble	t0, t1, itn_yes
itn_no:
	li	a0, 0
	j	is_tok_numeric_disp
itn_yes:
	li	a0, 1
	j	is_tok_numeric_disp

is_tok_numeric_disp:
	bnez	gp, 1f
	j	error_halt		# itn_rs0 was do_jalr_type (removed)
1:	addi	gp, gp, -1
	bnez	gp, 2f
	j	itn_rs1
2:	addi	gp, gp, -1
	bnez	gp, 3f
	j	itn_rs2
3:	addi	gp, gp, -1
	bnez	gp, 4f
	j	itn_rs3
4:	addi	gp, gp, -1
	bnez	gp, 5f
	j	itn_rs4
5:	j	itn_rs5

# is_upper_hex: t0=char, returns a0=1 if [0-9A-F], else 0 (leaf)
is_upper_hex:
	li	a0, 1
	li	t1, '0'
	blt	t0, t1, iuh_no
	li	t1, '9'
	ble	t0, t1, iuh_yes
	li	t1, 'A'
	blt	t0, t1, iuh_no
	li	t1, 'F'
	ble	t0, t1, iuh_yes
iuh_no:
	li	a0, 0
iuh_yes:
	j	is_upper_hex_disp

is_upper_hex_disp:
	bnez	gp, 1f
	j	iuh_rs0
1:	j	iuh_rs1

# hex_val: t0=hex char [0-9A-F], returns a0=value 0-15 (leaf)
#   Note: must not clobber t1 (caller may use it)
hex_val:
	addi	a0, t0, -'0'
	li	t2, 10
	blt	a0, t2, hv_done
	addi	a0, a0, -7		# 'A'-'0' = 17, -7 = 10
hv_done:
	j	hex_val_disp

hex_val_disp:
	bnez	gp, 1f
	j	hv_rs0
1:	j	hv_rs1

# expect_reg: read next token, parse as register, return reg num in a0
expect_reg:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 7
	j	next_token
nt_rs7:
	li	gp, 0
	j	parse_reg
pr_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	expect_reg_disp

expect_reg_disp:
	bnez	gp, 1f
	j	er_rs0
1:	addi	gp, gp, -1
	bnez	gp, 2f
	j	er_rs1
2:	addi	gp, gp, -1
	bnez	gp, 3f
	j	er_rs2
3:	addi	gp, gp, -1
	bnez	gp, 4f
	j	er_rs3
4:	addi	gp, gp, -1
	bnez	gp, 5f
	j	er_rs4
5:	addi	gp, gp, -1
	bnez	gp, 6f
	j	er_rs5
6:	addi	gp, gp, -1
	bnez	gp, 7f
	j	er_rs6
7:	addi	gp, gp, -1
	bnez	gp, 8f
	j	error_halt		# er_rs7 was do_jalr_type (removed)
8:	addi	gp, gp, -1
	bnez	gp, 9f
	j	error_halt		# er_rs8 was do_jalr_type (removed)
9:	addi	gp, gp, -1
	bnez	gp, 10f
	j	er_rs9
10:	addi	gp, gp, -1
	bnez	gp, 11f
	j	er_rs10
11:	addi	gp, gp, -1
	bnez	gp, 12f
	j	er_rs11
12:	addi	gp, gp, -1
	bnez	gp, 13f
	j	er_rs12
13:	addi	gp, gp, -1
	bnez	gp, 14f
	j	er_rs13
14:	addi	gp, gp, -1
	bnez	gp, 15f
	j	er_rs14
15:	addi	gp, gp, -1
	bnez	gp, 16f
	j	er_rs15
16:	addi	gp, gp, -1
	bnez	gp, 17f
	j	er_rs16
17:	addi	gp, gp, -1
	bnez	gp, 18f
	j	er_rs17
18:	addi	gp, gp, -1
	bnez	gp, 19f
	j	er_rs18
19:	j	er_rs19

# expect_imm: read next token, parse as number, return value in a0
expect_imm:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 8
	j	next_token
nt_rs8:
	li	gp, 0
	j	parse_num
pn_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	expect_imm_disp

expect_imm_disp:
	bnez	gp, 1f
	j	ei_rs0
1:	addi	gp, gp, -1
	bnez	gp, 2f
	j	ei_rs1
2:	addi	gp, gp, -1
	bnez	gp, 3f
	j	error_halt		# ei_rs2 was do_jalr_type (removed)
3:	addi	gp, gp, -1
	bnez	gp, 4f
	j	ei_rs3
4:	addi	gp, gp, -1
	bnez	gp, 5f
	j	ei_rs4
5:	j	ei_rs5

# parse_num: parse token buffer at s10 (length s0) as number, return in a0 (leaf)
#   handles: decimal (42), hex (0xFF), negative (-42, -0xFF)
parse_num:
	li	a0, 0			# accumulator
	mv	t2, s10			# read ptr
	add	t3, s10, s0		# end ptr
	li	t6, 0			# negative flag

	beq	t2, t3, pn_done		# empty → 0

	# Check for '-' prefix
	lbu	t0, 0(t2)
	li	t1, '-'
	bne	t0, t1, pn_check_hex
	li	t6, 1			# negative
	addi	t2, t2, 1
	beq	t2, t3, pn_done

pn_check_hex:
	# Check for 0x prefix
	lbu	t0, 0(t2)
	li	t1, '0'
	bne	t0, t1, pn_dec_loop

	# Could be 0x
	addi	t4, t2, 1
	beq	t4, t3, pn_dec_loop	# just "0"
	lbu	t0, 0(t4)
	li	t1, 'x'
	beq	t0, t1, pn_hex_start
	li	t1, 'X'
	beq	t0, t1, pn_hex_start
	j	pn_dec_loop

pn_hex_start:
	addi	t2, t4, 1		# skip "0x"
pn_hex_loop:
	beq	t2, t3, pn_negate
	lbu	t0, 0(t2)
	addi	t2, t2, 1

	# 0-9
	li	t1, '0'
	blt	t0, t1, pn_negate
	li	t1, '9'
	ble	t0, t1, pn_hex09
	# A-F
	li	t1, 'A'
	blt	t0, t1, pn_negate
	li	t1, 'F'
	ble	t0, t1, pn_hexAF
	# a-f
	li	t1, 'a'
	blt	t0, t1, pn_negate
	li	t1, 'f'
	ble	t0, t1, pn_hexaf
	j	pn_negate

pn_hex09:
	addi	t0, t0, -'0'
	j	pn_hex_acc
pn_hexAF:
	addi	t0, t0, -'A'
	addi	t0, t0, 10
	j	pn_hex_acc
pn_hexaf:
	addi	t0, t0, -'a'
	addi	t0, t0, 10
pn_hex_acc:
	slli	a0, a0, 4
	or	a0, a0, t0
	j	pn_hex_loop

pn_dec_loop:
	beq	t2, t3, pn_negate
	lbu	t0, 0(t2)
	addi	t2, t2, 1
	li	t1, '0'
	blt	t0, t1, pn_negate
	li	t1, '9'
	bgt	t0, t1, pn_negate
	addi	t0, t0, -'0'
	# a0 = a0 * 10 + t0
	slli	t1, a0, 3
	slli	a0, a0, 1
	add	a0, a0, t1
	add	a0, a0, t0
	j	pn_dec_loop

pn_negate:
	beqz	t6, pn_done
	sub	a0, zero, a0
pn_done:
	j	parse_num_disp

parse_num_disp:
	bnez	gp, 1f
	j	pn_rs0
1:	addi	gp, gp, -1
	bnez	gp, 2f
	j	error_halt		# pn_rs1 was do_jalr_type (removed)
2:	addi	gp, gp, -1
	bnez	gp, 3f
	j	pn_rs2
3:	addi	gp, gp, -1
	bnez	gp, 4f
	j	pn_rs3
4:	addi	gp, gp, -1
	bnez	gp, 5f
	j	pn_rs4
5:	addi	gp, gp, -1
	bnez	gp, 6f
	j	pn_rs5
6:	j	pn_rs6

# expect_lparen: read next token, assert '('
expect_lparen:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 9
	j	next_token
nt_rs9:
	# We trust the input; no error check
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	expect_lparen_disp

expect_lparen_disp:
	bnez	gp, 1f
	j	elp_rs0
1:	addi	gp, gp, -1
	bnez	gp, 2f
	j	error_halt		# elp_rs1 was do_jalr_type (removed)
2:	j	elp_rs2

# expect_rparen: read next token, assert ')'
expect_rparen:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 10
	j	next_token
nt_rs10:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	expect_rparen_disp

expect_rparen_disp:
	bnez	gp, 1f
	j	erp_rs0
1:	addi	gp, gp, -1
	bnez	gp, 2f
	j	error_halt		# erp_rs1 was do_jalr_type (removed)
2:	j	erp_rs2

# ═══════════════════════════════════════════════════════════════════════
#  Register Parser
# ═══════════════════════════════════════════════════════════════════════

# parse_reg: token in buffer at s10, length in s0 (leaf)
#   returns register number in a0, or -1 if not a register
parse_reg:
	# Check for 'x' prefix (x0-x31)
	lbu	t0, 0(s10)
	li	t1, 'x'
	bne	t0, t1, pr_abi

	# Parse number after 'x'
	li	a0, 0			# accumulator
	li	t2, 1			# index
pr_xloop:
	bge	t2, s0, pr_xdone
	add	t0, s10, t2
	lbu	t0, 0(t0)
	addi	t0, t0, -'0'
	bltz	t0, pr_fail
	li	t1, 9
	bgt	t0, t1, pr_fail
	# a0 = a0 * 10 + t0
	slli	t1, a0, 3
	slli	a0, a0, 1
	add	a0, a0, t1
	add	a0, a0, t0
	addi	t2, t2, 1
	j	pr_xloop

pr_xdone:
	li	t0, 31
	bgt	a0, t0, pr_fail
	j	pr_ret

pr_abi:
	# Linear scan of register table
	mv	t2, s11			# table ptr
pr_scan:
	lbu	t0, 0(t2)		# first byte of entry name
	beqz	t0, pr_fail		# end of table (null sentinel)

	# Compare name: entries are 8 bytes (5-byte name + 1 reg + 2 pad)
	mv	t3, t2			# entry name ptr
	mv	t4, s10			# token ptr
	li	t5, 0			# match len
pr_cmp:
	lbu	t0, 0(t3)
	lbu	t1, 0(t4)
	beqz	t0, pr_cmp_end		# end of entry name
	bne	t0, t1, pr_next
	addi	t3, t3, 1
	addi	t4, t4, 1
	addi	t5, t5, 1
	j	pr_cmp

pr_cmp_end:
	# Entry name ended. Check token also ended (t5 == s0)
	bne	t5, s0, pr_next
	# Match!
	lbu	a0, 5(t2)		# register number at offset 5
	j	pr_ret

pr_next:
	addi	t2, t2, 8
	j	pr_scan

pr_fail:
	li	a0, -1

pr_ret:
	j	parse_reg_disp

parse_reg_disp:
	bnez	gp, 1f
	j	pr_rs0
1:	j	error_halt		# pr_rs1 was do_jalr_type (removed)

# ═══════════════════════════════════════════════════════════════════════
#  Mnemonic Lookup
# ═══════════════════════════════════════════════════════════════════════

# lookup_mnem: token in buffer at s10, length in s0 (leaf)
#   returns pointer to 16-byte entry in a0, or 0 if not found
lookup_mnem:
	mv	t2, s9			# table ptr

lm_loop:
	lbu	t0, 0(t2)		# first byte
	beqz	t0, lm_fail		# null sentinel = end of table

	# Compare 8-byte name (token buf is zero-padded to 32 bytes)
	lw	t0, 0(t2)		# first 4 bytes of entry
	lw	t1, 0(s10)		# first 4 bytes of token
	bne	t0, t1, lm_next
	lw	t0, 4(t2)		# next 4 bytes
	lw	t1, 4(s10)
	bne	t0, t1, lm_next

	# Match
	mv	a0, t2
	j	lookup_mnem_disp

lm_next:
	addi	t2, t2, 16
	j	lm_loop

lm_fail:
	li	a0, 0
	j	lookup_mnem_disp

lookup_mnem_disp:
	j	lm_rs0

# ═══════════════════════════════════════════════════════════════════════
#  Label / Fixup / Resolve
# ═══════════════════════════════════════════════════════════════════════

# lookup_label: token in buffer at s10, s0=length (leaf)
#   returns offset in a0 (>=0) if found, -1 if not found
#   also sets t1 = current output offset (for computing branch displacement)
lookup_label:
	sub	t1, s2, s1		# current output offset
	mv	t2, s3			# symtab scan ptr

ll_loop:
	beq	t2, s4, ll_fail		# end of symtab

	# Compare 32-byte name using 8 word compares
	lw	t3, 0(t2)
	lw	t4, 0(s10)
	bne	t3, t4, ll_next
	lw	t3, 4(t2)
	lw	t4, 4(s10)
	bne	t3, t4, ll_next
	lw	t3, 8(t2)
	lw	t4, 8(s10)
	bne	t3, t4, ll_next
	lw	t3, 12(t2)
	lw	t4, 12(s10)
	bne	t3, t4, ll_next
	lw	t3, 16(t2)
	lw	t4, 16(s10)
	bne	t3, t4, ll_next
	lw	t3, 20(t2)
	lw	t4, 20(s10)
	bne	t3, t4, ll_next
	lw	t3, 24(t2)
	lw	t4, 24(s10)
	bne	t3, t4, ll_next
	lw	t3, 28(t2)
	lw	t4, 28(s10)
	bne	t3, t4, ll_next

	# Match — load offset
	lw	a0, 32(t2)
	j	lookup_label_disp

ll_next:
	addi	t2, t2, 40
	j	ll_loop

ll_fail:
	li	a0, -1
	j	lookup_label_disp

lookup_label_disp:
	bnez	gp, 1f
	j	ll_rs0
1:	addi	gp, gp, -1
	bnez	gp, 2f
	j	ll_rs1
2:	addi	gp, gp, -1
	bnez	gp, 3f
	j	ll_rs2
3:	addi	gp, gp, -1
	bnez	gp, 4f
	j	ll_rs3
4:	j	ll_rs4

# add_fixup: token (label name) in buffer at s10, a1=fixup type (leaf)
#   records fixup for the instruction at s2-4
add_fixup:
	# Zero 40 bytes at s8
	mv	t0, s8
	addi	t2, s8, 40
af_zero:
	sw	zero, 0(t0)
	addi	t0, t0, 4
	bne	t0, t2, af_zero

	# Copy token buffer (32 bytes, already zero-padded)
	mv	t0, s8
	mv	t2, s10
	addi	t3, s10, 32
af_copy:
	lw	t4, 0(t2)
	sw	t4, 0(t0)
	addi	t0, t0, 4
	addi	t2, t2, 4
	bne	t2, t3, af_copy

	# Store instruction address (output offset where it WILL be emitted)
	sub	t0, s2, s1
	sw	t0, 32(s8)

	# Store fixup type
	sb	a1, 36(s8)

	addi	s8, s8, 40
	j	add_fixup_disp

add_fixup_disp:
	bnez	gp, 1f
	j	af_rs0
1:	addi	gp, gp, -1
	bnez	gp, 2f
	j	af_rs1
2:	addi	gp, gp, -1
	bnez	gp, 3f
	j	af_rs2
3:	addi	gp, gp, -1
	bnez	gp, 4f
	j	af_rs3
4:	j	af_rs4

# ─── Resolve all fixups ──────────────────────────────────────────────
resolve:
	mv	t6, s7			# fixup table iterator

res_loop:
	beq	t6, s8, output		# done → output

	# Load fixup type
	lbu	a3, 36(t6)		# B or J

	# Load instruction offset
	lw	a4, 32(t6)		# offset in output buffer

	# Search symtab for matching name
	mv	t2, s3
res_search:
	beq	t2, s4, res_next	# not found → skip

	# Compare 32-byte names (8 word compares)
	lw	t3, 0(t6)
	lw	t4, 0(t2)
	bne	t3, t4, res_snext
	lw	t3, 4(t6)
	lw	t4, 4(t2)
	bne	t3, t4, res_snext
	lw	t3, 8(t6)
	lw	t4, 8(t2)
	bne	t3, t4, res_snext
	lw	t3, 12(t6)
	lw	t4, 12(t2)
	bne	t3, t4, res_snext
	lw	t3, 16(t6)
	lw	t4, 16(t2)
	bne	t3, t4, res_snext
	lw	t3, 20(t6)
	lw	t4, 20(t2)
	bne	t3, t4, res_snext
	lw	t3, 24(t6)
	lw	t4, 24(t2)
	bne	t3, t4, res_snext
	lw	t3, 28(t6)
	lw	t4, 28(t2)
	bne	t3, t4, res_snext

	# Match — compute offset
	lw	t0, 32(t2)		# label offset
	sub	t0, t0, a4		# displacement = label - instruction

	# Load instruction from output buffer
	add	t3, s1, a4		# absolute address in buffer
	lw	t4, 0(t3)		# instruction word

	# Dispatch on fixup type
	li	t5, FMT_B
	beq	a3, t5, res_patch_b
	li	t5, FMT_J
	beq	a3, t5, res_patch_j
	j	res_next

res_patch_b:
	# t0 = offset, t4 = instruction
	# Scatter B-type immediate bits
	li	t5, 0

	srli	a0, t0, 12		# imm[12] → bit[31]
	andi	a0, a0, 1
	slli	a0, a0, 31
	or	t5, t5, a0

	srli	a0, t0, 5		# imm[10:5] → bits[30:25]
	andi	a0, a0, 0x3F
	slli	a0, a0, 25
	or	t5, t5, a0

	srli	a0, t0, 1		# imm[4:1] → bits[11:8]
	andi	a0, a0, 0xF
	slli	a0, a0, 8
	or	t5, t5, a0

	srli	a0, t0, 11		# imm[11] → bit[7]
	andi	a0, a0, 1
	slli	a0, a0, 7
	or	t5, t5, a0

	or	t4, t4, t5
	sw	t4, 0(t3)
	j	res_next

res_patch_j:
	# t0 = offset, t4 = instruction
	li	t5, 0

	srli	a0, t0, 20		# imm[20] → bit[31]
	andi	a0, a0, 1
	slli	a0, a0, 31
	or	t5, t5, a0

	srli	a0, t0, 1		# imm[10:1] → bits[30:21]
	andi	a0, a0, 0x3FF
	slli	a0, a0, 21
	or	t5, t5, a0

	srli	a0, t0, 11		# imm[11] → bit[20]
	andi	a0, a0, 1
	slli	a0, a0, 20
	or	t5, t5, a0

	srli	a0, t0, 12		# imm[19:12] → bits[19:12]
	andi	a0, a0, 0xFF
	slli	a0, a0, 12
	or	t5, t5, a0

	or	t4, t4, t5
	sw	t4, 0(t3)
	j	res_next

res_snext:
	addi	t2, t2, 40
	j	res_search

res_next:
	addi	t6, t6, 40
	j	res_loop

# ═══════════════════════════════════════════════════════════════════════
#  Output
# ═══════════════════════════════════════════════════════════════════════
output:
	# Emit q32 magic nop (0x13, 0x00, 0x00, 0x00) before output
	li	a0, 0x00000013
	sb	a0, 0(s2)		# borrow s2 as scratch (output done)
	srli	a0, a0, 8
	sb	a0, 1(s2)
	srli	a0, a0, 8
	sb	a0, 2(s2)
	srli	a0, a0, 8
	sb	a0, 3(s2)
	# Send magic 4 bytes from s2
	mv	t3, s2
	addi	a0, s2, 4
tx_magic:
	beq	t3, a0, output_lp
	lbu	t4, 0(t3)
	addi	t3, t3, 1
tx_magic_poll:
	lbu	t0, 5(s5)
	andi	t0, t0, 0x20
	beqz	t0, tx_magic_poll
	sb	t4, 0(s5)
	j	tx_magic

	# Normal output loop
output_lp:
	beq	s1, s2, shutdown
	lbu	t3, 0(s1)
	addi	s1, s1, 1
tx_poll:
	lbu	t0, 5(s5)
	andi	t0, t0, 0x20
	beqz	t0, tx_poll
	sb	t3, 0(s5)
	j	output_lp

# ═══════════════════════════════════════════════════════════════════════
#  Shutdown
# ═══════════════════════════════════════════════════════════════════════
shutdown:
	lui	s5, 0x100
	lui	t0, 0x5
	addi	t0, t0, 0x555
	sw	t0, 0(s5)

# ═══════════════════════════════════════════════════════════════════════
#  Error halt — infinite loop
# ═══════════════════════════════════════════════════════════════════════
error_halt:
	j	error_halt

# ═══════════════════════════════════════════════════════════════════════
#  DATA TABLES
# ═══════════════════════════════════════════════════════════════════════

.balign 4

# ─── Mnemonic Table ───────────────────────────────────────────────────
# 16 bytes per entry: 8-byte name (null-padded) + 4-byte template + format + flags + pseudo_id + pad
mnem_table:
# R-type (format 0)
.ascii "add\0\0\0\0\0"
.word 0x00000033
.byte FMT_R, 0, 0, 0

.ascii "sub\0\0\0\0\0"
.word 0x40000033
.byte FMT_R, 0, 0, 0

.ascii "and\0\0\0\0\0"
.word 0x00007033
.byte FMT_R, 0, 0, 0

.ascii "or\0\0\0\0\0\0"
.word 0x00006033
.byte FMT_R, 0, 0, 0

.ascii "xor\0\0\0\0\0"
.word 0x00004033
.byte FMT_R, 0, 0, 0

.ascii "sll\0\0\0\0\0"
.word 0x00001033
.byte FMT_R, 0, 0, 0

.ascii "srl\0\0\0\0\0"
.word 0x00005033
.byte FMT_R, 0, 0, 0

.ascii "sra\0\0\0\0\0"
.word 0x40005033
.byte FMT_R, 0, 0, 0

.ascii "slt\0\0\0\0\0"
.word 0x00002033
.byte FMT_R, 0, 0, 0

.ascii "sltu\0\0\0\0"
.word 0x00003033
.byte FMT_R, 0, 0, 0

# I-type arithmetic (format 1): rd, rs1, imm
.ascii "addi\0\0\0\0"
.word 0x00000013
.byte FMT_I, 0, 0, 0

.ascii "andi\0\0\0\0"
.word 0x00007013
.byte FMT_I, 0, 0, 0

.ascii "ori\0\0\0\0\0"
.word 0x00006013
.byte FMT_I, 0, 0, 0

.ascii "xori\0\0\0\0"
.word 0x00004013
.byte FMT_I, 0, 0, 0

.ascii "slti\0\0\0\0"
.word 0x00002013
.byte FMT_I, 0, 0, 0

.ascii "sltiu\0\0\0"
.word 0x00003013
.byte FMT_I, 0, 0, 0

.ascii "slli\0\0\0\0"
.word 0x00001013
.byte FMT_I, 0, 0, 0

.ascii "srli\0\0\0\0"
.word 0x00005013
.byte FMT_I, 0, 0, 0

.ascii "srai\0\0\0\0"
.word 0x40005013
.byte FMT_I, 0, 0, 0

# Loads (format 7 = load): rd, imm(rs1)
.ascii "lb\0\0\0\0\0\0"
.word 0x00000003
.byte FMT_LOAD, 0, 0, 0

.ascii "lh\0\0\0\0\0\0"
.word 0x00001003
.byte FMT_LOAD, 0, 0, 0

.ascii "lw\0\0\0\0\0\0"
.word 0x00002003
.byte FMT_LOAD, 0, 0, 0

.ascii "lbu\0\0\0\0\0"
.word 0x00004003
.byte FMT_LOAD, 0, 0, 0

.ascii "lhu\0\0\0\0\0"
.word 0x00005003
.byte FMT_LOAD, 0, 0, 0

# Stores (format 2): rs2, imm(rs1)
.ascii "sb\0\0\0\0\0\0"
.word 0x00000023
.byte FMT_S, 0, 0, 0

.ascii "sh\0\0\0\0\0\0"
.word 0x00001023
.byte FMT_S, 0, 0, 0

.ascii "sw\0\0\0\0\0\0"
.word 0x00002023
.byte FMT_S, 0, 0, 0

# Branches (format 3): rs1, rs2, label
.ascii "beq\0\0\0\0\0"
.word 0x00000063
.byte FMT_B, 0, 0, 0

.ascii "bne\0\0\0\0\0"
.word 0x00001063
.byte FMT_B, 0, 0, 0

.ascii "blt\0\0\0\0\0"
.word 0x00004063
.byte FMT_B, 0, 0, 0

.ascii "bge\0\0\0\0\0"
.word 0x00005063
.byte FMT_B, 0, 0, 0

.ascii "bltu\0\0\0\0"
.word 0x00006063
.byte FMT_B, 0, 0, 0

.ascii "bgeu\0\0\0\0"
.word 0x00007063
.byte FMT_B, 0, 0, 0

# U-type (format 4): rd, imm
.ascii "lui\0\0\0\0\0"
.word 0x00000037
.byte FMT_U, 0, 0, 0

.ascii "auipc\0\0\0"
.word 0x00000017
.byte FMT_U, 0, 0, 0

# J-type (format 5): rd, label
.ascii "jal\0\0\0\0\0"
.word 0x0000006F
.byte FMT_J, 0, 0, 0

# Pseudos (format 6)
.ascii "nop\0\0\0\0\0"
.word 0x00000000
.byte FMT_PSEUDO, 0, PS_NOP, 0

.ascii "li\0\0\0\0\0\0"
.word 0x00000000
.byte FMT_PSEUDO, 0, PS_LI, 0

.ascii "mv\0\0\0\0\0\0"
.word 0x00000000
.byte FMT_PSEUDO, 0, PS_MV, 0

.ascii "j\0\0\0\0\0\0\0"
.word 0x00000000
.byte FMT_PSEUDO, 0, PS_J, 0

.ascii "beqz\0\0\0\0"
.word 0x00000000
.byte FMT_PSEUDO, 0, PS_BEQZ, 0

.ascii "bnez\0\0\0\0"
.word 0x00000000
.byte FMT_PSEUDO, 0, PS_BNEZ, 0

# Sentinel (end of table)
.word 0, 0, 0, 0

# ─── Register Table ───────────────────────────────────────────────────
# 8 bytes per entry: up to 5 chars name (null-terminated) + reg number at byte 5 + 2 pad
reg_table:
.ascii "zero\0"
.byte 0, 0, 0

.ascii "ra\0\0\0"
.byte 1, 0, 0

.ascii "sp\0\0\0"
.byte 2, 0, 0

.ascii "gp\0\0\0"
.byte 3, 0, 0

.ascii "tp\0\0\0"
.byte 4, 0, 0

.ascii "t0\0\0\0"
.byte 5, 0, 0

.ascii "t1\0\0\0"
.byte 6, 0, 0

.ascii "t2\0\0\0"
.byte 7, 0, 0

.ascii "s0\0\0\0"
.byte 8, 0, 0

.ascii "fp\0\0\0"
.byte 8, 0, 0

.ascii "s1\0\0\0"
.byte 9, 0, 0

.ascii "a0\0\0\0"
.byte 10, 0, 0

.ascii "a1\0\0\0"
.byte 11, 0, 0

.ascii "a2\0\0\0"
.byte 12, 0, 0

.ascii "a3\0\0\0"
.byte 13, 0, 0

.ascii "a4\0\0\0"
.byte 14, 0, 0

.ascii "a5\0\0\0"
.byte 15, 0, 0

.ascii "a6\0\0\0"
.byte 16, 0, 0

.ascii "a7\0\0\0"
.byte 17, 0, 0

.ascii "s2\0\0\0"
.byte 18, 0, 0

.ascii "s3\0\0\0"
.byte 19, 0, 0

.ascii "s4\0\0\0"
.byte 20, 0, 0

.ascii "s5\0\0\0"
.byte 21, 0, 0

.ascii "s6\0\0\0"
.byte 22, 0, 0

.ascii "s7\0\0\0"
.byte 23, 0, 0

.ascii "s8\0\0\0"
.byte 24, 0, 0

.ascii "s9\0\0\0"
.byte 25, 0, 0

.ascii "s10\0\0"
.byte 26, 0, 0

.ascii "s11\0\0"
.byte 27, 0, 0

.ascii "t3\0\0\0"
.byte 28, 0, 0

.ascii "t4\0\0\0"
.byte 29, 0, 0

.ascii "t5\0\0\0"
.byte 30, 0, 0

.ascii "t6\0\0\0"
.byte 31, 0, 0

# Sentinel
.byte 0, 0, 0, 0, 0, 0, 0, 0
