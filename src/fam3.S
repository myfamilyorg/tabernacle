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

# ══════════════════════════════════════════════════════════════════════════════
# fam3.S — RV32I mnemonic assembler (fourth-stage bootstrap)
# ══════════════════════════════════════════════════════════════════════════════
#
# Reads text from UART (terminated by EOT = 0x04), emits a RISC-V binary
# back over UART, then poweroffs.
#
# Grammar:
#   # ... \n                    comment (to end of line)
#   whitespace / comma          token separators (interchangeable)
#   name:                       label definition (name <= 31 chars)
#   N:                          local label (digit 0-9)
#   mnemonic operands           RV32I instruction or pseudo
#
# Supported mnemonics (RV32I base, minus jalr/jr — static jumps only):
#   R: add sub sll slt sltu xor srl sra or and
#   I: addi slti sltiu xori ori andi slli srli srai
#   Load: lb lh lw lbu lhu
#   Store: sb sh sw
#   Branch: beq bne blt bge bltu bgeu
#   U: lui auipc
#   Jump: jal
#
# Pseudos:
#   nop li mv j beqz bnez neg not
#   seqz snez sltz sgtz bltz bgez blez
#   bgt ble bgtu bleu
#   lla wfi
#   prologue epilogue
#
# Removed from fam2-series: ret, jr, jalr, call, tail, return (all indirect-jump-based)
#
# Directives:
#   .equ NAME, value
#   .byte val[, val...]
#   .word val[, val...]
#   .ascii "string"
#   .zero count
#
# Branch relaxation: B-type label targets always emit an inverted-branch +8
# then JAL trampoline (8 bytes total), converting fixup to J-type (±1 MB).
# Numeric B-type offsets remain compact (4 bytes, ±4 KB).
#
# Register map:
#   s0  = token length          s1  = output buf base
#   s2  = output write ptr      s3  = symtab base
#   s4  = symtab write ptr      s5  = UART base (0x10000000)
#   s6  = 10 (constant)         s7  = fixup base
#   s8  = fixup write ptr       s9  = mnem_table base
#   s10 = token buf base        s11 = reg_table base
#   sp  = descending stack
#
# Memory layout (auipc-relative):
#   +0x10000   output buffer (512 KB)
#   +0x90000   symtab (40-byte entries: 32B name + 4B value + 4B kind)
#   +0xD0000   fixup table (40-byte entries: 32B name + 4B offset + 4B type)
#   +0x110000  token buffer (64 KB scratch)
#   +0x120000  stack top
#
# Token buffer layout (at s10):
#   0..255    token text (zero-padded, max 255 chars)
#   256       sticky EOT flag
#   288..327  local label counters (10 words, digits 0-9)
#   328..331  frame_depth (for prologue/epilogue)
#   332..631  frame_stack (5 frames × 60 bytes each)
#   680       input_flag (expansion buffer)
#   684       input_ptr
#   688       input_end
#   696       eol_flag
#   700       pushback_flag
#   704       pending_nl
#   728       line_count
#
# Token buffer constants:
.equ	TOK_MAX,	256
.equ	TB_EOT,		256
.equ	TB_LLCNT,	288
.equ	TB_FRAMEDEP,	328
.equ	TB_FRAMES,	332
.equ	TB_INFLAG,	680
.equ	TB_INPTR,	684
.equ	TB_INEND,	688
.equ	TB_EOL,		696
.equ	TB_PUSHBACK,	700
.equ	TB_PENDING,	704
.equ	TB_LINECOUNT,	728
#
# Fixup slot types:
#   1 = J-type (PC-relative 20-bit signed)
#   7 = U_hi20_pcrel (auipc in lla/call/tail)
#   8 = I_lo12_pcrel_prev (addi/jalr after auipc)
#
# Calling convention:
#   args a0..a7, return a0 (a1 for two-value)
#   s-regs are global invariants
#   nested calls save/restore ra on stack

.section .text
.globl _start

# ══════════════════════════════════════════════════════════════════════════════
#  Mnemonic table classes
# ══════════════════════════════════════════════════════════════════════════════
# Each entry: 8-byte padded name + class[1] + f3[1] + f7[1] + pad[1] = 12 bytes
# Classes:
#   1=R, 2=I_arith, 3=I_shift, 4=I_load, 5=S, 6=B,
#   7=U_lui, 8=U_auipc, 9=J_jal, 10=I_jalr,
#   11=ps_li, 12=ps_mv, 13=ps_j, 14=ps_ret, 15=ps_beqz, 16=ps_bnez,
#   17=ps_equ,
#   19=ps_byte, 21=ps_word, 22=ps_ascii, 24=ps_zero,
#   28=ps_lla, 29=ps_call, 30=ps_tail,
#   31=ps_nop, 32=ps_neg, 33=ps_not,
#   34=ps_seqz, 35=ps_snez, 36=ps_sltz, 37=ps_sgtz,
#   38=ps_bgt, 39=ps_ble, 40=ps_bgtu, 41=ps_bleu,
#   42=ps_prologue, 43=ps_epilogue, 44=ps_return,
#   46=ps_bltz, 47=ps_bgez, 48=ps_wfi, 49=ps_blez

# ══════════════════════════════════════════════════════════════════════════════
#  Entry point — jump over embedded data tables
# ══════════════════════════════════════════════════════════════════════════════
_start:
	nop				# q32 magic
	jal	t0, after_mnem_tab	# t0 = &mnem_table (PC after jal)

mnem_table:
# R-type (class 1)
.ascii "add\0\0\0\0\0"
.byte 1, 0, 0, 0
.ascii "sub\0\0\0\0\0"
.byte 1, 0, 0x20, 0
.ascii "sll\0\0\0\0\0"
.byte 1, 1, 0, 0
.ascii "slt\0\0\0\0\0"
.byte 1, 2, 0, 0
.ascii "sltu\0\0\0\0"
.byte 1, 3, 0, 0
.ascii "xor\0\0\0\0\0"
.byte 1, 4, 0, 0
.ascii "srl\0\0\0\0\0"
.byte 1, 5, 0, 0
.ascii "sra\0\0\0\0\0"
.byte 1, 5, 0x20, 0
.ascii "or\0\0\0\0\0\0"
.byte 1, 6, 0, 0
.ascii "and\0\0\0\0\0"
.byte 1, 7, 0, 0

# I-type arithmetic (class 2)
.ascii "addi\0\0\0\0"
.byte 2, 0, 0, 0
.ascii "slti\0\0\0\0"
.byte 2, 2, 0, 0
.ascii "sltiu\0\0\0"
.byte 2, 3, 0, 0
.ascii "xori\0\0\0\0"
.byte 2, 4, 0, 0
.ascii "ori\0\0\0\0\0"
.byte 2, 6, 0, 0
.ascii "andi\0\0\0\0"
.byte 2, 7, 0, 0

# I-type shift (class 3)
.ascii "slli\0\0\0\0"
.byte 3, 1, 0, 0
.ascii "srli\0\0\0\0"
.byte 3, 5, 0, 0
.ascii "srai\0\0\0\0"
.byte 3, 5, 0x20, 0

# Loads (class 4)
.ascii "lb\0\0\0\0\0\0"
.byte 4, 0, 0, 0
.ascii "lh\0\0\0\0\0\0"
.byte 4, 1, 0, 0
.ascii "lw\0\0\0\0\0\0"
.byte 4, 2, 0, 0
.ascii "lbu\0\0\0\0\0"
.byte 4, 4, 0, 0
.ascii "lhu\0\0\0\0\0"
.byte 4, 5, 0, 0

# Stores (class 5)
.ascii "sb\0\0\0\0\0\0"
.byte 5, 0, 0, 0
.ascii "sh\0\0\0\0\0\0"
.byte 5, 1, 0, 0
.ascii "sw\0\0\0\0\0\0"
.byte 5, 2, 0, 0

# Branches (class 6)
.ascii "beq\0\0\0\0\0"
.byte 6, 0, 0, 0
.ascii "bne\0\0\0\0\0"
.byte 6, 1, 0, 0
.ascii "blt\0\0\0\0\0"
.byte 6, 4, 0, 0
.ascii "bge\0\0\0\0\0"
.byte 6, 5, 0, 0
.ascii "bltu\0\0\0\0"
.byte 6, 6, 0, 0
.ascii "bgeu\0\0\0\0"
.byte 6, 7, 0, 0

# U-type (classes 7-8)
.ascii "lui\0\0\0\0\0"
.byte 7, 0, 0, 0
.ascii "auipc\0\0\0"
.byte 8, 0, 0, 0

# J-type (class 9)
.ascii "jal\0\0\0\0\0"
.byte 9, 0, 0, 0

# (class 10 "jalr" removed — static jumps only)

# Pseudos
.ascii "li\0\0\0\0\0\0"
.byte 11, 0, 0, 0
.ascii "mv\0\0\0\0\0\0"
.byte 12, 0, 0, 0
.ascii "j\0\0\0\0\0\0\0"
.byte 13, 0, 0, 0
# (class 14 "ret" removed — static jumps only)
.ascii "beqz\0\0\0\0"
.byte 15, 0, 0, 0
.ascii "bnez\0\0\0\0"
.byte 16, 0, 0, 0

# Directives
.ascii ".equ\0\0\0\0"
.byte 17, 0, 0, 0
.ascii ".byte\0\0\0"
.byte 19, 0, 0, 0
.ascii ".word\0\0\0"
.byte 21, 0, 0, 0
.ascii ".ascii\0\0"
.byte 22, 0, 0, 0
.ascii ".zero\0\0\0"
.byte 24, 0, 0, 0

# PC-relative pseudos
.ascii "lla\0\0\0\0\0"
.byte 28, 0, 0, 0
# (class 29 "call" and 30 "tail" removed — they expand to auipc+jalr)

# Simple pseudos
.ascii "nop\0\0\0\0\0"
.byte 31, 0, 0, 0
.ascii "neg\0\0\0\0\0"
.byte 32, 0, 0, 0
.ascii "not\0\0\0\0\0"
.byte 33, 0, 0, 0
.ascii "seqz\0\0\0\0"
.byte 34, 0, 0, 0
.ascii "snez\0\0\0\0"
.byte 35, 0, 0, 0
.ascii "sltz\0\0\0\0"
.byte 36, 0, 0, 0
.ascii "sgtz\0\0\0\0"
.byte 37, 0, 0, 0
.ascii "bgt\0\0\0\0\0"
.byte 38, 0, 0, 0
.ascii "ble\0\0\0\0\0"
.byte 39, 0, 0, 0
.ascii "bgtu\0\0\0\0"
.byte 40, 0, 0, 0
.ascii "bleu\0\0\0\0"
.byte 41, 0, 0, 0
.ascii "bltz\0\0\0\0"
.byte 46, 0, 0, 0
.ascii "bgez\0\0\0\0"
.byte 47, 0, 0, 0
.ascii "blez\0\0\0\0"
.byte 49, 0, 0, 0

# Frame pseudos (prologue/epilogue kept — they just save/restore regs to stack;
# "return" removed because it expands to epilogue + ret)
.ascii "prologu"
.byte 'e', 42, 0, 0, 0
.ascii "epilogu"
.byte 'e', 43, 0, 0, 0

# WFI
.ascii "wfi\0\0\0\0\0"
.byte 48, 0, 0, 0

# Sentinel (null name)
.word 0, 0, 0

after_mnem_tab:
	jal	t1, after_reg_tab	# t1 = &reg_table

reg_table:
# 8 bytes per entry: 4-byte padded name + 4-byte register number
.ascii "zero"
.word 0
.ascii "ra\0\0"
.word 1
.ascii "sp\0\0"
.word 2
.ascii "gp\0\0"
.word 3
.ascii "tp\0\0"
.word 4
.ascii "t0\0\0"
.word 5
.ascii "t1\0\0"
.word 6
.ascii "t2\0\0"
.word 7
.ascii "s0\0\0"
.word 8
.ascii "fp\0\0"
.word 8
.ascii "s1\0\0"
.word 9
.ascii "a0\0\0"
.word 10
.ascii "a1\0\0"
.word 11
.ascii "a2\0\0"
.word 12
.ascii "a3\0\0"
.word 13
.ascii "a4\0\0"
.word 14
.ascii "a5\0\0"
.word 15
.ascii "a6\0\0"
.word 16
.ascii "a7\0\0"
.word 17
.ascii "s2\0\0"
.word 18
.ascii "s3\0\0"
.word 19
.ascii "s4\0\0"
.word 20
.ascii "s5\0\0"
.word 21
.ascii "s6\0\0"
.word 22
.ascii "s7\0\0"
.word 23
.ascii "s8\0\0"
.word 24
.ascii "s9\0\0"
.word 25
.ascii "s10\0"
.word 26
.ascii "s11\0"
.word 27
.ascii "t3\0\0"
.word 28
.ascii "t4\0\0"
.word 29
.ascii "t5\0\0"
.word 30
.ascii "t6\0\0"
.word 31
# Sentinel
.word 0, 0

after_reg_tab:

# ══════════════════════════════════════════════════════════════════════════════
#  Initialization
# ══════════════════════════════════════════════════════════════════════════════

	mv	s9, t0			# mnem_table base
	mv	s11, t1			# reg_table base
	li	s6, 10			# constant
	lui	s5, 0x10000		# UART base

	auipc	a0, 0			# PC base for memory regions
	lui	t2, 0x10
	add	s1, a0, t2		# output buffer = PC + 0x10000
	mv	s2, s1
	lui	t2, 0x90
	add	s3, a0, t2		# symtab = PC + 0x90000
	mv	s4, s3
	lui	t2, 0xD0
	add	s7, a0, t2		# fixup table = PC + 0xD0000
	mv	s8, s7
	lui	t2, 0x110
	add	s10, a0, t2		# token buffer = PC + 0x110000
	lui	t2, 0x120
	add	sp, a0, t2		# stack = PC + 0x120000

	# Zero: EOT flag, local-label counters, frame depth, flags
	sb	zero, TB_EOT(s10)		# sticky EOT
	addi	t2, s10, TB_LLCNT
	addi	t3, s10, TB_LINECOUNT+4
init_zero:
	sw	zero, 0(t2)
	addi	t2, t2, 4
	bne	t2, t3, init_zero

	sw	zero, TB_LINECOUNT(s10)		# line_count = 0
	j	main_loop

# ══════════════════════════════════════════════════════════════════════════════
#  Main Loop
# ══════════════════════════════════════════════════════════════════════════════

main_loop:
	li	gp, 0
	j	read_token
read_token_rs0:
	beqz	s0, ml_post		# empty token

	# Check for ':' suffix → label definition
	add	t0, s10, s0
	lbu	t1, -1(t0)
	li	t2, ':'
	beq	t1, t2, ml_label
	j	ml_mnem

ml_label:
	# Local label? (len==2, first char is digit)
	li	t2, 2
	bne	s0, t2, ml_named
	lbu	t0, 0(s10)
	li	t1, '0'
	blt	t0, t1, ml_named
	li	t1, '9'+1
	bge	t0, t1, ml_named
	addi	a0, t0, -'0'
	li	gp, 0
	j	def_local_label
def_local_label_rs0:
	j	ml_post
ml_named:
	li	gp, 0
	j	define_label
define_label_rs0:
	j	ml_post

ml_mnem:
	li	gp, 0
	j	find_mnem
find_mnem_rs0:
	li	t0, -1
	bne	a0, t0, ml_dispatch
	# Unknown mnemonic → error
	li	a0, 1
	j	halt_err
ml_dispatch:
	li	gp, 0
	j	dispatch
dispatch_rs0:
ml_post:
	lbu	t0, TB_EOT(s10)		# sticky EOT flag
	bnez	t0, finish_all
	j	main_loop

# ══════════════════════════════════════════════════════════════════════════════
#  Finish: fixup pass + output + shutdown
# ══════════════════════════════════════════════════════════════════════════════

finish_all:
	li	gp, 0
	j	fixup_pass
fixup_pass_rs0:
	li	gp, 0
	j	dump_output
dump_output_rs0:
	# fall through to poweroff
poweroff:
	lui	s5, 0x100
	lui	t0, 5
	addi	t0, t0, 0x555
	sw	t0, 0(s5)
poweroff_hang:
	j	poweroff_hang

# ══════════════════════════════════════════════════════════════════════════════
#  Error: print "ENN@LINE\n" and halt
# ══════════════════════════════════════════════════════════════════════════════
# a0 = error code (1-29)
# Error codes:
#   E01 unknown mnemonic         E02 read after EOT
#   E03 token too long           E05 bad immediate
#   E06 bad memory operand       E08 bad register
#   E10 bad branch target        E11 label name too long
#   E12 duplicate label          E13 symtab overflow
#   E14 fixup overflow           E15 output overflow
#   E17 unresolved symbol        E18 unknown fixup type
#   E19 I/S imm12 range          E20 U-type imm20 range
#   E21 B-type range             E22 J-type range
#   E24 bad string literal       E25 bad prologue
#   E26 bad epilogue
#
# Trailing `#` comments on the same line as .word / .byte work: when
# read_imm_op sees TB_EOL set after its read_token (indicating the
# tokenizer skipped past a newline before finding a token), it pushes
# the token back and returns a1=1 instead of running eval_expr on it.
# do_ps_word / do_ps_byte check a1 and exit the loop cleanly, and the
# main loop then processes the pushed-back token as its own statement.

imm_range_i:
	li	a0, 19			# E19 = I/S-type immediate out of range
	j	halt_err
imm_range_u:
	li	a0, 20			# E20 = U-type immediate out of range
	j	halt_err
imm_range_b:
	li	a0, 21			# E21 = B-type offset out of range / odd
	j	halt_err
imm_range_j:
	li	a0, 22			# E22 = J-type offset out of range / odd
	j	halt_err
halt_err:
	mv	a1, a0
	li	t0, 'E'
	li	gp, 0
	j	wrch
wrch_rs0:
	# Tens digit
	li	t2, 10
	mv	a2, a1
	li	a3, 0
he_div:
	blt	a2, t2, he_tens
	sub	a2, a2, t2
	addi	a3, a3, 1
	j	he_div
he_tens:
	addi	t0, a3, '0'
	li	gp, 1
	j	wrch
wrch_rs1:
	addi	t0, a2, '0'
	li	gp, 2
	j	wrch
wrch_rs2:
	li	t0, '@'
	li	gp, 3
	j	wrch
wrch_rs3:
	# Line number (decimal, up to 6 digits)
	lw	a1, TB_LINECOUNT(s10)
	addi	sp, sp, -24
	li	t2, 100000
	sw	t2, 0(sp)
	li	t2, 10000
	sw	t2, 4(sp)
	li	t2, 1000
	sw	t2, 8(sp)
	li	t2, 100
	sw	t2, 12(sp)
	li	t2, 10
	sw	t2, 16(sp)
	li	t2, 1
	sw	t2, 20(sp)
	mv	t3, sp
	addi	t4, sp, 24
	li	a2, 1			# leading-zero suppression
he_dec:
	beq	t3, t4, he_dec_done
	lw	t2, 0(t3)
	li	a3, 0
he_dec_sub:
	blt	a1, t2, he_dec_emit
	sub	a1, a1, t2
	addi	a3, a3, 1
	j	he_dec_sub
he_dec_emit:
	addi	t5, t3, 4
	beq	t5, t4, he_dec_pr	# last digit: always print
	beqz	a3, he_dec_skip
	li	a2, 0			# saw nonzero: stop suppressing
	j	he_dec_pr
he_dec_skip:
	bnez	a2, he_dec_nx		# still suppressing
he_dec_pr:
	addi	t0, a3, '0'
	li	gp, 4
	j	wrch
wrch_rs4:
he_dec_nx:
	addi	t3, t3, 4
	j	he_dec
he_dec_done:
	addi	sp, sp, 24
	li	t0, '\n'
	li	gp, 5
	j	wrch
wrch_rs5:
	lui	s5, 0x100
	lui	t0, 5
	addi	t0, t0, 0x555
	sw	t0, 0(s5)
halt_hang:
	j	halt_hang

# ══════════════════════════════════════════════════════════════════════════════
#  UART Primitives
# ══════════════════════════════════════════════════════════════════════════════

rdch:
	# Read one char into t1. Check expansion buffer first.
	lw	t5, TB_INFLAG(s10)		# input_flag
	beqz	t5, rdch_uart
	lw	t5, TB_INPTR(s10)		# input_ptr
	lw	t6, TB_INEND(s10)		# input_end
	beq	t5, t6, rdch_exh
	lbu	t1, 0(t5)
	addi	t5, t5, 1
	sw	t5, TB_INPTR(s10)
	j	rdch_disp
rdch_exh:
	sw	zero, TB_INFLAG(s10)		# clear expansion flag
rdch_uart:
	lbu	t5, TB_EOT(s10)		# sticky EOT
	beqz	t5, rdch_poll
	li	a0, 2			# E02: read after EOT
	j	halt_err
rdch_poll:
	lbu	t5, 5(s5)
	andi	t5, t5, 1
	beqz	t5, rdch_poll
	lbu	t1, 0(s5)
	j	rdch_disp

rdch_disp:
	bnez	gp, rdch_d1
	j	rdch_rs0
rdch_d1:
	addi	gp, gp, -1
	bnez	gp, rdch_d2
	j	rdch_rs1
rdch_d2:
	addi	gp, gp, -1
	bnez	gp, rdch_d3
	j	rdch_rs2
rdch_d3:
	addi	gp, gp, -1
	bnez	gp, rdch_d4
	j	rdch_rs3
rdch_d4:
	addi	gp, gp, -1
	bnez	gp, rdch_d5
	j	rdch_rs4
rdch_d5:
	addi	gp, gp, -1
	bnez	gp, rdch_d6
	j	rdch_rs5
rdch_d6:
	addi	gp, gp, -1
	bnez	gp, rdch_d7
	j	rdch_rs6
rdch_d7:
	addi	gp, gp, -1
	j	rdch_rs7

wrch:
	# Write t0 to UART
	lbu	t5, 5(s5)
	andi	t5, t5, 0x20
	beqz	t5, wrch
	sb	t0, 0(s5)
	j	wrch_disp

# ══════════════════════════════════════════════════════════════════════════════
#  Tokenizer: read_token
# ══════════════════════════════════════════════════════════════════════════════
# On exit: s0 = length (0..31), token text at s10 (zero-padded to 32 bytes)
# Sets sticky EOT flag at TB_EOT(s10) on EOT.

wrch_disp:
	bnez	gp, wrch_d1
	j	wrch_rs0
wrch_d1:
	addi	gp, gp, -1
	bnez	gp, wrch_d2
	j	wrch_rs1
wrch_d2:
	addi	gp, gp, -1
	bnez	gp, wrch_d3
	j	wrch_rs2
wrch_d3:
	addi	gp, gp, -1
	bnez	gp, wrch_d4
	j	wrch_rs3
wrch_d4:
	addi	gp, gp, -1
	bnez	gp, wrch_d5
	j	wrch_rs4
wrch_d5:
	addi	gp, gp, -1
	bnez	gp, wrch_d6
	j	wrch_rs5
wrch_d6:
	addi	gp, gp, -1
	bnez	gp, wrch_d7
	j	wrch_rs6
wrch_d7:
	addi	gp, gp, -1
	bnez	gp, wrch_d8
	j	wrch_rs7
wrch_d8:
	addi	gp, gp, -1
	bnez	gp, wrch_d9
	j	wrch_rs8
wrch_d9:
	addi	gp, gp, -1
	j	wrch_rs9

read_token:
	# Pushback: if active, clear and return with existing token
	lw	t0, TB_PUSHBACK(s10)
	beqz	t0, rt_entry
	sw	zero, TB_PUSHBACK(s10)
	j	read_token_disp
rt_entry:
	# Transfer pending_nl → eol_flag
	lw	t0, TB_PENDING(s10)
	sw	t0, TB_EOL(s10)
	sw	zero, TB_PENDING(s10)

	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	s0, 0
	# Zero token buffer (32 bytes)
	mv	t0, s10
	addi	t2, s10, TOK_MAX
rt_zero:
	sb	zero, 0(t0)
	addi	t0, t0, 1
	bne	t0, t2, rt_zero

rt_skip:
	li	gp, 0
	j	rdch
rdch_rs0:
	li	t0, 4			# EOT
	beq	t1, t0, rt_eot
	li	t0, '#'
	beq	t1, t0, rt_comment
	bne	t1, s6, rt_not_nl	# s6 = 10 = '\n'
	# Newline
	li	t0, 1
	sw	t0, TB_EOL(s10)		# eol_flag
	lw	t0, TB_LINECOUNT(s10)
	addi	t0, t0, 1
	sw	t0, TB_LINECOUNT(s10)		# line_count++
	j	rt_skip
rt_not_nl:
	li	t0, ','
	beq	t1, t0, rt_skip
	li	t0, 33
	blt	t1, t0, rt_skip		# whitespace/control
	li	t0, '"'
	beq	t1, t0, rt_str		# quoted string
	li	t0, '\''
	beq	t1, t0, rt_chr		# char literal
	j	rt_collect

rt_comment:
	li	gp, 1
	j	rdch
rdch_rs1:
	li	t0, 4
	beq	t1, t0, rt_eot
	bne	t1, s6, rt_comment
	# Newline ends comment
	li	t0, 1
	sw	t0, TB_EOL(s10)
	lw	t0, TB_LINECOUNT(s10)
	addi	t0, t0, 1
	sw	t0, TB_LINECOUNT(s10)
	j	rt_skip

rt_collect:
	add	t0, s10, s0
	sb	t1, 0(t0)
	addi	s0, s0, 1
	li	t0, TOK_MAX
	blt	s0, t0, rt_coll_next
	li	a0, 3			# E03: token too long
	j	halt_err
rt_coll_next:
	li	gp, 2
	j	rdch
rdch_rs2:
	li	t0, 4
	beq	t1, t0, rt_eot
	li	t0, '#'
	beq	t1, t0, rt_coll_comment
	li	t0, ','
	beq	t1, t0, rt_done
	bne	t1, s6, rt_coll_not_nl
	# Newline terminates token
	li	t0, 1
	sw	t0, TB_PENDING(s10)		# pending_nl
	lw	t0, TB_LINECOUNT(s10)
	addi	t0, t0, 1
	sw	t0, TB_LINECOUNT(s10)
	j	rt_done
rt_coll_not_nl:
	li	t0, 33
	blt	t1, t0, rt_done		# whitespace ends token
	j	rt_collect

rt_coll_comment:
	# Comment after token — skip to newline
	li	gp, 3
	j	rdch
rdch_rs3:
	li	t0, 4
	beq	t1, t0, rt_eot
	bne	t1, s6, rt_coll_comment
	li	t0, 1
	sw	t0, TB_PENDING(s10)
	lw	t0, TB_LINECOUNT(s10)
	addi	t0, t0, 1
	sw	t0, TB_LINECOUNT(s10)
	j	rt_done

# ─── Quoted string token ─────────────────────────────────────────────
rt_str:
	add	t0, s10, s0
	sb	t1, 0(t0)		# store opening '"'
	addi	s0, s0, 1
	li	t0, TOK_MAX
	blt	s0, t0, rt_str_lp
	li	a0, 3
	j	halt_err
rt_str_lp:
	li	gp, 4
	j	rdch
rdch_rs4:
	li	t0, 4
	beq	t1, t0, rt_str_eot
	li	t0, '\\'
	beq	t1, t0, rt_str_bs
	add	t0, s10, s0
	sb	t1, 0(t0)
	addi	s0, s0, 1
	li	t0, TOK_MAX
	blt	s0, t0, rt_str_chk
	li	a0, 3
	j	halt_err
rt_str_chk:
	li	t0, '"'
	beq	t1, t0, rt_done		# closing quote
	j	rt_str_lp
rt_str_bs:
	# Store backslash + next char
	add	t0, s10, s0
	sb	t1, 0(t0)
	addi	s0, s0, 1
	li	t0, TOK_MAX
	blt	s0, t0, rt_str_bs2
	li	a0, 3
	j	halt_err
rt_str_bs2:
	li	gp, 5
	j	rdch
rdch_rs5:
	li	t0, 4
	beq	t1, t0, rt_str_eot
	add	t0, s10, s0
	sb	t1, 0(t0)
	addi	s0, s0, 1
	li	t0, TOK_MAX
	blt	s0, t0, rt_str_lp
	li	a0, 3
	j	halt_err
rt_str_eot:
	li	a0, 2			# E02: unexpected EOT in string
	j	halt_err

# ─── Char literal token ──────────────────────────────────────────────
rt_chr:
	add	t0, s10, s0
	sb	t1, 0(t0)		# store opening '\''
	addi	s0, s0, 1
rt_chr_lp:
	li	gp, 6
	j	rdch
rdch_rs6:
	li	t0, 4
	beq	t1, t0, rt_str_eot
	li	t0, '\\'
	beq	t1, t0, rt_chr_bs
	add	t0, s10, s0
	sb	t1, 0(t0)
	addi	s0, s0, 1
	li	t0, TOK_MAX
	blt	s0, t0, rt_chr_chk
	li	a0, 3
	j	halt_err
rt_chr_chk:
	li	t0, '\''
	beq	t1, t0, rt_done
	j	rt_chr_lp
rt_chr_bs:
	add	t0, s10, s0
	sb	t1, 0(t0)
	addi	s0, s0, 1
	li	t0, TOK_MAX
	blt	s0, t0, rt_chr_bs2
	li	a0, 3
	j	halt_err
rt_chr_bs2:
	li	gp, 7
	j	rdch
rdch_rs7:
	li	t0, 4
	beq	t1, t0, rt_str_eot
	add	t0, s10, s0
	sb	t1, 0(t0)
	addi	s0, s0, 1
	li	t0, TOK_MAX
	blt	s0, t0, rt_chr_lp
	li	a0, 3
	j	halt_err

rt_eot:
	li	t0, 1
	sb	t0, TB_EOT(s10)		# set sticky EOT
rt_done:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	read_token_disp

# ══════════════════════════════════════════════════════════════════════════════
#  find_mnem: token in buf at s10 (zero-padded).
#  Returns: a0 = class, a1 = f3, a2 = f7, or a0 = -1 if not found.
# ══════════════════════════════════════════════════════════════════════════════

read_token_disp:
	bnez	gp, read_token_d1
	j	read_token_rs0
read_token_d1:
	addi	gp, gp, -1
	bnez	gp, read_token_d2
	j	read_token_rs1
read_token_d2:
	addi	gp, gp, -1
	bnez	gp, read_token_d3
	j	read_token_rs2
read_token_d3:
	addi	gp, gp, -1
	bnez	gp, read_token_d4
	j	read_token_rs3
read_token_d4:
	addi	gp, gp, -1
	bnez	gp, read_token_d5
	j	read_token_rs4
read_token_d5:
	addi	gp, gp, -1
	bnez	gp, read_token_d6
	j	read_token_rs5
read_token_d6:
	addi	gp, gp, -1
	bnez	gp, read_token_d7
	j	read_token_rs6
read_token_d7:
	addi	gp, gp, -1
	bnez	gp, read_token_d8
	j	read_token_rs7
read_token_d8:
	addi	gp, gp, -1
	bnez	gp, read_token_d9
	j	error_halt
read_token_d9:
	addi	gp, gp, -1
	bnez	gp, read_token_d10
	j	read_token_rs9
read_token_d10:
	addi	gp, gp, -1
	j	read_token_rs10

find_mnem:
	mv	t0, s9
fm_next:
	lbu	t1, 0(t0)
	beqz	t1, fm_notfound
	mv	t2, s10
	mv	t3, t0
	li	t4, 8
fm_cmp:
	lbu	t5, 0(t2)
	lbu	t6, 0(t3)
	bne	t5, t6, fm_skip
	addi	t2, t2, 1
	addi	t3, t3, 1
	addi	t4, t4, -1
	bnez	t4, fm_cmp
	lbu	a0, 8(t0)		# class
	lbu	a1, 9(t0)		# f3
	lbu	a2, 10(t0)		# f7
	j	find_mnem_disp
fm_skip:
	addi	t0, t0, 12
	j	fm_next
fm_notfound:
	li	a0, -1
	j	find_mnem_disp

# ══════════════════════════════════════════════════════════════════════════════
#  parse_reg: a0=ptr, a1=len → a0=reg num (0..31) or -1
# ══════════════════════════════════════════════════════════════════════════════

find_mnem_disp:
	j	find_mnem_rs0

parse_reg:
	mv	t0, a0			# save ptr (a0 gets clobbered in cmp)
	beqz	a1, pr_bad
	lbu	t2, 0(t0)
	li	t3, 'x'
	bne	t2, t3, pr_abi

	# xN or xNN
	li	t3, 2
	beq	a1, t3, pr_x1
	li	t3, 3
	beq	a1, t3, pr_x2
	j	pr_bad
pr_x1:
	lbu	t2, 1(t0)
	addi	t2, t2, -'0'
	bltz	t2, pr_bad
	li	t3, 10
	bge	t2, t3, pr_bad
	mv	a0, t2
	j	parse_reg_disp
pr_x2:
	lbu	t2, 1(t0)
	addi	t2, t2, -'0'
	bltz	t2, pr_bad
	li	t3, 10
	bge	t2, t3, pr_bad
	lbu	t4, 2(t0)
	addi	t4, t4, -'0'
	bltz	t4, pr_bad
	bge	t4, t3, pr_bad
	slli	t5, t2, 3
	slli	t6, t2, 1
	add	t5, t5, t6
	add	a0, t5, t4
	li	t3, 32
	bge	a0, t3, pr_bad
	j	parse_reg_disp

pr_abi:
	li	t2, 5
	bge	a1, t2, pr_bad		# ABI names are 2-4 chars
	mv	t2, s11
pr_a_next:
	lbu	t3, 0(t2)
	beqz	t3, pr_bad		# sentinel
	mv	t4, t0			# token ptr (use saved t0)
	mv	t5, t2			# entry name ptr
	mv	t6, a1			# remaining len
pr_a_cmp:
	lbu	a0, 0(t4)
	lbu	a2, 0(t5)
	bne	a0, a2, pr_a_skip
	addi	t4, t4, 1
	addi	t5, t5, 1
	addi	t6, t6, -1
	bnez	t6, pr_a_cmp
	# Matched first a1 bytes. Ensure entry pad bytes are null.
	li	t6, 4
	sub	t6, t6, a1
	beqz	t6, pr_a_found
pr_a_pad:
	lbu	a0, 0(t5)
	bnez	a0, pr_a_skip
	addi	t5, t5, 1
	addi	t6, t6, -1
	bnez	t6, pr_a_pad
pr_a_found:
	lbu	a0, 4(t2)		# reg number at offset 4
	j	parse_reg_disp
pr_a_skip:
	addi	t2, t2, 8
	j	pr_a_next
pr_bad:
	li	a0, -1
	j	parse_reg_disp

# ══════════════════════════════════════════════════════════════════════════════
#  parse_imm: a0=ptr, a1=len → a0=value. Halts on error.
#  Handles: decimal, 0xHEX, negative, char literals ('x', '\n')
# ══════════════════════════════════════════════════════════════════════════════

parse_reg_disp:
	bnez	gp, parse_reg_d1
	j	parse_reg_rs0
parse_reg_d1:
	addi	gp, gp, -1
	bnez	gp, parse_reg_d2
	j	parse_reg_rs1
parse_reg_d2:
	addi	gp, gp, -1
	bnez	gp, parse_reg_d3
	j	parse_reg_rs2
parse_reg_d3:
	addi	gp, gp, -1
	j	error_halt

parse_imm:
	mv	t0, a0			# ptr
	mv	t1, a1			# len
	li	t2, 1			# sign (+1)
	beqz	t1, pi_bad

	# Char literal?
	lbu	t3, 0(t0)
	li	t4, '\''
	bne	t3, t4, pi_not_char
	# 'x' (len=3) or '\x' (len=4)
	li	t4, 3
	blt	t1, t4, pi_bad
	add	t4, t0, t1
	addi	t4, t4, -1
	lbu	t5, 0(t4)
	li	t4, '\''
	bne	t5, t4, pi_bad
	li	t4, 3
	beq	t1, t4, pi_char_plain
	li	t4, 4
	bne	t1, t4, pi_bad
	# Escaped: '\x'
	lbu	t3, 1(t0)
	li	t4, '\\'
	bne	t3, t4, pi_bad
	lbu	t3, 2(t0)
	li	t4, 'n'
	beq	t3, t4, pi_esc_n
	li	t4, 't'
	beq	t3, t4, pi_esc_t
	li	t4, 'r'
	beq	t3, t4, pi_esc_r
	li	t4, '0'
	beq	t3, t4, pi_esc_0
	li	t4, '\\'
	beq	t3, t4, pi_esc_lit
	li	t4, '\''
	beq	t3, t4, pi_esc_lit
	j	pi_bad
pi_esc_n:
	li	a0, 10
	j	parse_imm_disp
pi_esc_t:
	li	a0, 9
	j	parse_imm_disp
pi_esc_r:
	li	a0, 13
	j	parse_imm_disp
pi_esc_0:
	li	a0, 0
	j	parse_imm_disp
pi_esc_lit:
	mv	a0, t3
	j	parse_imm_disp
pi_char_plain:
	lbu	a0, 1(t0)
	j	parse_imm_disp

pi_not_char:
	# Sign
	li	t4, '-'
	bne	t3, t4, pi_plus
	li	t2, -1
	addi	t0, t0, 1
	addi	t1, t1, -1
	j	pi_after_sign
pi_plus:
	li	t4, '+'
	bne	t3, t4, pi_after_sign
	addi	t0, t0, 1
	addi	t1, t1, -1
pi_after_sign:
	beqz	t1, pi_bad

	# Check for 0x prefix
	li	t4, 2
	blt	t1, t4, pi_decimal
	lbu	t3, 0(t0)
	li	t4, '0'
	bne	t3, t4, pi_decimal
	lbu	t3, 1(t0)
	li	t4, 'x'
	beq	t3, t4, pi_hex
	li	t4, 'X'
	beq	t3, t4, pi_hex
	j	pi_decimal

pi_hex:
	addi	t0, t0, 2
	addi	t1, t1, -2
	beqz	t1, pi_bad
	li	a0, 0
pi_hex_lp:
	beqz	t1, pi_done
	lbu	t3, 0(t0)
	addi	t4, t3, -'0'
	li	t5, 10
	blt	t4, t5, pi_h_ok
	addi	t4, t3, -'A'
	addi	t4, t4, 10
	blt	t4, t5, pi_bad
	li	t5, 16
	blt	t4, t5, pi_h_ok
	addi	t4, t3, -'a'
	addi	t4, t4, 10
	li	t5, 10
	blt	t4, t5, pi_bad
	li	t5, 16
	blt	t4, t5, pi_h_ok
	j	pi_bad
pi_h_ok:
	slli	a0, a0, 4
	or	a0, a0, t4
	addi	t0, t0, 1
	addi	t1, t1, -1
	j	pi_hex_lp

pi_decimal:
	li	a0, 0
	beqz	t1, pi_bad
pi_dec_lp:
	beqz	t1, pi_done
	lbu	t3, 0(t0)
	addi	t3, t3, -'0'
	bltz	t3, pi_bad
	li	t4, 10
	bge	t3, t4, pi_bad
	slli	t4, a0, 3
	slli	t5, a0, 1
	add	t4, t4, t5
	add	a0, t4, t3
	addi	t0, t0, 1
	addi	t1, t1, -1
	j	pi_dec_lp

pi_done:
	li	t3, 1
	beq	t2, t3, pi_ret
	sub	a0, zero, a0
pi_ret:
	j	parse_imm_disp
pi_bad:
	li	a0, 5			# E05: bad immediate
	j	halt_err

# ══════════════════════════════════════════════════════════════════════════════
#  parse_mem: a0=ptr, a1=len → a0=imm, a1=reg. Expects imm(rs).
# ══════════════════════════════════════════════════════════════════════════════

parse_imm_disp:
	bnez	gp, parse_imm_d1
	j	parse_imm_rs0
parse_imm_d1:
	addi	gp, gp, -1
	bnez	gp, parse_imm_d2
	j	parse_imm_rs1
parse_imm_d2:
	addi	gp, gp, -1
	j	parse_imm_rs2

parse_mem:
	addi	sp, sp, -20
	sw	gp, 0(sp)
	sw	a0, 4(sp)		# ptr
	sw	a1, 8(sp)		# len
	mv	t0, a0
	mv	t1, a1
	li	t2, 0
	li	t3, '('
pm_scan:
	bge	t2, t1, pm_bad
	add	t4, t0, t2
	lbu	t5, 0(t4)
	beq	t5, t3, pm_found
	addi	t2, t2, 1
	j	pm_scan
pm_found:
	sw	t2, 12(sp)		# paren position
	# Parse immediate: ptr..ptr+t2 (use eval_expr for symbol support)
	mv	a0, t0
	add	a1, t0, t2		# end ptr = start + paren offset
	li	gp, 0
	j	eval_expr
eval_expr_rs0:
	bne	a2, a1, pm_bad		# must consume everything before '('
	sw	a0, 16(sp)		# imm value
	# Parse register: ptr+t2+1 .. ptr+len-1 (excluding closing ')')
	lw	t0, 4(sp)
	lw	t1, 8(sp)
	lw	t2, 12(sp)
	# Check closing ')'
	addi	t3, t1, -1
	add	t4, t0, t3
	lbu	t5, 0(t4)
	li	t6, ')'
	bne	t5, t6, pm_bad
	# Register name: ptr+t2+1, len = t1-t2-2
	add	a0, t0, t2
	addi	a0, a0, 1
	sub	a1, t1, t2
	addi	a1, a1, -2
	li	gp, 0
	j	parse_reg
parse_reg_rs0:
	li	t3, -1
	beq	a0, t3, pm_bad
	mv	a1, a0			# reg
	lw	a0, 16(sp)		# imm
	lw	gp, 0(sp)
	addi	sp, sp, 20
	j	parse_mem_disp
pm_bad:
	li	a0, 6			# E06: bad memory operand
	j	halt_err

# ══════════════════════════════════════════════════════════════════════════════
#  Expression evaluator (simplified: + and - only)
# ══════════════════════════════════════════════════════════════════════════════
# eval_expr: a0=start_ptr, a1=end_ptr → a0=value, a2=new_ptr
#   Parses: primary (('+' | '-') primary)*
#   primary: number | symbol_lookup | '(' expr ')'

parse_mem_disp:
	bnez	gp, parse_mem_d1
	j	parse_mem_rs0
parse_mem_d1:
	addi	gp, gp, -1
	j	error_halt

eval_expr:
	addi	sp, sp, -12
	sw	gp, 0(sp)
	sw	a1, 8(sp)		# save end ptr (eval_primary clobbers a1)
	li	gp, 0
	j	eval_primary
eval_primary_rs0:
	lw	a1, 8(sp)		# restore end
ee_lp:
	beq	a2, a1, ee_done
	lbu	t0, 0(a2)
	li	t1, '+'
	beq	t0, t1, ee_add
	li	t1, '-'
	beq	t0, t1, ee_sub
	j	ee_done
ee_add:
	sw	a0, 4(sp)
	addi	a0, a2, 1
	li	gp, 1
	j	eval_primary
eval_primary_rs1:
	lw	a1, 8(sp)		# restore end
	lw	t0, 4(sp)
	add	a0, t0, a0
	j	ee_lp
ee_sub:
	sw	a0, 4(sp)
	addi	a0, a2, 1
	li	gp, 2
	j	eval_primary
eval_primary_rs2:
	lw	a1, 8(sp)		# restore end
	lw	t0, 4(sp)
	sub	a0, t0, a0
	j	ee_lp
ee_done:
	lw	gp, 0(sp)
	addi	sp, sp, 12
	j	eval_expr_disp

eval_expr_disp:
	bnez	gp, eval_expr_d1
	j	eval_expr_rs0
eval_expr_d1:
	addi	gp, gp, -1
	bnez	gp, eval_expr_d2
	j	eval_expr_rs1
eval_expr_d2:
	addi	gp, gp, -1
	bnez	gp, eval_expr_d3
	j	eval_expr_rs2
eval_expr_d3:
	addi	gp, gp, -1
	j	eval_expr_rs3

eval_primary:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	beq	a0, a1, ep_bad
	lbu	t0, 0(a0)

	# '(' → subexpression
	li	t1, '('
	beq	t0, t1, ep_paren

	# Digit or sign → number
	li	t1, '0'
	bge	t0, t1, ep_num_chk
	li	t1, '-'
	beq	t0, t1, ep_num_range
	li	t1, '+'
	beq	t0, t1, ep_num_range
	j	ep_ident_chk

ep_num_chk:
	li	t1, '9'+1
	blt	t0, t1, ep_num_range
	j	ep_ident_chk

ep_num_range:
	# Find end of number: skip leading sign, then scan alnum
	mv	t2, a0
	lbu	t3, 0(t2)
	li	t4, '-'
	beq	t3, t4, ep_num_skipsign
	li	t4, '+'
	bne	t3, t4, ep_num_scan
ep_num_skipsign:
	addi	t2, t2, 1		# skip sign char
ep_num_scan:
	beq	t2, a1, ep_num_end
	lbu	t3, 0(t2)
	li	t4, '0'
	blt	t3, t4, ep_num_end
	li	t4, '9'+1
	blt	t3, t4, ep_num_go
	li	t4, 'A'
	blt	t3, t4, ep_num_end
	li	t4, 'Z'+1
	blt	t3, t4, ep_num_go
	li	t4, 'a'
	blt	t3, t4, ep_num_end
	li	t4, 'z'+1
	blt	t3, t4, ep_num_go
	j	ep_num_end
ep_num_go:
	addi	t2, t2, 1
	j	ep_num_scan
ep_num_end:
	mv	a2, t2			# save new_ptr
	sub	a1, t2, a0		# len
	li	gp, 0		# a0 = value
	j	parse_imm
parse_imm_rs0:
	j	ep_ret

ep_ident_chk:
	# Char literal
	li	t1, '\''
	beq	t0, t1, ep_char

	# Letter or underscore → symbol
	li	t1, 'A'
	blt	t0, t1, ep_us
	li	t1, 'Z'+1
	blt	t0, t1, ep_sym
	li	t1, 'a'
	blt	t0, t1, ep_us
	li	t1, 'z'+1
	blt	t0, t1, ep_sym
	j	ep_us
ep_us:
	li	t1, '_'
	beq	t0, t1, ep_sym
	j	ep_bad

ep_sym:
	li	gp, 0
	j	find_sym_ident
find_sym_ident_rs0:
	j	ep_ret

ep_char:
	# Char literal in expression context
	# Determine length: 'x' = 3, '\x' = 4
	addi	t2, a0, 2		# at least 3 chars
	bge	t2, a1, ep_bad
	lbu	t3, 1(a0)
	li	t4, '\\'
	bne	t3, t4, ep_char_3
	addi	t2, a0, 4		# escaped = 4 chars
	bgt	t2, a1, ep_bad
	j	ep_char_go
ep_char_3:
	addi	t2, a0, 3
ep_char_go:
	mv	a2, t2			# new_ptr past closing quote
	sub	a1, t2, a0		# len
	li	gp, 1
	j	parse_imm
parse_imm_rs1:
	j	ep_ret

ep_paren:
	addi	a0, a0, 1		# skip '('
	li	gp, 1
	j	eval_expr
eval_expr_rs1:
	beq	a2, a1, ep_bad
	lbu	t0, 0(a2)
	li	t1, ')'
	bne	t0, t1, ep_bad
	addi	a2, a2, 1		# skip ')'
ep_ret:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	eval_primary_disp
ep_bad:
	li	a0, 5
	j	halt_err

# find_sym_ident: scan identifier at a0, look up in symtab
#   a0=ptr, a1=end → a0=value, a2=new_ptr
eval_primary_disp:
	bnez	gp, eval_primary_d1
	j	eval_primary_rs0
eval_primary_d1:
	addi	gp, gp, -1
	bnez	gp, eval_primary_d2
	j	eval_primary_rs1
eval_primary_d2:
	addi	gp, gp, -1
	j	eval_primary_rs2

find_sym_ident:
	addi	sp, sp, -12
	sw	gp, 0(sp)
	sw	a1, 4(sp)		# save end
	mv	t0, a0
fsi_scan:
	beq	t0, a1, fsi_end
	lbu	t1, 0(t0)
	li	t2, '_'
	beq	t1, t2, fsi_go
	li	t2, '0'
	blt	t1, t2, fsi_end
	li	t2, '9'+1
	blt	t1, t2, fsi_go
	li	t2, 'A'
	blt	t1, t2, fsi_end
	li	t2, 'Z'+1
	blt	t1, t2, fsi_go
	li	t2, 'a'
	blt	t1, t2, fsi_end
	li	t2, 'z'+1
	blt	t1, t2, fsi_go
	j	fsi_end
fsi_go:
	addi	t0, t0, 1
	j	fsi_scan
fsi_end:
	sw	t0, 8(sp)		# save new_ptr
	sub	a1, t0, a0		# len
	beqz	a1, fsi_bad
	li	gp, 0		# a0=val, a1=kind, a2=found
	j	find_sym
find_sym_rs0:
	beqz	a2, fsi_bad		# not found
	lw	a2, 8(sp)		# restore new_ptr
	lw	gp, 0(sp)
	addi	sp, sp, 12
	j	find_sym_ident_disp
fsi_bad:
	li	a0, 17			# E17: unresolved symbol
	j	halt_err

# ══════════════════════════════════════════════════════════════════════════════
#  read_multi_expr: reads tokens until EOL, concatenates, evaluates.
#  Returns: a0 = value. Uses pushback for lookahead.
# ══════════════════════════════════════════════════════════════════════════════

find_sym_ident_disp:
	j	find_sym_ident_rs0

read_multi_expr:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	t0, 14624
	add	t0, s10, t0		# buf base (14624 offset in token area)
	sw	t0, 4(sp)
	li	t1, 0			# len written
rme_lp:
	addi	sp, sp, -12
	sw	t0, 0(sp)
	sw	t1, 4(sp)
	li	gp, 1
	j	read_token
read_token_rs1:
	lw	t0, 0(sp)
	lw	t1, 4(sp)
	addi	sp, sp, 12
	bnez	s0, rme_chk_eol
	beqz	t1, rme_bad		# empty on first iter
	j	rme_eval		# EOT finishes
rme_chk_eol:
	lw	t2, TB_EOL(s10)		# eol_flag
	beqz	t2, rme_accept
	beqz	t1, rme_bad
	li	t2, 1
	sw	t2, TB_PUSHBACK(s10)		# pushback
	j	rme_eval
rme_accept:
	add	t2, t0, t1
	mv	t3, s10
	mv	t4, s0
rme_cp:
	beqz	t4, rme_cpd
	lbu	t5, 0(t3)
	sb	t5, 0(t2)
	addi	t2, t2, 1
	addi	t3, t3, 1
	addi	t4, t4, -1
	addi	t1, t1, 1
	j	rme_cp
rme_cpd:
	li	t2, 128
	bge	t1, t2, rme_bad
	j	rme_lp
rme_eval:
	mv	a0, t0
	add	a1, t0, t1
	li	gp, 2
	j	eval_expr
eval_expr_rs2:
	bne	a2, a1, rme_bad
	lw	gp, 0(sp)
	addi	sp, sp, 8
	j	read_multi_expr_disp
rme_bad:
	li	a0, 5
	j	halt_err

# ══════════════════════════════════════════════════════════════════════════════
#  Operand readers
# ══════════════════════════════════════════════════════════════════════════════

read_multi_expr_disp:
	bnez	gp, read_multi_expr_d1
	j	read_multi_expr_rs0
read_multi_expr_d1:
	addi	gp, gp, -1
	j	read_multi_expr_rs1

read_reg_op:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 2
	j	read_token
read_token_rs2:
	mv	a0, s10
	mv	a1, s0
	li	gp, 1
	j	parse_reg
parse_reg_rs1:
	li	t0, -1
	bne	a0, t0, rro_ok
	li	a0, 8			# E08: bad register
	j	halt_err
rro_ok:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	read_reg_op_disp

read_reg_op_disp:
	bnez	gp, read_reg_op_d1
	j	read_reg_op_rs0
read_reg_op_d1:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d2
	j	read_reg_op_rs1
read_reg_op_d2:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d3
	j	read_reg_op_rs2
read_reg_op_d3:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d4
	j	read_reg_op_rs3
read_reg_op_d4:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d5
	j	read_reg_op_rs4
read_reg_op_d5:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d6
	j	read_reg_op_rs5
read_reg_op_d6:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d7
	j	read_reg_op_rs6
read_reg_op_d7:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d8
	j	read_reg_op_rs7
read_reg_op_d8:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d9
	j	read_reg_op_rs8
read_reg_op_d9:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d10
	j	read_reg_op_rs9
read_reg_op_d10:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d11
	j	read_reg_op_rs10
read_reg_op_d11:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d12
	j	read_reg_op_rs11
read_reg_op_d12:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d13
	j	read_reg_op_rs12
read_reg_op_d13:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d14
	j	error_halt
read_reg_op_d14:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d15
	j	read_reg_op_rs14
read_reg_op_d15:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d16
	j	read_reg_op_rs15
read_reg_op_d16:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d17
	j	read_reg_op_rs16
read_reg_op_d17:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d18
	j	read_reg_op_rs17
read_reg_op_d18:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d19
	j	read_reg_op_rs18
read_reg_op_d19:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d20
	j	read_reg_op_rs19
read_reg_op_d20:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d21
	j	read_reg_op_rs20
read_reg_op_d21:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d22
	j	read_reg_op_rs21
read_reg_op_d22:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d23
	j	read_reg_op_rs22
read_reg_op_d23:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d24
	j	read_reg_op_rs23
read_reg_op_d24:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d25
	j	read_reg_op_rs24
read_reg_op_d25:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d26
	j	read_reg_op_rs25
read_reg_op_d26:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d27
	j	read_reg_op_rs26
read_reg_op_d27:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d28
	j	read_reg_op_rs27
read_reg_op_d28:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d29
	j	read_reg_op_rs28
read_reg_op_d29:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d30
	j	read_reg_op_rs29
read_reg_op_d30:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d31
	j	read_reg_op_rs30
read_reg_op_d31:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d32
	j	read_reg_op_rs31
read_reg_op_d32:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d33
	j	read_reg_op_rs32
read_reg_op_d33:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d34
	j	read_reg_op_rs33
read_reg_op_d34:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d35
	j	read_reg_op_rs34
read_reg_op_d35:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d36
	j	read_reg_op_rs35
read_reg_op_d36:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d37
	j	read_reg_op_rs36
read_reg_op_d37:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d38
	j	read_reg_op_rs37
read_reg_op_d38:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d39
	j	read_reg_op_rs38
read_reg_op_d39:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d40
	j	read_reg_op_rs39
read_reg_op_d40:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d41
	j	read_reg_op_rs40
read_reg_op_d41:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d42
	j	read_reg_op_rs41
read_reg_op_d42:
	addi	gp, gp, -1
	bnez	gp, read_reg_op_d43
	j	read_reg_op_rs42
read_reg_op_d43:
	j	read_reg_op_rs43

read_imm_op:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 3
	j	read_token
read_token_rs3:
	# If the tokenizer crossed a newline before collecting this token, the
	# token belongs to the next logical line.  Push it back and signal the
	# caller with a1=1 instead of running eval_expr on it — eval_expr on an
	# identifier that happens to be the next line's mnemonic would halt
	# with E17 (unresolved symbol) during the final fixup pass, which
	# bit `.word VAL  # trailing comment` as a previously documented bug.
	lw	t0, TB_EOL(s10)
	bnez	t0, rio_pushback
	mv	a0, s10
	add	a1, s10, s0
	li	gp, 3
	j	eval_expr
eval_expr_rs3:
	bne	a2, a1, rio_bad
	li	a1, 0			# normal return: a0 = value
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	read_imm_op_disp
rio_pushback:
	# Pushback the token so a subsequent read_token returns it unchanged.
	# Zero a0 so single-op callers that ignore a1 produce a harmless 0 imm
	# rather than whatever was in a0 from the previous iteration.
	li	t0, 1
	sw	t0, TB_PUSHBACK(s10)
	li	a0, 0
	li	a1, 1			# signal: no imm read (line ended first)
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	read_imm_op_disp
rio_bad:
	li	a0, 5
	j	halt_err

read_imm_op_disp:
	bnez	gp, read_imm_op_d1
	j	read_imm_op_rs0
read_imm_op_d1:
	addi	gp, gp, -1
	bnez	gp, read_imm_op_d2
	j	read_imm_op_rs1
read_imm_op_d2:
	addi	gp, gp, -1
	bnez	gp, read_imm_op_d3
	j	read_imm_op_rs2
read_imm_op_d3:
	addi	gp, gp, -1
	bnez	gp, read_imm_op_d4
	j	read_imm_op_rs3
read_imm_op_d4:
	addi	gp, gp, -1
	bnez	gp, read_imm_op_d5
	j	error_halt
read_imm_op_d5:
	addi	gp, gp, -1
	bnez	gp, read_imm_op_d6
	j	read_imm_op_rs5
read_imm_op_d6:
	addi	gp, gp, -1
	bnez	gp, read_imm_op_d7
	j	read_imm_op_rs6
read_imm_op_d7:
	addi	gp, gp, -1
	j	read_imm_op_rs7

read_mem_op:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 4
	j	read_token
read_token_rs4:
	mv	a0, s10
	mv	a1, s0
	li	gp, 0
	j	parse_mem
parse_mem_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	read_mem_op_disp

# read_br_target: a0=slot_type (0=B, 1=J)
#   Returns: a0 = offset (or 0 if label fixup recorded)
read_mem_op_disp:
	bnez	gp, read_mem_op_d1
	j	read_mem_op_rs0
read_mem_op_d1:
	addi	gp, gp, -1
	j	read_mem_op_rs1

read_br_target:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	sw	a0, 4(sp)		# slot_type
	li	gp, 5
	j	read_token
read_token_rs5:

	# Local label ref? (len=2, digit + 'f'/'b')
	li	t2, 2
	bne	s0, t2, rbt_not_local
	lbu	t0, 0(s10)
	li	t1, '0'
	blt	t0, t1, rbt_not_local
	li	t1, '9'+1
	bge	t0, t1, rbt_not_local
	lbu	t1, 1(s10)
	li	t2, 'f'
	beq	t1, t2, rbt_local
	li	t2, 'b'
	beq	t1, t2, rbt_local
	j	rbt_not_local

rbt_local:
	# Build local label name, record fixup
	addi	t3, t0, -'0'		# digit
	slli	t4, t3, 2
	add	t4, s10, t4
	lw	t5, TB_LLCNT(t4)		# counter[digit]
	li	t2, 'f'
	bne	t1, t2, rbt_local_b
	addi	t5, t5, 1		# forward: seq = counter+1
	j	rbt_local_build
rbt_local_b:
	beqz	t5, rbt_bad		# backward with no prior def
rbt_local_build:
	addi	sp, sp, -16
	mv	a0, t3			# digit
	mv	a1, t5			# seq
	mv	a2, sp			# buf
	li	gp, 0
	j	build_local_name
build_local_name_rs0:
	mv	a0, sp			# name_ptr
	li	a1, 9			# name_len
	sub	a2, s2, s1		# patch_offset
	lw	a3, 20(sp)		# slot_type (at 4(sp) before 16-push = 20)
	bnez	a3, rbt_local_j
	# B-type → trampoline: fixup at offset+4 (JAL)
	addi	a2, a2, 4
	li	a3, 1			# J-type
rbt_local_j:
	li	gp, 0
	j	record_fixup_arg
record_fixup_arg_rs0:
	addi	sp, sp, 16
	li	a0, 0
	j	rbt_done

rbt_not_local:
	# Letter or underscore → label
	lbu	t0, 0(s10)
	li	t1, 'A'
	blt	t0, t1, rbt_chk_us
	li	t1, 'Z'+1
	blt	t0, t1, rbt_label
	li	t1, 'a'
	blt	t0, t1, rbt_chk_us
	li	t1, 'z'+1
	blt	t0, t1, rbt_label
rbt_chk_us:
	li	t1, '_'
	beq	t0, t1, rbt_label
	# Must be numeric immediate
	mv	a0, s10
	mv	a1, s0
	li	gp, 2
	j	parse_imm
parse_imm_rs2:
	j	rbt_done

rbt_label:
	lw	a1, 4(sp)		# slot_type
	bnez	a1, rbt_label_j		# J-type: record as-is
	# B-type → trampoline: fixup at offset+4
	sub	a0, s2, s1
	addi	a0, a0, 4
	li	a1, 1			# J-type
	li	gp, 0
	j	record_fixup
record_fixup_rs0:
	li	a0, 0
	j	rbt_done
rbt_label_j:
	sub	a0, s2, s1		# patch_offset
	li	gp, 1
	j	record_fixup
record_fixup_rs1:
	li	a0, 0
rbt_done:
	lw	gp, 0(sp)
	addi	sp, sp, 8
	j	read_br_target_disp
rbt_bad:
	li	a0, 10			# E10: bad branch target
	j	halt_err

# ══════════════════════════════════════════════════════════════════════════════
#  Label / Symbol / Fixup
# ══════════════════════════════════════════════════════════════════════════════

# define_label: token "name:" in buf, length s0. Strip colon, store in symtab.
read_br_target_disp:
	bnez	gp, read_br_target_d1
	j	read_br_target_rs0
read_br_target_d1:
	addi	gp, gp, -1
	bnez	gp, read_br_target_d2
	j	read_br_target_rs1
read_br_target_d2:
	addi	gp, gp, -1
	bnez	gp, read_br_target_d3
	j	read_br_target_rs2
read_br_target_d3:
	addi	gp, gp, -1
	bnez	gp, read_br_target_d4
	j	read_br_target_rs3
read_br_target_d4:
	addi	gp, gp, -1
	bnez	gp, read_br_target_d5
	j	read_br_target_rs4
read_br_target_d5:
	addi	gp, gp, -1
	bnez	gp, read_br_target_d6
	j	read_br_target_rs5
read_br_target_d6:
	addi	gp, gp, -1
	bnez	gp, read_br_target_d7
	j	read_br_target_rs6
read_br_target_d7:
	addi	gp, gp, -1
	bnez	gp, read_br_target_d8
	j	read_br_target_rs7
read_br_target_d8:
	addi	gp, gp, -1
	bnez	gp, read_br_target_d9
	j	read_br_target_rs8
read_br_target_d9:
	addi	gp, gp, -1
	bnez	gp, read_br_target_d10
	j	read_br_target_rs9
read_br_target_d10:
	addi	gp, gp, -1
	bnez	gp, read_br_target_d11
	j	read_br_target_rs10

read_br_target_d11:
	j	read_br_target_rs11
define_label:
	li	t0, 33			# max s0 = 32 (31 chars + colon)
	blt	s0, t0, dl_ok
	li	a0, 11			# E11: label too long
	j	halt_err
dl_ok:
	addi	t0, s0, -1		# position of ':'
	add	t1, s10, t0
	sb	zero, 0(t1)		# zero out colon

	# Duplicate check
	addi	sp, sp, -8
	sw	gp, 0(sp)
	mv	a0, s10
	addi	a1, s0, -1
	li	gp, 1
	j	find_sym
find_sym_rs1:
	lw	gp, 0(sp)
	addi	sp, sp, 8
	beqz	a2, dl_new		# not found → OK
	li	a0, 12			# E12: duplicate label
	j	halt_err
dl_new:
	# Zero 40 bytes at s4
	mv	t2, s4
	addi	t3, s4, 40
dl_zero:
	sw	zero, 0(t2)
	addi	t2, t2, 4
	bne	t2, t3, dl_zero
	# Copy name (32 bytes max, buffer already zero-padded)
	mv	t2, s10
	mv	t3, s4
	addi	t0, s0, -1		# name len (without colon)
dl_cp:
	beqz	t0, dl_store
	lbu	t5, 0(t2)
	sb	t5, 0(t3)
	addi	t2, t2, 1
	addi	t3, t3, 1
	addi	t0, t0, -1
	j	dl_cp
dl_store:
	sub	t5, s2, s1		# output offset
	sw	t5, 32(s4)		# value
	sw	zero, 36(s4)		# kind = 0 (code label)
	addi	s4, s4, 40
	j	define_label_disp

# find_sym: a0=name_ptr, a1=name_len → a0=value, a1=kind, a2=1 if found (0=not)
define_label_disp:
	bnez	gp, define_label_d1
	j	define_label_rs0
define_label_d1:
	addi	gp, gp, -1
	j	define_label_rs1

find_sym:
	mv	t0, s3			# symtab scan ptr
fs_lp:
	beq	t0, s4, fs_notfound
	# Compare name: must match all 32 bytes (entry is zero-padded)
	# But we only compare a1 bytes then check remaining are zero
	mv	t2, a0			# name ptr
	mv	t3, t0			# entry ptr
	mv	t4, a1			# remaining
fs_cmp:
	beqz	t4, fs_pad
	lbu	t5, 0(t2)
	lbu	t6, 0(t3)
	bne	t5, t6, fs_next
	addi	t2, t2, 1
	addi	t3, t3, 1
	addi	t4, t4, -1
	j	fs_cmp
fs_pad:
	# Check remaining bytes in entry name are zero
	li	t4, 32
	sub	t4, t4, a1
	beqz	t4, fs_found
fs_pad_lp:
	lbu	t5, 0(t3)
	bnez	t5, fs_next
	addi	t3, t3, 1
	addi	t4, t4, -1
	bnez	t4, fs_pad_lp
fs_found:
	lw	a0, 32(t0)		# value
	lw	a1, 36(t0)		# kind
	li	a2, 1			# found
	j	find_sym_disp
fs_next:
	addi	t0, t0, 40
	j	fs_lp
fs_notfound:
	li	a2, 0
	j	find_sym_disp

# record_fixup: a0=patch_offset, a1=slot_type. Name from token buf s10/s0.
find_sym_disp:
	bnez	gp, find_sym_d1
	j	find_sym_rs0
find_sym_d1:
	addi	gp, gp, -1
	j	find_sym_rs1

record_fixup:
	mv	a2, a0
	mv	a3, a1
	mv	a0, s10
	mv	a1, s0
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 1
	j	record_fixup_arg
record_fixup_arg_rs1:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	record_fixup_disp

# record_fixup_arg: a0=name_ptr, a1=name_len, a2=patch_offset, a3=slot_type
record_fixup_disp:
	bnez	gp, record_fixup_d1
	j	record_fixup_rs0
record_fixup_d1:
	addi	gp, gp, -1
	j	record_fixup_rs1

record_fixup_arg:
	# Zero 40 bytes at s8
	mv	t1, s8
	addi	t5, s8, 40
rfa_zero:
	sw	zero, 0(t1)
	addi	t1, t1, 4
	bne	t1, t5, rfa_zero
	# Copy name
	mv	t1, a0
	mv	t2, s8
	mv	t3, a1
rfa_cp:
	beqz	t3, rfa_fields
	lbu	t5, 0(t1)
	sb	t5, 0(t2)
	addi	t1, t1, 1
	addi	t2, t2, 1
	addi	t3, t3, -1
	j	rfa_cp
rfa_fields:
	sw	a2, 32(s8)		# patch_offset
	sw	a3, 36(s8)		# slot_type
	addi	s8, s8, 40
	j	record_fixup_arg_disp

# ══════════════════════════════════════════════════════════════════════════════
#  Local Labels
# ══════════════════════════════════════════════════════════════════════════════

# build_local_name: a0=digit, a1=seq, a2=buf_ptr
#   Writes 9-byte name ".Ldigitseq" zero-padded
record_fixup_arg_disp:
	bnez	gp, record_fixup_arg_d1
	j	record_fixup_arg_rs0
record_fixup_arg_d1:
	addi	gp, gp, -1
	bnez	gp, record_fixup_arg_d2
	j	record_fixup_arg_rs1
record_fixup_arg_d2:
	addi	gp, gp, -1
	bnez	gp, record_fixup_arg_d3
	j	record_fixup_arg_rs2
record_fixup_arg_d3:
	addi	gp, gp, -1
	j	record_fixup_arg_rs3

build_local_name:
	li	t0, '.'
	sb	t0, 0(a2)
	li	t0, 'L'
	sb	t0, 1(a2)
	addi	t0, a0, '0'
	sb	t0, 2(a2)
	# Write seq as decimal (up to 6 digits)
	addi	t0, a2, 3
	li	t1, 0			# digit count
	# Repeatedly divide by 10 (shift method), push digits
	addi	sp, sp, -24
	mv	t2, a1
bln_lp:
	li	t3, 10
	li	t4, 0			# quotient
bln_div:
	blt	t2, t3, bln_rem
	sub	t2, t2, t3
	addi	t4, t4, 1
	j	bln_div
bln_rem:
	addi	t5, t2, '0'
	add	t6, sp, t1
	sb	t5, 0(t6)		# push remainder
	addi	t1, t1, 1
	mv	t2, t4
	bnez	t2, bln_lp
	# Pop digits in reverse
bln_pop:
	addi	t1, t1, -1
	add	t6, sp, t1
	lbu	t5, 0(t6)
	sb	t5, 0(t0)
	addi	t0, t0, 1
	bnez	t1, bln_pop
	addi	sp, sp, 24
	# Zero-pad remaining
	addi	t1, a2, 9
bln_pad:
	bge	t0, t1, bln_done
	sb	zero, 0(t0)
	addi	t0, t0, 1
	j	bln_pad
bln_done:
	j	build_local_name_disp

# def_local_label: a0=digit. Increments counter, builds name, defines in symtab.
build_local_name_disp:
	bnez	gp, build_local_name_d1
	j	build_local_name_rs0
build_local_name_d1:
	addi	gp, gp, -1
	j	build_local_name_rs1

def_local_label:
	addi	sp, sp, -20
	sw	gp, 0(sp)
	slli	t0, a0, 2
	add	t0, s10, t0
	lw	t1, TB_LLCNT(t0)		# counter[digit]
	addi	t1, t1, 1
	sw	t1, TB_LLCNT(t0)		# counter[digit]++
	# Build name at sp+4
	mv	a1, t1			# seq
	addi	a2, sp, 4
	li	gp, 1
	j	build_local_name
build_local_name_rs1:
	# Copy to token buffer for define_label
	mv	t0, s10
	addi	t1, sp, 4
	li	t2, 9
dll_cp:
	lbu	t3, 0(t1)
	sb	t3, 0(t0)
	addi	t0, t0, 1
	addi	t1, t1, 1
	addi	t2, t2, -1
	bnez	t2, dll_cp
	# Zero rest of token buffer
	addi	t1, s10, 32
dll_z:
	beq	t0, t1, dll_def
	sb	zero, 0(t0)
	addi	t0, t0, 1
	j	dll_z
dll_def:
	# Add ':' and set s0 = 10 (name + colon)
	li	t0, ':'
	sb	t0, 9(s10)
	li	s0, 10
	li	gp, 1
	j	define_label
define_label_rs1:
	lw	gp, 0(sp)
	addi	sp, sp, 20
	j	def_local_label_disp

# ══════════════════════════════════════════════════════════════════════════════
#  Emit helpers
# ══════════════════════════════════════════════════════════════════════════════

def_local_label_disp:
	j	def_local_label_rs0

emit_word:
	sb	a0, 0(s2)
	srli	t5, a0, 8
	sb	t5, 1(s2)
	srli	t5, t5, 8
	sb	t5, 2(s2)
	srli	t5, t5, 8
	sb	t5, 3(s2)
	addi	s2, s2, 4
	j	emit_word_disp

# emit_u_inst: a0=opcode, a1=rd, a2=imm20 → emit U-type, tail-call emit_word
emit_word_disp:
	bnez	gp, emit_word_d1
	j	emit_word_rs0
emit_word_d1:
	addi	gp, gp, -1
	bnez	gp, emit_word_d2
	j	emit_word_rs1
emit_word_d2:
	addi	gp, gp, -1
	bnez	gp, emit_word_d3
	j	emit_word_rs2
emit_word_d3:
	addi	gp, gp, -1
	bnez	gp, emit_word_d4
	j	emit_word_rs3
emit_word_d4:
	addi	gp, gp, -1
	bnez	gp, emit_word_d5
	j	emit_word_rs4
emit_word_d5:
	addi	gp, gp, -1
	bnez	gp, emit_word_d6
	j	emit_word_rs5
emit_word_d6:
	addi	gp, gp, -1
	bnez	gp, emit_word_d7
	j	emit_word_rs6
emit_word_d7:
	addi	gp, gp, -1
	bnez	gp, emit_word_d8
	j	emit_word_rs7
emit_word_d8:
	addi	gp, gp, -1
	bnez	gp, emit_word_d9
	j	emit_word_rs8
emit_word_d9:
	addi	gp, gp, -1
	j	emit_word_rs9

emit_u_inst:
	# Range check: lui/auipc imm20 (in a2) must fit in either
	# 20-bit unsigned (0..0xFFFFF) or 20-bit signed
	# (-0x80000..0x7FFFF).  Their union is -0x80000..0xFFFFF.
	# Halts with E20 on overflow.
	addi	sp, sp, -4
	sw	t2, 0(sp)
	li	t2, 1048575		# 0xFFFFF
	bge	a2, t2, eui_chk_hi
	j	eui_chk_lo
eui_chk_hi:
	beq	a2, t2, eui_ok
	j	eui_err
eui_chk_lo:
	li	t2, -524288		# -0x80000
	bge	a2, t2, eui_ok
eui_err:
	lw	t2, 0(sp)
	addi	sp, sp, 4
	j	imm_range_u
eui_ok:
	lw	t2, 0(sp)
	addi	sp, sp, 4
	slli	t0, a2, 12
	andi	t1, a1, 0x1F
	slli	t1, t1, 7
	or	t0, t0, t1
	andi	t1, a0, 0x7F
	or	a0, t0, t1
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	emit_word
emit_word_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	emit_u_inst_disp

# emit_i_inst: a0=opcode, a1=rd, a2=rs1, a3=f3, a4=imm12
emit_u_inst_disp:
	bnez	gp, emit_u_inst_d1
	j	emit_u_inst_rs0
emit_u_inst_d1:
	addi	gp, gp, -1
	bnez	gp, emit_u_inst_d2
	j	emit_u_inst_rs1
emit_u_inst_d2:
	addi	gp, gp, -1
	bnez	gp, emit_u_inst_d3
	j	emit_u_inst_rs2
emit_u_inst_d3:
	addi	gp, gp, -1
	bnez	gp, emit_u_inst_d4
	j	emit_u_inst_rs3
emit_u_inst_d4:
	addi	gp, gp, -1
	bnez	gp, emit_u_inst_d5
	j	error_halt
emit_u_inst_d5:
	addi	gp, gp, -1
	j	error_halt

emit_i_inst:
	# Range check: imm (a4) must fit in the instruction's immediate
	# field.  addi / slti / sltiu (f3 bit 2 = 0) require -2048..2047.
	# xori / ori / andi (f3 bit 2 = 1) sign-extend the imm in hardware,
	# but source code conventionally writes the raw 12-bit bit pattern
	# (e.g. `andi x, y, 0xFFF` = mask to -1), so for those we accept
	# the wider range -2048..4095.
	#
	# NOTE: we use explicit `li bound; bge/ble; j imm_range_i`
	# sequences rather than `bne reg,reg,label` to dodge a
	# branch-relaxation quirk that was observed to mis-resolve
	# long-distance B-type label branches in earlier attempts.
	addi	sp, sp, -4
	sw	t2, 0(sp)		# save t2 (scratch)
	andi	t2, a3, 4
	bnez	t2, eii_bitwise
	# ── arith path: -2048 ≤ a4 ≤ 2047 ──
	li	t2, 2047
	bge	a4, t2, eii_chk_arith_hi	# a4 >= 2047 → check equal
	j	eii_chk_arith_lo
eii_chk_arith_hi:
	beq	a4, t2, eii_range_ok		# a4 == 2047 → ok
	j	imm_range_err
eii_chk_arith_lo:
	li	t2, -2048
	bge	a4, t2, eii_range_ok		# a4 >= -2048 → ok
	j	imm_range_err
eii_bitwise:
	# ── bitwise path: -2048 ≤ a4 ≤ 4095 ──
	li	t2, 4095
	bge	a4, t2, eii_chk_bw_hi
	j	eii_chk_bw_lo
eii_chk_bw_hi:
	beq	a4, t2, eii_range_ok
	j	imm_range_err
eii_chk_bw_lo:
	li	t2, -2048
	bge	a4, t2, eii_range_ok
	j	imm_range_err
imm_range_err:
	lw	t2, 0(sp)
	addi	sp, sp, 4
	j	imm_range_i
eii_range_ok:
	lw	t2, 0(sp)
	addi	sp, sp, 4
	slli	t0, a4, 20
	andi	t1, a2, 0x1F
	slli	t1, t1, 15
	or	t0, t0, t1
	andi	t1, a3, 0x7
	slli	t1, t1, 12
	or	t0, t0, t1
	andi	t1, a1, 0x1F
	slli	t1, t1, 7
	or	t0, t0, t1
	andi	t1, a0, 0x7F
	or	a0, t0, t1
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 1
	j	emit_word
emit_word_rs1:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	emit_i_inst_disp

# emit_r_inst: a0=opcode, a1=rd, a2=rs1, a3=rs2, a4=f3, a5=f7
emit_i_inst_disp:
	bnez	gp, emit_i_inst_d1
	j	emit_i_inst_rs0
emit_i_inst_d1:
	addi	gp, gp, -1
	bnez	gp, emit_i_inst_d2
	j	emit_i_inst_rs1
emit_i_inst_d2:
	addi	gp, gp, -1
	bnez	gp, emit_i_inst_d3
	j	emit_i_inst_rs2
emit_i_inst_d3:
	addi	gp, gp, -1
	bnez	gp, emit_i_inst_d4
	j	error_halt
emit_i_inst_d4:
	addi	gp, gp, -1
	bnez	gp, emit_i_inst_d5
	j	emit_i_inst_rs4
emit_i_inst_d5:
	addi	gp, gp, -1
	bnez	gp, emit_i_inst_d6
	j	emit_i_inst_rs5
emit_i_inst_d6:
	addi	gp, gp, -1
	bnez	gp, emit_i_inst_d7
	j	emit_i_inst_rs6
emit_i_inst_d7:
	addi	gp, gp, -1
	bnez	gp, emit_i_inst_d8
	j	error_halt
emit_i_inst_d8:
	addi	gp, gp, -1
	bnez	gp, emit_i_inst_d9
	j	emit_i_inst_rs8
emit_i_inst_d9:
	addi	gp, gp, -1
	bnez	gp, emit_i_inst_d10
	j	emit_i_inst_rs9
emit_i_inst_d10:
	addi	gp, gp, -1
	bnez	gp, emit_i_inst_d11
	j	emit_i_inst_rs10
emit_i_inst_d11:
	addi	gp, gp, -1
	bnez	gp, emit_i_inst_d12
	j	error_halt
emit_i_inst_d12:
	addi	gp, gp, -1
	bnez	gp, emit_i_inst_d13
	j	error_halt
emit_i_inst_d13:
	addi	gp, gp, -1
	bnez	gp, emit_i_inst_d14
	j	emit_i_inst_rs13
emit_i_inst_d14:
	addi	gp, gp, -1
	bnez	gp, emit_i_inst_d15
	j	emit_i_inst_rs14
emit_i_inst_d15:
	addi	gp, gp, -1
	bnez	gp, emit_i_inst_d16
	j	emit_i_inst_rs15
emit_i_inst_d16:
	addi	gp, gp, -1
	j	emit_i_inst_rs16

emit_r_inst:
	andi	t1, a5, 0x7F
	slli	t0, t1, 25
	andi	t1, a3, 0x1F
	slli	t1, t1, 20
	or	t0, t0, t1
	andi	t1, a2, 0x1F
	slli	t1, t1, 15
	or	t0, t0, t1
	andi	t1, a4, 0x7
	slli	t1, t1, 12
	or	t0, t0, t1
	andi	t1, a1, 0x1F
	slli	t1, t1, 7
	or	t0, t0, t1
	andi	t1, a0, 0x7F
	or	a0, t0, t1
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 2
	j	emit_word
emit_word_rs2:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	emit_r_inst_disp

# emit_s_inst: a0=opcode, a1=rs1, a2=rs2, a3=f3, a4=imm12
emit_r_inst_disp:
	bnez	gp, emit_r_inst_d1
	j	emit_r_inst_rs0
emit_r_inst_d1:
	addi	gp, gp, -1
	bnez	gp, emit_r_inst_d2
	j	emit_r_inst_rs1
emit_r_inst_d2:
	addi	gp, gp, -1
	bnez	gp, emit_r_inst_d3
	j	emit_r_inst_rs2
emit_r_inst_d3:
	addi	gp, gp, -1
	bnez	gp, emit_r_inst_d4
	j	emit_r_inst_rs3
emit_r_inst_d4:
	addi	gp, gp, -1
	j	emit_r_inst_rs4

emit_s_inst:
	# Range check: offset (a4) must fit in 12-bit signed (-2048..2047).
	# Store offsets are always signed, never bitwise.
	addi	sp, sp, -4
	sw	t2, 0(sp)
	li	t2, 2047
	bge	a4, t2, esi_chk_hi
	j	esi_chk_lo
esi_chk_hi:
	beq	a4, t2, esi_ok
	j	esi_err
esi_chk_lo:
	li	t2, -2048
	bge	a4, t2, esi_ok
esi_err:
	lw	t2, 0(sp)
	addi	sp, sp, 4
	j	imm_range_i
esi_ok:
	lw	t2, 0(sp)
	addi	sp, sp, 4
	srli	t1, a4, 5
	andi	t1, t1, 0x7F
	slli	t0, t1, 25
	andi	t1, a2, 0x1F
	slli	t1, t1, 20
	or	t0, t0, t1
	andi	t1, a1, 0x1F
	slli	t1, t1, 15
	or	t0, t0, t1
	andi	t1, a3, 0x7
	slli	t1, t1, 12
	or	t0, t0, t1
	andi	t1, a4, 0x1F
	slli	t1, t1, 7
	or	t0, t0, t1
	andi	t1, a0, 0x7F
	or	a0, t0, t1
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 3
	j	emit_word
emit_word_rs3:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	emit_s_inst_disp

# emit_b_inst: a0=opcode(0x63), a1=rs1, a2=rs2, a3=f3, a4=imm
emit_s_inst_disp:
	bnez	gp, emit_s_inst_d1
	j	emit_s_inst_rs0
emit_s_inst_d1:
	addi	gp, gp, -1
	bnez	gp, emit_s_inst_d2
	j	emit_s_inst_rs1
emit_s_inst_d2:
	addi	gp, gp, -1
	j	emit_s_inst_rs2

emit_b_inst:
	# Range check: B-type offset (in a4) must fit in 13-bit signed
	# (-4096..4094) AND be even.  Halts with E21 on overflow.
	addi	sp, sp, -4
	sw	t2, 0(sp)
	# even check
	andi	t2, a4, 1
	bnez	t2, ebi_err
	# upper bound: a4 ≤ 4094
	li	t2, 4094
	bge	a4, t2, ebi_chk_hi
	j	ebi_chk_lo
ebi_chk_hi:
	beq	a4, t2, ebi_ok
	j	ebi_err
ebi_chk_lo:
	li	t2, -4096
	bge	a4, t2, ebi_ok
ebi_err:
	lw	t2, 0(sp)
	addi	sp, sp, 4
	j	imm_range_b
ebi_ok:
	lw	t2, 0(sp)
	addi	sp, sp, 4
	srli	t0, a4, 12
	andi	t0, t0, 1
	slli	t0, t0, 31
	srli	t1, a4, 5
	andi	t1, t1, 0x3F
	slli	t1, t1, 25
	or	t0, t0, t1
	andi	t1, a2, 0x1F
	slli	t1, t1, 20
	or	t0, t0, t1
	andi	t1, a1, 0x1F
	slli	t1, t1, 15
	or	t0, t0, t1
	andi	t1, a3, 0x7
	slli	t1, t1, 12
	or	t0, t0, t1
	srli	t1, a4, 1
	andi	t1, t1, 0xF
	slli	t1, t1, 8
	or	t0, t0, t1
	srli	t1, a4, 11
	andi	t1, t1, 1
	slli	t1, t1, 7
	or	t0, t0, t1
	andi	t1, a0, 0x7F
	or	a0, t0, t1
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 4
	j	emit_word
emit_word_rs4:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	emit_b_inst_disp

# emit_j_inst: a0=opcode(0x6F), a1=rd, a2=imm
emit_b_inst_disp:
	j	emit_b_inst_rs0

emit_j_inst:
	# Range check: J-type offset (in a2) must fit in 21-bit signed
	# (-1048576..1048574) AND be even.  Halts with E22 on overflow.
	addi	sp, sp, -4
	sw	t2, 0(sp)
	# even check
	andi	t2, a2, 1
	bnez	t2, eji_err
	li	t2, 1048574		# 0xFFFFE
	bge	a2, t2, eji_chk_hi
	j	eji_chk_lo
eji_chk_hi:
	beq	a2, t2, eji_ok
	j	eji_err
eji_chk_lo:
	li	t2, -1048576		# -0x100000
	bge	a2, t2, eji_ok
eji_err:
	lw	t2, 0(sp)
	addi	sp, sp, 4
	j	imm_range_j
eji_ok:
	lw	t2, 0(sp)
	addi	sp, sp, 4
	srli	t0, a2, 20
	andi	t0, t0, 1
	slli	t0, t0, 31
	srli	t1, a2, 1
	li	t3, 0x3FF
	and	t1, t1, t3
	slli	t1, t1, 21
	or	t0, t0, t1
	srli	t1, a2, 11
	andi	t1, t1, 1
	slli	t1, t1, 20
	or	t0, t0, t1
	srli	t1, a2, 12
	andi	t1, t1, 0xFF
	slli	t1, t1, 12
	or	t0, t0, t1
	andi	t1, a1, 0x1F
	slli	t1, t1, 7
	or	t0, t0, t1
	andi	t1, a0, 0x7F
	or	a0, t0, t1
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 5
	j	emit_word
emit_word_rs5:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	emit_j_inst_disp

# emit_branch_auto: emits relaxed branch (inverted + JAL trampoline)
# when label target (a4=0), or compact B-type when numeric (a4!=0).
# a0=0x63, a1=rs1, a2=rs2, a3=f3, a4=offset
# For label targets, the fixup was already recorded as J-type at offset+4.
emit_branch_auto:
	bnez	a4, emit_b_inst		# numeric → compact
	# Always relax: inverted branch +8, then JAL placeholder
	addi	sp, sp, -4
	sw	gp, 0(sp)
	xori	a3, a3, 1		# invert condition
	li	a4, 8			# branch over JAL
	li	gp, 0
	j	emit_b_inst
emit_b_inst_rs0:
	li	a0, 0x6F		# JAL x0, 0 (placeholder)
	li	gp, 6
	j	emit_word
emit_word_rs6:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	emit_j_inst_disp

# ══════════════════════════════════════════════════════════════════════════════
#  rec_pcrel_pair: records 2 fixups for auipc+addi/jalr pair
# ══════════════════════════════════════════════════════════════════════════════

emit_j_inst_disp:
	bnez	gp, emit_j_inst_d1
	j	emit_j_inst_rs0
emit_j_inst_d1:
	addi	gp, gp, -1
	j	emit_j_inst_rs1

rec_pcrel_pair:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 6
	j	read_token
read_token_rs6:
	# Record U_hi20_pcrel fixup for auipc
	mv	a0, s10
	mv	a1, s0
	sub	a2, s2, s1
	li	a3, 7			# U_hi20_pcrel
	li	gp, 2
	j	record_fixup_arg
record_fixup_arg_rs2:
	# Record I_lo12_pcrel_prev fixup for addi/jalr
	mv	a0, s10
	mv	a1, s0
	sub	a2, s2, s1
	addi	a2, a2, 4
	li	a3, 8			# I_lo12_pcrel_prev
	li	gp, 3
	j	record_fixup_arg
record_fixup_arg_rs3:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	rec_pcrel_pair_disp

# ══════════════════════════════════════════════════════════════════════════════
#  Dispatch: a0=class, a1=f3, a2=f7
# ══════════════════════════════════════════════════════════════════════════════

rec_pcrel_pair_disp:
	bnez	gp, rec_pcrel_pair_d1
	j	rec_pcrel_pair_rs0
rec_pcrel_pair_d1:
	addi	gp, gp, -1
	bnez	gp, rec_pcrel_pair_d2
	j	error_halt
rec_pcrel_pair_d2:
	addi	gp, gp, -1
	j	error_halt

dispatch:
	li	t0, 1
	bne	a0, t0, dispatch_cd0_do_r
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_r
do_r_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
dispatch_cd0_do_r:
	li	t0, 2
	bne	a0, t0, dispatch_cd0_do_i_arith
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_i_arith
do_i_arith_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
dispatch_cd0_do_i_arith:
	li	t0, 3
	bne	a0, t0, dispatch_cd0_do_i_shift
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_i_shift
do_i_shift_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
dispatch_cd0_do_i_shift:
	li	t0, 4
	bne	a0, t0, dispatch_cd0_do_i_load
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_i_load
do_i_load_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
dispatch_cd0_do_i_load:
	li	t0, 5
	bne	a0, t0, dispatch_cd0_do_s
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_s
do_s_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
dispatch_cd0_do_s:
	li	t0, 6
	bne	a0, t0, dispatch_cd0_do_b
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_b
do_b_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
dispatch_cd0_do_b:
	li	t0, 7
	bne	a0, t0, dispatch_cd0_do_u_lui
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_u_lui
do_u_lui_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
dispatch_cd0_do_u_lui:
	li	t0, 8
	bne	a0, t0, dispatch_cd0_do_u_auipc
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_u_auipc
do_u_auipc_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
dispatch_cd0_do_u_auipc:
	li	t0, 9
	bne	a0, t0, dispatch_cd0_do_j_jal
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_j_jal
do_j_jal_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
dispatch_cd0_do_j_jal:
	# Pseudos — use bne+j trampolines for far targets
	li	t0, 11
	bne	a0, t0, d_12
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_li
do_ps_li_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_12:
	li	t0, 12
	bne	a0, t0, d_13
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_mv
do_ps_mv_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_13:
	li	t0, 13
	bne	a0, t0, d_14
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_j
do_ps_j_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_14:
d_15:
	li	t0, 15
	bne	a0, t0, d_16
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_beqz
do_ps_beqz_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_16:
	li	t0, 16
	bne	a0, t0, d_17
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_bnez
do_ps_bnez_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_17:
	li	t0, 17
	bne	a0, t0, d_19
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_equ
do_ps_equ_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_19:
	li	t0, 19
	bne	a0, t0, d_21
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_byte
do_ps_byte_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_21:
	li	t0, 21
	bne	a0, t0, d_22
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_word
do_ps_word_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_22:
	li	t0, 22
	bne	a0, t0, d_24
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_ascii
do_ps_ascii_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_24:
	li	t0, 24
	bne	a0, t0, d_28
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_zero
do_ps_zero_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_28:
	li	t0, 28
	bne	a0, t0, d_29
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_lla
do_ps_lla_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_29:
d_30:
d_31:
	li	t0, 31
	bne	a0, t0, d_32
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_nop
do_ps_nop_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_32:
	li	t0, TOK_MAX
	bne	a0, t0, d_33
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_neg
do_ps_neg_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_33:
	li	t0, 33
	bne	a0, t0, d_34
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_not
do_ps_not_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_34:
	li	t0, 34
	bne	a0, t0, d_35
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_seqz
do_ps_seqz_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_35:
	li	t0, 35
	bne	a0, t0, d_36
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_snez
do_ps_snez_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_36:
	li	t0, 36
	bne	a0, t0, d_37
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_sltz
do_ps_sltz_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_37:
	li	t0, 37
	bne	a0, t0, d_38
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_sgtz
do_ps_sgtz_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_38:
	li	t0, 38
	bne	a0, t0, d_39
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_bgt
do_ps_bgt_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_39:
	li	t0, 39
	bne	a0, t0, d_40
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_ble
do_ps_ble_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_40:
	li	t0, 40
	bne	a0, t0, d_41
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_bgtu
do_ps_bgtu_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_41:
	li	t0, 41
	bne	a0, t0, d_42
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_bleu
do_ps_bleu_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_42:
	li	t0, 42
	bne	a0, t0, d_43
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_prologue
do_ps_prologue_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_43:
	li	t0, 43
	bne	a0, t0, d_44
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_epilogue
do_ps_epilogue_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_44:
d_46:
	li	t0, 46
	bne	a0, t0, d_47
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_bltz
do_ps_bltz_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_47:
	li	t0, 47
	bne	a0, t0, d_48
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_bgez
do_ps_bgez_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_48:
	li	t0, 48
	bne	a0, t0, d_49
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_wfi
do_ps_wfi_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_49:
	li	t0, 49
	bne	a0, t0, d_err
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	do_ps_blez
do_ps_blez_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dispatch_disp
d_err:
	li	a0, 1
	j	halt_err

# ══════════════════════════════════════════════════════════════════════════════
#  Instruction Handlers
# ══════════════════════════════════════════════════════════════════════════════

# do_r: rd, rs1, rs2
dispatch_disp:
	j	dispatch_rs0

do_r:
	addi	sp, sp, -20
	sw	gp, 0(sp)
	sw	a1, 4(sp)
	sw	a2, 8(sp)
	li	gp, 0
	j	read_reg_op
read_reg_op_rs0:
	sw	a0, 12(sp)		# rd
	li	gp, 1
	j	read_reg_op
read_reg_op_rs1:
	sw	a0, 16(sp)		# rs1
	li	gp, 2
	j	read_reg_op
read_reg_op_rs2:
	mv	a3, a0			# rs2
	lw	a5, 8(sp)		# f7
	lw	a4, 4(sp)		# f3
	lw	a2, 16(sp)		# rs1
	lw	a1, 12(sp)		# rd
	li	a0, 0x33
	lw	gp, 0(sp)
	addi	sp, sp, 20
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	emit_r_inst
emit_r_inst_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_r_disp

# do_i_arith: rd, rs1, imm
do_r_disp:
	j	do_r_rs0

do_i_arith:
	addi	sp, sp, -16
	sw	gp, 0(sp)
	sw	a1, 4(sp)
	li	gp, 3
	j	read_reg_op
read_reg_op_rs3:
	sw	a0, 8(sp)		# rd
	li	gp, 4
	j	read_reg_op
read_reg_op_rs4:
	sw	a0, 12(sp)		# rs1
	li	gp, 0
	j	read_imm_op
read_imm_op_rs0:
	mv	a4, a0			# imm
	lw	a3, 4(sp)		# f3
	lw	a2, 12(sp)		# rs1
	lw	a1, 8(sp)		# rd
	li	a0, 0x13
	lw	gp, 0(sp)
	addi	sp, sp, 16
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	emit_i_inst
emit_i_inst_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_i_arith_disp

# do_i_shift: rd, rs1, shamt
do_i_arith_disp:
	j	do_i_arith_rs0

do_i_shift:
	addi	sp, sp, -20
	sw	gp, 0(sp)
	sw	a1, 4(sp)
	sw	a2, 8(sp)
	li	gp, 5
	j	read_reg_op
read_reg_op_rs5:
	sw	a0, 12(sp)		# rd
	li	gp, 6
	j	read_reg_op
read_reg_op_rs6:
	sw	a0, 16(sp)		# rs1
	li	gp, 1
	j	read_imm_op
read_imm_op_rs1:
	andi	a4, a0, 0x1F		# shamt
	lw	t0, 8(sp)		# f7
	andi	t0, t0, 0x7F
	slli	t0, t0, 5
	or	a4, a4, t0		# imm = (f7<<5)|shamt
	lw	a3, 4(sp)		# f3
	lw	a2, 16(sp)		# rs1
	lw	a1, 12(sp)		# rd
	li	a0, 0x13
	lw	gp, 0(sp)
	addi	sp, sp, 20
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 1
	j	emit_i_inst
emit_i_inst_rs1:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_i_shift_disp

# do_i_load: rd, imm(rs1)
do_i_shift_disp:
	j	do_i_shift_rs0

do_i_load:
	addi	sp, sp, -12
	sw	gp, 0(sp)
	sw	a1, 4(sp)
	li	gp, 7
	j	read_reg_op
read_reg_op_rs7:
	sw	a0, 8(sp)		# rd
	li	gp, 0		# a0=imm, a1=rs1
	j	read_mem_op
read_mem_op_rs0:
	mv	a4, a0			# imm
	mv	a2, a1			# rs1
	lw	a3, 4(sp)		# f3
	lw	a1, 8(sp)		# rd
	li	a0, 0x03
	lw	gp, 0(sp)
	addi	sp, sp, 12
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 2
	j	emit_i_inst
emit_i_inst_rs2:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_i_load_disp

# do_s: rs2, imm(rs1)
do_i_load_disp:
	j	do_i_load_rs0

do_s:
	addi	sp, sp, -12
	sw	gp, 0(sp)
	sw	a1, 4(sp)
	li	gp, 8
	j	read_reg_op
read_reg_op_rs8:
	sw	a0, 8(sp)		# rs2
	li	gp, 1		# a0=imm, a1=rs1
	j	read_mem_op
read_mem_op_rs1:
	mv	a4, a0			# imm
	mv	a1, a1			# rs1
	lw	a2, 8(sp)		# rs2
	lw	a3, 4(sp)		# f3
	li	a0, 0x23
	lw	gp, 0(sp)
	addi	sp, sp, 12
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	emit_s_inst
emit_s_inst_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_s_disp

# do_b: rs1, rs2, target
do_s_disp:
	j	do_s_rs0

do_b:
	addi	sp, sp, -16
	sw	gp, 0(sp)
	sw	a1, 4(sp)
	li	gp, 9
	j	read_reg_op
read_reg_op_rs9:
	sw	a0, 8(sp)		# rs1
	li	gp, 10
	j	read_reg_op
read_reg_op_rs10:
	sw	a0, 12(sp)		# rs2
	li	a0, 0			# slot_type B
	li	gp, 0
	j	read_br_target
read_br_target_rs0:
	mv	a4, a0			# offset
	lw	a3, 4(sp)		# f3
	lw	a1, 8(sp)		# rs1
	lw	a2, 12(sp)		# rs2
	li	a0, 0x63
	lw	gp, 0(sp)
	addi	sp, sp, 16
	j	emit_branch_auto

# do_u_lui: rd, imm
do_u_lui:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	gp, 11
	j	read_reg_op
read_reg_op_rs11:
	sw	a0, 4(sp)
	li	gp, 2
	j	read_imm_op
read_imm_op_rs2:
	mv	a2, a0
	lw	a1, 4(sp)
	li	a0, 0x37
	lw	gp, 0(sp)
	addi	sp, sp, 8
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	emit_u_inst
emit_u_inst_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_u_lui_disp

# do_u_auipc: rd, imm
do_u_lui_disp:
	j	do_u_lui_rs0

do_u_auipc:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	gp, 12
	j	read_reg_op
read_reg_op_rs12:
	sw	a0, 4(sp)
	li	gp, 3
	j	read_imm_op
read_imm_op_rs3:
	mv	a2, a0
	lw	a1, 4(sp)
	li	a0, 0x17
	lw	gp, 0(sp)
	addi	sp, sp, 8
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 1
	j	emit_u_inst
emit_u_inst_rs1:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_u_auipc_disp

# do_j_jal: rd, target (or just target with rd=ra implied)
do_u_auipc_disp:
	j	do_u_auipc_rs0

do_j_jal:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	gp, 7
	j	read_token
read_token_rs7:
	mv	a0, s10
	mv	a1, s0
	li	gp, 2
	j	parse_reg
parse_reg_rs2:
	li	t0, -1
	bne	a0, t0, jal_have_rd
	# Not a register → default rd=ra, pushback
	li	a0, 1
	li	t0, 1
	sw	t0, TB_PUSHBACK(s10)
jal_have_rd:
	sw	a0, 4(sp)
	li	a0, 1			# slot_type J
	li	gp, 1
	j	read_br_target
read_br_target_rs1:
	mv	a2, a0			# offset
	lw	a1, 4(sp)		# rd
	li	a0, 0x6F
	lw	gp, 0(sp)
	addi	sp, sp, 8
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 0
	j	emit_j_inst
emit_j_inst_rs0:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_j_jal_disp

do_j_jal_disp:
	j	do_j_jal_rs0

# ══════════════════════════════════════════════════════════════════════════════
#  Pseudo Handlers
# ══════════════════════════════════════════════════════════════════════════════

do_ps_nop:
	li	a0, 0x00000013		# addi x0, x0, 0
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 7
	j	emit_word
emit_word_rs7:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_nop_disp

do_ps_nop_disp:
	j	do_ps_nop_rs0

do_ps_wfi:
	li	a0, 0x10500073		# wfi encoding
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 8
	j	emit_word
emit_word_rs8:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_wfi_disp

# li rd, imm
do_ps_wfi_disp:
	j	do_ps_wfi_rs0

do_ps_li:
	addi	sp, sp, -12
	sw	gp, 0(sp)
	li	gp, 14
	j	read_reg_op
read_reg_op_rs14:
	sw	a0, 4(sp)		# rd
	li	gp, 0
	j	read_multi_expr
read_multi_expr_rs0:
	sw	a0, 8(sp)		# imm
	# Check if fits in 12-bit signed
	lw	t0, 8(sp)
	li	t1, 2047
	bgt	t0, t1, li_two
	li	t1, -2048
	blt	t0, t1, li_two
	# Single addi rd, x0, imm
	mv	a4, t0
	li	a3, 0
	li	a2, 0
	lw	a1, 4(sp)
	li	a0, 0x13
	lw	gp, 0(sp)
	addi	sp, sp, 12
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 4
	j	emit_i_inst
emit_i_inst_rs4:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_li_disp
li_two:
	# lui rd, upper + addi rd, rd, lower
	lw	t0, 8(sp)
	li	t1, 0x800
	add	t2, t0, t1
	srai	t2, t2, 12		# upper20
	lw	a1, 4(sp)		# rd
	mv	a2, t2
	li	a0, 0x37		# lui
	li	gp, 2
	j	emit_u_inst
emit_u_inst_rs2:
	lw	t0, 8(sp)
	slli	t0, t0, 20
	srai	t0, t0, 20		# lower12
	mv	a4, t0
	li	a3, 0
	lw	a2, 4(sp)		# rs1=rd
	lw	a1, 4(sp)		# rd
	li	a0, 0x13		# addi
	lw	gp, 0(sp)
	addi	sp, sp, 12
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 5
	j	emit_i_inst
emit_i_inst_rs5:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_li_disp

# mv rd, rs → addi rd, rs, 0
do_ps_li_disp:
	j	do_ps_li_rs0

do_ps_mv:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	gp, 15
	j	read_reg_op
read_reg_op_rs15:
	sw	a0, 4(sp)		# rd
	li	gp, 16
	j	read_reg_op
read_reg_op_rs16:
	mv	a2, a0			# rs1
	lw	a1, 4(sp)		# rd
	li	a4, 0
	li	a3, 0
	li	a0, 0x13
	lw	gp, 0(sp)
	addi	sp, sp, 8
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 6
	j	emit_i_inst
emit_i_inst_rs6:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_mv_disp

# j target → jal x0, target
do_ps_mv_disp:
	j	do_ps_mv_rs0

do_ps_j:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	a0, 1			# slot_type J
	li	gp, 2
	j	read_br_target
read_br_target_rs2:
	mv	a2, a0
	li	a1, 0			# rd = x0
	li	a0, 0x6F
	lw	gp, 0(sp)
	addi	sp, sp, 4
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 1
	j	emit_j_inst
emit_j_inst_rs1:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_j_disp

do_ps_j_disp:
	j	do_ps_j_rs0

# beqz rs, target → beq rs, x0, target (always relaxed for labels)
do_ps_beqz:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	gp, 17
	j	read_reg_op
read_reg_op_rs17:
	sw	a0, 4(sp)		# rs1
	li	a0, 0			# slot_type B
	li	gp, 3
	j	read_br_target
read_br_target_rs3:
	mv	a4, a0
	lw	a1, 4(sp)		# rs1
	li	a2, 0			# rs2 = x0
	li	a3, 0			# f3 = beq
	li	a0, 0x63
	lw	gp, 0(sp)
	addi	sp, sp, 8
	j	emit_branch_auto

# bnez rs, target → bne rs, x0, target
do_ps_bnez:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	gp, 18
	j	read_reg_op
read_reg_op_rs18:
	sw	a0, 4(sp)
	li	a0, 0
	li	gp, 4
	j	read_br_target
read_br_target_rs4:
	mv	a4, a0
	lw	a1, 4(sp)
	li	a2, 0
	li	a3, 1			# f3 = bne
	li	a0, 0x63
	lw	gp, 0(sp)
	addi	sp, sp, 8
	j	emit_branch_auto

# neg rd, rs → sub rd, x0, rs
do_ps_neg:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	gp, 19
	j	read_reg_op
read_reg_op_rs19:
	sw	a0, 4(sp)
	li	gp, 20
	j	read_reg_op
read_reg_op_rs20:
	mv	a3, a0			# rs2
	li	a2, 0			# rs1 = x0
	lw	a1, 4(sp)		# rd
	li	a5, 0x20		# f7
	li	a4, 0			# f3
	li	a0, 0x33
	lw	gp, 0(sp)
	addi	sp, sp, 8
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 1
	j	emit_r_inst
emit_r_inst_rs1:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_neg_disp

# not rd, rs → xori rd, rs, -1
do_ps_neg_disp:
	j	do_ps_neg_rs0

do_ps_not:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	gp, 21
	j	read_reg_op
read_reg_op_rs21:
	sw	a0, 4(sp)
	li	gp, 22
	j	read_reg_op
read_reg_op_rs22:
	mv	a2, a0			# rs1
	lw	a1, 4(sp)		# rd
	li	a4, -1			# imm
	li	a3, 4			# f3 = xori
	li	a0, 0x13
	lw	gp, 0(sp)
	addi	sp, sp, 8
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 8
	j	emit_i_inst
emit_i_inst_rs8:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_not_disp

# seqz rd, rs → sltiu rd, rs, 1
do_ps_not_disp:
	j	do_ps_not_rs0

do_ps_seqz:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	gp, 23
	j	read_reg_op
read_reg_op_rs23:
	sw	a0, 4(sp)
	li	gp, 24
	j	read_reg_op
read_reg_op_rs24:
	mv	a2, a0
	lw	a1, 4(sp)
	li	a4, 1
	li	a3, 3			# sltiu
	li	a0, 0x13
	lw	gp, 0(sp)
	addi	sp, sp, 8
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 9
	j	emit_i_inst
emit_i_inst_rs9:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_seqz_disp

# snez rd, rs → sltu rd, x0, rs
do_ps_seqz_disp:
	j	do_ps_seqz_rs0

do_ps_snez:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	gp, 25
	j	read_reg_op
read_reg_op_rs25:
	sw	a0, 4(sp)
	li	gp, 26
	j	read_reg_op
read_reg_op_rs26:
	mv	a3, a0			# rs2
	li	a2, 0			# rs1 = x0
	lw	a1, 4(sp)
	li	a5, 0
	li	a4, 3			# sltu
	li	a0, 0x33
	lw	gp, 0(sp)
	addi	sp, sp, 8
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 2
	j	emit_r_inst
emit_r_inst_rs2:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_snez_disp

# sltz rd, rs → slt rd, rs, x0
do_ps_snez_disp:
	j	do_ps_snez_rs0

do_ps_sltz:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	gp, 27
	j	read_reg_op
read_reg_op_rs27:
	sw	a0, 4(sp)
	li	gp, 28
	j	read_reg_op
read_reg_op_rs28:
	mv	a2, a0			# rs1
	li	a3, 0			# rs2 = x0
	lw	a1, 4(sp)
	li	a5, 0
	li	a4, 2			# slt
	li	a0, 0x33
	lw	gp, 0(sp)
	addi	sp, sp, 8
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 3
	j	emit_r_inst
emit_r_inst_rs3:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_sltz_disp

# sgtz rd, rs → slt rd, x0, rs
do_ps_sltz_disp:
	j	do_ps_sltz_rs0

do_ps_sgtz:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	gp, 29
	j	read_reg_op
read_reg_op_rs29:
	sw	a0, 4(sp)
	li	gp, 30
	j	read_reg_op
read_reg_op_rs30:
	mv	a3, a0			# rs2
	li	a2, 0			# rs1 = x0
	lw	a1, 4(sp)
	li	a5, 0
	li	a4, 2			# slt
	li	a0, 0x33
	lw	gp, 0(sp)
	addi	sp, sp, 8
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 4
	j	emit_r_inst
emit_r_inst_rs4:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_sgtz_disp

# bgt rs1, rs2, tgt → blt rs2, rs1, tgt (swap operands)
do_ps_sgtz_disp:
	j	do_ps_sgtz_rs0

do_ps_bgt:
	addi	sp, sp, -12
	sw	gp, 0(sp)
	li	gp, 31
	j	read_reg_op
read_reg_op_rs31:
	sw	a0, 4(sp)
	li	gp, 32
	j	read_reg_op
read_reg_op_rs32:
	sw	a0, 8(sp)
	li	a0, 0
	li	gp, 5
	j	read_br_target
read_br_target_rs5:
	mv	a4, a0
	lw	a2, 4(sp)		# rs2 = first operand (swapped)
	lw	a1, 8(sp)		# rs1 = second operand (swapped)
	li	a3, 4			# blt
	li	a0, 0x63
	lw	gp, 0(sp)
	addi	sp, sp, 12
	j	emit_branch_auto

# ble rs1, rs2, tgt → bge rs2, rs1, tgt
do_ps_ble:
	addi	sp, sp, -12
	sw	gp, 0(sp)
	li	gp, 33
	j	read_reg_op
read_reg_op_rs33:
	sw	a0, 4(sp)
	li	gp, 34
	j	read_reg_op
read_reg_op_rs34:
	sw	a0, 8(sp)
	li	a0, 0
	li	gp, 6
	j	read_br_target
read_br_target_rs6:
	mv	a4, a0
	lw	a2, 4(sp)
	lw	a1, 8(sp)
	li	a3, 5			# bge
	li	a0, 0x63
	lw	gp, 0(sp)
	addi	sp, sp, 12
	j	emit_branch_auto

# bgtu rs1, rs2, tgt → bltu rs2, rs1, tgt
do_ps_bgtu:
	addi	sp, sp, -12
	sw	gp, 0(sp)
	li	gp, 35
	j	read_reg_op
read_reg_op_rs35:
	sw	a0, 4(sp)
	li	gp, 36
	j	read_reg_op
read_reg_op_rs36:
	sw	a0, 8(sp)
	li	a0, 0
	li	gp, 7
	j	read_br_target
read_br_target_rs7:
	mv	a4, a0
	lw	a2, 4(sp)
	lw	a1, 8(sp)
	li	a3, 6			# bltu
	li	a0, 0x63
	lw	gp, 0(sp)
	addi	sp, sp, 12
	j	emit_branch_auto

# bleu rs1, rs2, tgt → bgeu rs2, rs1, tgt
do_ps_bleu:
	addi	sp, sp, -12
	sw	gp, 0(sp)
	li	gp, 37
	j	read_reg_op
read_reg_op_rs37:
	sw	a0, 4(sp)
	li	gp, 38
	j	read_reg_op
read_reg_op_rs38:
	sw	a0, 8(sp)
	li	a0, 0
	li	gp, 8
	j	read_br_target
read_br_target_rs8:
	mv	a4, a0
	lw	a2, 4(sp)
	lw	a1, 8(sp)
	li	a3, 7			# bgeu
	li	a0, 0x63
	lw	gp, 0(sp)
	addi	sp, sp, 12
	j	emit_branch_auto

# bltz rs, tgt → blt rs, x0, tgt
do_ps_bltz:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	gp, 39
	j	read_reg_op
read_reg_op_rs39:
	sw	a0, 4(sp)
	li	a0, 0
	li	gp, 9
	j	read_br_target
read_br_target_rs9:
	mv	a4, a0
	lw	a1, 4(sp)
	li	a2, 0
	li	a3, 4			# blt
	li	a0, 0x63
	lw	gp, 0(sp)
	addi	sp, sp, 8
	j	emit_branch_auto

# blez rs, tgt → bge x0, rs, tgt
do_ps_blez:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	gp, 43
	j	read_reg_op
read_reg_op_rs43:
	sw	a0, 4(sp)
	li	a0, 0
	li	gp, 11
	j	read_br_target
read_br_target_rs11:
	mv	a4, a0
	li	a1, 0
	lw	a2, 4(sp)
	li	a3, 5			# bge
	li	a0, 0x63
	lw	gp, 0(sp)
	addi	sp, sp, 8
	j	emit_branch_auto

# bgez rs, tgt → bge rs, x0, tgt
do_ps_bgez:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	gp, 40
	j	read_reg_op
read_reg_op_rs40:
	sw	a0, 4(sp)
	li	a0, 0
	li	gp, 10
	j	read_br_target
read_br_target_rs10:
	mv	a4, a0
	lw	a1, 4(sp)
	li	a2, 0
	li	a3, 5			# bge
	li	a0, 0x63
	lw	gp, 0(sp)
	addi	sp, sp, 8
	j	emit_branch_auto

# lla rd, symbol → auipc rd, 0 + addi rd, rd, 0 (fixups recorded)
do_ps_lla:
	addi	sp, sp, -8
	sw	gp, 0(sp)
	li	gp, 41
	j	read_reg_op
read_reg_op_rs41:
	sw	a0, 4(sp)		# rd
	li	gp, 0
	j	rec_pcrel_pair
rec_pcrel_pair_rs0:
	lw	a1, 4(sp)		# rd
	li	a2, 0
	li	a0, 0x17		# auipc
	li	gp, 3
	j	emit_u_inst
emit_u_inst_rs3:
	lw	a1, 4(sp)
	mv	a2, a1			# rs1 = rd
	li	a4, 0
	li	a3, 0
	li	a0, 0x13		# addi
	lw	gp, 0(sp)
	addi	sp, sp, 8
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 10
	j	emit_i_inst
emit_i_inst_rs10:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_lla_disp

do_ps_lla_disp:
	j	do_ps_lla_rs0

# ══════════════════════════════════════════════════════════════════════════════
#  Directive Handlers
# ══════════════════════════════════════════════════════════════════════════════

# .equ name, value
do_ps_equ:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 9		# name
	j	read_token
read_token_rs9:
	# Save name in symtab: zero 40 bytes, copy name, set kind=1
	mv	t2, s4
	addi	t3, s4, 40
equ_z:
	sw	zero, 0(t2)
	addi	t2, t2, 4
	bne	t2, t3, equ_z
	mv	t2, s10
	mv	t3, s4
	mv	t4, s0
equ_cp:
	beqz	t4, equ_val
	lbu	t5, 0(t2)
	sb	t5, 0(t3)
	addi	t2, t2, 1
	addi	t3, t3, 1
	addi	t4, t4, -1
	j	equ_cp
equ_val:
	li	gp, 1
	j	read_multi_expr
read_multi_expr_rs1:
	sw	a0, 32(s4)		# value
	li	t0, 1
	sw	t0, 36(s4)		# kind = 1 (constant)
	addi	s4, s4, 40
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_equ_disp

# .byte val[, val...]
do_ps_equ_disp:
	j	do_ps_equ_rs0

do_ps_byte:
	addi	sp, sp, -4
	sw	gp, 0(sp)
byte_lp:
	li	gp, 5		# single-token expression per value
	j	read_imm_op
read_imm_op_rs5:
	# a1=1 means read_imm_op saw a newline before finding a token — the
	# token (if any) was pushed back and belongs on the next logical line.
	# Don't emit anything; exit cleanly.
	bnez	a1, byte_done
	sb	a0, 0(s2)
	addi	s2, s2, 1
	# Check if more values: pending_nl means the token we just consumed
	# ended with \n; EOT means input is exhausted.
	lw	t0, TB_PENDING(s10)
	bnez	t0, byte_done
	lbu	t0, TB_EOT(s10)
	beqz	t0, byte_lp
byte_done:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_byte_disp

# .word val[, val...]
do_ps_byte_disp:
	j	do_ps_byte_rs0

do_ps_word:
	addi	sp, sp, -4
	sw	gp, 0(sp)
word_lp:
	li	gp, 6
	j	read_imm_op
read_imm_op_rs6:
	# See do_ps_byte — a1=1 means the next token is on a following line.
	# Skip the emit so we don't turn a trailing `#` comment or missing
	# operand into a bogus emit / E17.
	bnez	a1, word_done
	li	gp, 9
	j	emit_word
emit_word_rs9:
	lw	t0, TB_PENDING(s10)
	bnez	t0, word_done
	lbu	t0, TB_EOT(s10)
	beqz	t0, word_lp
word_done:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_word_disp

# .ascii "string"
do_ps_word_disp:
	j	do_ps_word_rs0

do_ps_ascii:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 10		# token = "content"
	j	read_token
read_token_rs10:
	# First char must be '"', skip it
	lbu	t0, 0(s10)
	li	t1, '"'
	bne	t0, t1, ascii_bad
	# Process chars from s10+1 to s10+s0 (closing quote already stripped by tokenizer...
	# actually tokenizer includes closing quote as last char)
	# Token: "content" → bytes: '"', c, o, n, t, e, n, t, '"'
	# We emit chars from index 1 to s0-2 (skip opening and closing quotes)
	addi	t2, s10, 1		# start
	add	t3, s10, s0
	addi	t3, t3, -1		# end (exclusive, before closing quote)
ascii_lp:
	beq	t2, t3, ascii_done
	lbu	t0, 0(t2)
	li	t1, '\\'
	beq	t0, t1, ascii_esc
	sb	t0, 0(s2)
	addi	s2, s2, 1
	addi	t2, t2, 1
	j	ascii_lp
ascii_esc:
	addi	t2, t2, 1
	beq	t2, t3, ascii_bad
	lbu	t0, 0(t2)
	li	t1, 'n'
	beq	t0, t1, ascii_n
	li	t1, 't'
	beq	t0, t1, ascii_t
	li	t1, 'r'
	beq	t0, t1, ascii_r
	li	t1, '0'
	beq	t0, t1, ascii_0
	li	t1, '\\'
	beq	t0, t1, ascii_lit
	li	t1, '"'
	beq	t0, t1, ascii_lit
	j	ascii_bad
ascii_n:
	li	t0, 10
	j	ascii_emit
ascii_t:
	li	t0, 9
	j	ascii_emit
ascii_r:
	li	t0, 13
	j	ascii_emit
ascii_0:
	li	t0, 0
	j	ascii_emit
ascii_lit:
	# t0 already has the literal char
ascii_emit:
	sb	t0, 0(s2)
	addi	s2, s2, 1
	addi	t2, t2, 1
	j	ascii_lp
ascii_done:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_ascii_disp
ascii_bad:
	li	a0, 24			# E24: bad string
	j	halt_err

# .zero count
do_ps_ascii_disp:
	j	do_ps_ascii_rs0

do_ps_zero:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	li	gp, 7
	j	read_imm_op
read_imm_op_rs7:
	mv	t0, a0
zero_lp:
	beqz	t0, zero_done
	sb	zero, 0(s2)
	addi	s2, s2, 1
	addi	t0, t0, -1
	j	zero_lp
zero_done:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_zero_disp

# ══════════════════════════════════════════════════════════════════════════════
#  Prologue / Epilogue / Return
# ══════════════════════════════════════════════════════════════════════════════
# prologue reg1 reg2 ... x0
#   Reads register list until x0 sentinel. Emits:
#     addi sp, sp, -frame_size
#     sw   ra, 0(sp)
#     sw   reg1, 4(sp)
#     sw   reg2, 8(sp)
#     ...
#   Saves frame info for matching epilogue.

do_ps_zero_disp:
	j	do_ps_zero_rs0

do_ps_prologue:
	addi	sp, sp, -64
	sw	gp, 60(sp)
	sw	zero, 48(sp)		# nregs = 0
prol_read:
	li	gp, 42
	j	read_reg_op
read_reg_op_rs42:
	beqz	a0, prol_build		# x0 sentinel
	lw	t0, 48(sp)
	li	t1, 12
	bge	t0, t1, prol_bad
	slli	t1, t0, 2
	add	t1, sp, t1
	sw	a0, 0(t1)		# regs[nregs]
	addi	t0, t0, 1
	sw	t0, 48(sp)
	j	prol_read

prol_build:
	lw	t0, 48(sp)		# nregs
	addi	t1, t0, 1		# +1 for ra
	slli	t1, t1, 2		# bytes
	addi	t1, t1, 15
	andi	t1, t1, -16		# align to 16
	sw	t1, 52(sp)		# frame_size

	# Save frame info at TB_FRAMES + depth*60 offset in token area
	lw	t2, TB_FRAMEDEP(s10)		# frame_depth
	li	t3, 5
	bge	t2, t3, prol_bad
	# Compute offset: depth * 60 = depth * 64 - depth * 4
	slli	t3, t2, 6		# depth*64
	slli	t4, t2, 2		# depth*4
	sub	t3, t3, t4		# depth*60
	add	t3, t3, s10
	addi	t3, t3, TB_FRAMES		# frame base
	sw	t1, 0(t3)		# frame_size
	sw	t0, 4(t3)		# nregs
	# Copy regs
	mv	t4, sp
	addi	t5, t3, 8
	mv	t6, t0
prol_cp:
	beqz	t6, prol_cpd
	lw	a0, 0(t4)
	sw	a0, 0(t5)
	addi	t4, t4, 4
	addi	t5, t5, 4
	addi	t6, t6, -1
	j	prol_cp
prol_cpd:
	addi	t2, t2, 1
	sw	t2, TB_FRAMEDEP(s10)		# depth++

	# Emit: addi sp, sp, -frame_size
	lw	t1, 52(sp)
	sub	a4, zero, t1
	li	a3, 0
	li	a2, 2			# sp
	li	a1, 2			# sp
	li	a0, 0x13
	li	gp, 13
	j	emit_i_inst
emit_i_inst_rs13:
	# Emit: sw ra, 0(sp)
	li	a4, 0
	li	a3, 2			# sw
	li	a2, 1			# ra
	li	a1, 2			# sp
	li	a0, 0x23
	li	gp, 1
	j	emit_s_inst
emit_s_inst_rs1:
	# Emit: sw regs[i], (i+1)*4(sp)
	sw	zero, 56(sp)		# i = 0
prol_emit:
	lw	t0, 56(sp)
	lw	t1, 48(sp)
	beq	t0, t1, prol_ret
	slli	t2, t0, 2
	add	t2, sp, t2
	lw	a2, 0(t2)		# reg
	addi	t3, t0, 1
	slli	a4, t3, 2		# offset = (i+1)*4
	li	a3, 2			# sw
	li	a1, 2			# sp
	li	a0, 0x23
	li	gp, 2
	j	emit_s_inst
emit_s_inst_rs2:
	lw	t0, 56(sp)
	addi	t0, t0, 1
	sw	t0, 56(sp)
	j	prol_emit
prol_ret:
	lw	gp, 60(sp)
	addi	sp, sp, 64
	j	do_ps_prologue_disp
prol_bad:
	li	a0, 25
	j	halt_err

# epilogue — restores regs, deallocates frame (no ret)
do_ps_prologue_disp:
	j	do_ps_prologue_rs0

do_ps_epilogue:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	lw	t0, TB_FRAMEDEP(s10)		# frame_depth
	beqz	t0, epil_bad
	addi	t0, t0, -1
	sw	t0, TB_FRAMEDEP(s10)
	# Load frame info
	slli	t1, t0, 6
	slli	t2, t0, 2
	sub	t1, t1, t2		# depth*60
	add	t1, t1, s10
	addi	t1, t1, TB_FRAMES
	lw	t2, 0(t1)		# frame_size
	lw	t3, 4(t1)		# nregs
	# Emit: lw ra, 0(sp)
	li	a4, 0
	li	a3, 2			# lw
	li	a2, 2			# sp (base)
	li	a1, 1			# rd = ra
	li	a0, 0x03
	li	gp, 14
	j	emit_i_inst
emit_i_inst_rs14:
	# Emit: lw regs[i], (i+1)*4(sp)
	# Recalculate frame pointer (t1 was clobbered by emit)
	lw	t0, TB_FRAMEDEP(s10)		# current depth (already decremented)
	slli	t4, t0, 6
	slli	t5, t0, 2
	sub	t4, t4, t5
	add	t4, t4, s10
	addi	t4, t4, TB_FRAMES
	lw	t3, 4(t4)		# nregs
	li	t5, 0			# i
epil_lp:
	beq	t5, t3, epil_end
	addi	t6, t4, 8
	slli	a7, t5, 2
	add	a7, a7, t6
	lw	a1, 0(a7)		# rd = regs[i]
	addi	t6, t5, 1
	slli	a4, t6, 2		# offset = (i+1)*4
	li	a3, 2			# lw
	li	a2, 2			# sp
	li	a0, 0x03
	# save t3,t4,t5 across call
	addi	sp, sp, -12
	sw	t3, 0(sp)
	sw	t4, 4(sp)
	sw	t5, 8(sp)
	li	gp, 15
	j	emit_i_inst
emit_i_inst_rs15:
	lw	t3, 0(sp)
	lw	t4, 4(sp)
	lw	t5, 8(sp)
	addi	sp, sp, 12
	addi	t5, t5, 1
	j	epil_lp
epil_end:
	# Emit: addi sp, sp, frame_size
	lw	a4, 0(t4)		# frame_size
	li	a3, 0
	li	a2, 2
	li	a1, 2
	li	a0, 0x13
	li	gp, 16
	j	emit_i_inst
emit_i_inst_rs16:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	do_ps_epilogue_disp
epil_bad:
	li	a0, 26
	j	halt_err

do_ps_epilogue_disp:
	j	do_ps_epilogue_rs0

# ══════════════════════════════════════════════════════════════════════════════
#  Fixup Pass
# ══════════════════════════════════════════════════════════════════════════════

fixup_pass:
	mv	t0, s7			# fixup iterator
fp_lp:
	beq	t0, s8, fp_ret

	# Search symtab for matching name
	mv	a6, s3
fp_sym:
	beq	a6, s4, fp_noresolve
	# Compare 32-byte names
	mv	t1, t0
	mv	t2, a6
	li	t3, 32
fp_cmp:
	lbu	t4, 0(t1)
	lbu	t5, 0(t2)
	bne	t4, t5, fp_skip
	addi	t1, t1, 1
	addi	t2, t2, 1
	addi	t3, t3, -1
	bnez	t3, fp_cmp

	# Matched — resolve
	lw	t5, 32(a6)		# symbol value
	lw	t6, 32(t0)		# patch offset
	lw	a7, 36(t0)		# slot_type
	add	t2, s1, t6		# patch addr

	li	t3, 1
	beq	a7, t3, fp_enc_j
	li	t3, 7
	beq	a7, t3, fp_enc_uhi_pcrel
	li	t3, 8
	beq	a7, t3, fp_enc_ilo_pcrp
	li	a0, 18			# E18: unknown fixup type
	j	halt_err

fp_skip:
	addi	a6, a6, 40
	j	fp_sym

fp_noresolve:
	li	a0, 17			# E17: unresolved symbol
	j	halt_err

fp_enc_j:
	sub	t5, t5, t6		# PC-relative
	# Range check
	lui	a7, 0x100		# 0x100000
	blt	t5, a7, fpj_hi
	li	a0, 22
	j	halt_err
fpj_hi:
	sub	a7, zero, a7
	bge	t5, a7, fpj_ok
	li	a0, 22
	j	halt_err
fpj_ok:
	lw	t3, 0(t2)
	# Clear imm bits: keep low 12 bits (rd + opcode)
	lui	t4, 1
	addi	t4, t4, -1		# 0xFFF
	and	t3, t3, t4
	# Encode J-type imm
	srli	t4, t5, 20
	andi	t4, t4, 1
	slli	t4, t4, 31
	or	t3, t3, t4
	srli	t4, t5, 1
	li	a7, 0x3FF
	and	t4, t4, a7
	slli	t4, t4, 21
	or	t3, t3, t4
	srli	t4, t5, 11
	andi	t4, t4, 1
	slli	t4, t4, 20
	or	t3, t3, t4
	srli	t4, t5, 12
	andi	t4, t4, 0xFF
	slli	t4, t4, 12
	or	t3, t3, t4
	sw	t3, 0(t2)
	j	fp_next

fp_enc_uhi_pcrel:
	# delta = symbol - patch_offset
	sub	t5, t5, t6
	lw	t3, 0(t2)
	slli	t3, t3, 20
	srli	t3, t3, 20		# clear bits 31:12
	lui	t4, 1
	srli	t4, t4, 1		# 0x800
	add	t5, t5, t4
	srli	t5, t5, 12
	slli	t5, t5, 12
	or	t3, t3, t5
	sw	t3, 0(t2)
	j	fp_next

fp_enc_ilo_pcrp:
	# delta = symbol - (patch_offset - 4)
	addi	t6, t6, -4		# auipc PC
	sub	t5, t5, t6
	lw	t3, 0(t2)
	slli	t3, t3, 12
	srli	t3, t3, 12		# clear bits 31:20
	slli	t5, t5, 20		# lo12 at bits 31:20
	or	t3, t3, t5
	sw	t3, 0(t2)
	j	fp_next

fp_next:
	addi	t0, t0, 40
	j	fp_lp
fp_ret:
	j	fixup_pass_disp

# ══════════════════════════════════════════════════════════════════════════════
#  Output: write s1..s2 to UART
# ══════════════════════════════════════════════════════════════════════════════

fixup_pass_disp:
	j	fixup_pass_rs0

dump_output:
	addi	sp, sp, -4
	sw	gp, 0(sp)
	# Emit q32 magic nop (0x13, 0x00, 0x00, 0x00) before output
	li	t0, 0x13
	li	gp, 6
	j	wrch
wrch_rs6:
	li	t0, 0
	li	gp, 7
	j	wrch
wrch_rs7:
	li	gp, 8
	j	wrch
wrch_rs8:
	li	gp, 9
	j	wrch
wrch_rs9:
	mv	a0, s1
do_lp:
	beq	a0, s2, do_ret
	lbu	t0, 0(a0)
	addi	a0, a0, 1
do_tx:
	lbu	t5, 5(s5)
	andi	t5, t5, 0x20
	beqz	t5, do_tx
	sb	t0, 0(s5)
	j	do_lp
do_ret:
	lw	gp, 0(sp)
	addi	sp, sp, 4
	j	dump_output_disp
dump_output_disp:
	j	dump_output_rs0
