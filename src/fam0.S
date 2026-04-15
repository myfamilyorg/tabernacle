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
# file: fam0.S - first stage bootstrap tool (168 bytes compiled - GNU as src)
# RISC-V 32-bit Hex-to-Binary Converter (Bootstrapping Seed)
#
# Runs only in a known environment (QEMU virt bare-metal, -bios none). Takes
# advantage of two environment guarantees:
#   1. GPRs are zeroed at reset, so s3 (nibble toggle) and s4 (comment flag)
#      don't need explicit init.
#   2. Load address is 0x80000000, so the output buffer can live at a fixed
#      absolute address (0x80100000) instead of a PC-relative one.
#
# ── Porting note (reset state) ───────────────────────────────────────────────
# Assumption #1 is a QEMU convention, NOT a RISC-V architectural guarantee.
# The privileged spec leaves GPR contents at reset unspecified. Real RISC-V
# hardware (e.g., SiFive HiFive1/FE310) typically runs through a ROM
# bootloader (ZSBL) before user code, which leaves GPRs in an arbitrary
# state. The same applies to QEMU runs that use a BIOS such as OpenSBI.
#
# If porting fam0 to real hardware or any environment with a bootloader,
# add back explicit initialization for s3 and s4 after the `mv s2, s1` line:
#
#     li  s4, 0        # comment flag = false
#     li  s3, 1        # nibble toggle = "expecting high"
#
# and invert `beqz s3, store_low` back to `bnez s3, store_low` below.
# This grows fam0 to 176 bytes (44 instructions) but makes it
# reset-state-independent. The tradeoff is 8 bytes for robustness.
# ──────────────────────────────────────────────────────────────────────────────

_start:
	li	s6, 10			# Constant: (\n) and Hex limit (10)
	li	s5, 0x10000000		# Constant: UART base address
	lui	s1, 0x80100		# s1 = 0x80100000 = start of output buffer
	mv	s2, s1			# s2 = high-water mark (starts == s1)
	# s4 (comment flag, want 0)       — rely on GPR reset = 0
	# s3 (nibble toggle, want "high") — rely on GPR reset = 0; the store
	#   block uses beqz-after-xor so s3 = 0 correctly means "expecting
	#   high nibble next" on the first iteration.

	# Main input processing loop
loop:
	# UART poll: check for incoming byte
	lbu	t5, 5(s5)		# Read Line Status Register
	andi	t5, t5, 1		# Mask: Data Ready bit
	beqz	t5, loop		# Wait if no data
	lbu	t1, 0(s5)		# Read byte from Receive Buffer

	# Logic: Handle line comments
	bne	t1, s6, not_backn	# If not newline, skip reset
	li	s4, 0			# At '\n', set in-comment = false
not_backn:
	li	t3, '#'			# Load comment start delimiter
	bne	t1, t3, skip_start_comment
	li	s4, 1			# At '#', set in-comment = true
skip_start_comment:

	# Logic: Check for End of Transmission (ASCII 4)
	li	t3, 4
	beq	t1, t3, end_loop	# Exit input loop if EOT received

	# If currently inside a comment, ignore all characters
	bnez	s4, loop

	# Logic: ASCII Hex to Binary Nibble conversion. Whitespace and control
	# codes (< '0') naturally fall through the two bltu checks to `j loop`
	# because `addi t1,-48` makes them wrap large-unsigned; no explicit
	# whitespace filter is needed.
	addi	t1, t1, -48 		# Normalize '0' to 0
	bltu	t1, s6, store	 	# If 0-9, it's a valid hex digit
	addi	t1, t1, -7		# Normalize 'A'-'F' (55-48=7 offset)
	li	t3, 16
	bltu	t1, t3, store 		# If 10-15, it's a valid hex digit
	j	loop			# Otherwise, skip invalid hex char

	# Logic: Pack two 4-bit nibbles into one 8-bit byte
	# Invariant: after each xor, s3=1 → just parsed high nibble;
	#            s3=0 → just parsed low nibble (and must emit the byte).
store:
	xori	s3, s3, 1		# Toggle high/low state
	beqz	s3, store_low		# If 0, just finished the low nibble
	slli	t4, t1, 4		# Store high nibble in t4
	j	loop

store_low:
	or	t4, t4, t1		# Combine high and low nibbles
	sb	t4, 0(s2)		# Store resulting byte in buffer
	addi	s2, s2, 1		# Increment high-water pointer
	j	loop
end_loop:

	# Final Output: Stream the constructed binary back through the UART
output:
	beq	s1, s2, end_output 	# Stop when read ptr == write ptr
	lbu	t3, 0(s1)		# Load byte from buffer
	addi	s1, s1, 1		# Increment read pointer

retry:
	lbu	t1, 5(s5)		# Check Line Status Register
	andi	t1, t1, 0x20		# Mask: Transmitter Holding Register
	beqz	t1, retry		# Wait until UART is ready to send
	sb	t3, 0(s5)		# Send byte to UART
	j	output

	# Shutdown
end_output:
	li	s5, 0x100000		# QEMU Virt Device address
	li	t1, 0x5555		# Power-off command
	sw	t1, 0(s5)		# Exit

