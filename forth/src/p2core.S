# p2core ( st w rci rcp rcf dg np -- )   the Poseidon2 permutation in place, in
# one piece of RV32I: st the w cells; rci / rcf the initial / final full
# rounds' constants (w each), rcp the np partial rounds' (one each), dg the
# internal diagonal as descriptors -- all little-endian words.  A descriptor:
# bit 31 negate; bit 8 set: divide by 2^k (k = the low 5 bits), else
# multiply by n (1..4, the low bits).
#
# Registers: a0 p, a1 st, a2 w*4, a3 this full round's constants, a4 the
# partial constants, a5 rcf, a6 dg, a7 np; s0 the round, s2 a byte index,
# s3 a sum, s4 FADD's scratch; t0..t6 scratch.  s0, s2..s4 are saved on the
# data stack.
	.option norelax

	.macro FADD dst, x, y           # dst = x + y mod p (x, y < p); uses s4
	add     \dst, \x, \y            # (branch-free: QEMU ends a block at a branch)
	sltu    s4, \dst, a0
	addi    s4, s4, -1
	and     s4, s4, a0
	sub     \dst, \dst, s4
	.endm

	.macro FMUL dst, ra, rb         # dst = ra * rb mod p; uses t0, t3, t4
	slli    t0, \rb, 1              # rb's bit 30 to the sign bit
	li      t3, 0
	.rept 31                        # branch-free (QEMU ends a block at a branch)
	slli    t3, t3, 1               # r = 2r mod p
	sltu    t4, t3, a0
	addi    t4, t4, -1
	and     t4, t4, a0
	sub     t3, t3, t4
	srai    t4, t0, 31              # the bit: r = r + ra mod p
	and     t4, t4, \ra
	add     t3, t3, t4
	sltu    t4, t3, a0
	addi    t4, t4, -1
	and     t4, t4, a0
	sub     t3, t3, t4
	slli    t0, t0, 1
	.endr
	mv      \dst, t3
	.endm

	.macro SBOX x                   # x = x^7; uses t0..t4
	FMUL    t1, \x, \x              # x^2
	FMUL    t2, t1, \x              # x^3
	FMUL    t1, t2, t2              # x^6
	FMUL    \x, t1, \x              # x^7
	.endm

	lw      a7, 0(sp)               # np
	lw      a6, 4(sp)               # dg
	lw      a5, 8(sp)               # rcf
	lw      a4, 12(sp)              # rcp
	lw      a3, 16(sp)              # rci
	lw      a2, 20(sp)              # w
	lw      a1, 24(sp)              # st
	addi    sp, sp, 12              # 7 popped, 4 pushed: s0, s2, s3, s4
	sw      s0, 0(sp)
	sw      s2, 4(sp)
	sw      s3, 8(sp)
	sw      s4, 12(sp)
	slli    a2, a2, 2
	lui     a0, 0x78000
	addi    a0, a0, 1               # p
	li      s0, 0                   # the round

# ── The external layer, then the next round ──
ext:
	li      s2, 0
ext_m:                                  # the 4x4 matrix on each group of four
	add     t6, a1, s2
	lw      t0, 0(t6)
	lw      t1, 4(t6)
	lw      t2, 8(t6)
	lw      t3, 12(t6)
	FADD    t4, t0, t1              # t01
	FADD    t5, t2, t3              # t23
	FADD    s3, t4, t5              # t0123
	FADD    t3, s3, t3              # t01233
	FADD    t1, s3, t1              # t01123
	FADD    s3, t3, t5
	sw      s3, 8(t6)               # x2 = t01233 + t23
	FADD    s3, t0, t0
	FADD    s3, s3, t3
	sw      s3, 12(t6)              # x3 = t01233 + 2 x0
	FADD    s3, t1, t4
	sw      s3, 0(t6)               # x0 = t01123 + t01
	FADD    s3, t2, t2
	FADD    s3, s3, t1
	sw      s3, 4(t6)               # x1 = t01123 + 2 x2
	addi    s2, s2, 16
	blt     s2, a2, ext_m
	li      s2, 0                   # each position mod 4: add its class's sum
ext_c:
	li      s3, 0
	mv      t1, s2
ec_sum:	add     t6, a1, t1
	lw      t0, 0(t6)
	FADD    s3, s3, t0
	addi    t1, t1, 16
	blt     t1, a2, ec_sum
	mv      t1, s2
ec_add:	add     t6, a1, t1
	lw      t0, 0(t6)
	FADD    t0, t0, s3
	sw      t0, 0(t6)
	addi    t1, t1, 16
	blt     t1, a2, ec_add
	addi    s2, s2, 4
	li      t0, 16
	blt     s2, t0, ext_c

# ── Which round next ──
round:
	li      t0, 4
	blt     s0, t0, full            # the 4 initial full rounds
	addi    t0, a7, 4
	blt     s0, t0, partial         # then np partial ones
	addi    t1, t0, 4
	bge     s0, t1, done            # then 4 final full rounds
	bne     s0, t0, full
	mv      a3, a5                  # the first final round: its constants

full:                                   # every cell: + constant, S-box
	addi    s0, s0, 1
	li      s2, 0
full_c:
	add     t6, a1, s2
	lw      t5, 0(t6)
	add     t1, a3, s2
	lw      t1, 0(t1)
	FADD    t5, t5, t1
	SBOX    t5
	add     t6, a1, s2
	sw      t5, 0(t6)
	addi    s2, s2, 4
	blt     s2, a2, full_c
	add     a3, a3, a2              # the next round's constants
	j       ext

partial:                                # cell 0: + constant, S-box; internal layer
	addi    s0, s0, 1
	lw      t5, 0(a1)
	lw      t1, 0(a4)
	addi    a4, a4, 4
	FADD    t5, t5, t1
	SBOX    t5
	sw      t5, 0(a1)
	li      s3, 0                   # the sum
	li      s2, 0
ps_sum:	add     t6, a1, s2
	lw      t0, 0(t6)
	FADD    s3, s3, t0
	addi    s2, s2, 4
	blt     s2, a2, ps_sum
	li      s2, 0
pi:	add     t6, a1, s2              # out[i] = d[i] * s[i] + sum
	lw      t5, 0(t6)
	add     t1, a6, s2
	lw      t1, 0(t1)               # d[i]'s descriptor
	andi    t2, t1, 0x100
	andi    t3, t1, 31
	bnez    t2, inv
	mv      t4, t5                  # times n (1..4)
	li      t0, 1
	beq     t3, t0, md
	FADD    t4, t5, t5
	li      t0, 2
	beq     t3, t0, md
	li      t0, 3
	bne     t3, t0, 3f
	FADD    t4, t4, t5
	j       md
3:	FADD    t4, t4, t4
	j       md
inv:                                    # divided by 2^k: p = 1 mod 2^k, so with
	li      t0, 1                   # m = -x mod 2^k, x / 2^k =
	sll     t0, t0, t3              #   (x + m) / 2^k + 15 m 2^(27 - k)
	addi    t0, t0, -1
	sub     t2, zero, t5
	and     t2, t2, t0              # m
	add     t4, t5, t2
	srl     t4, t4, t3              # (x + m) >> k
	slli    t0, t2, 4
	sub     t0, t0, t2              # 15 m
	li      t2, 27
	sub     t2, t2, t3
	sll     t0, t0, t2
	add     t4, t4, t0              # < 2p
	bltu    t4, a0, md
	sub     t4, t4, a0
md:	bge     t1, zero, 4f            # negated?
	beqz    t4, 4f
	sub     t4, a0, t4
4:	FADD    t4, t4, s3
	sw      t4, 0(t6)
	addi    s2, s2, 4
	blt     s2, a2, pi
	j       round

done:
	lw      s0, 0(sp)
	lw      s2, 4(sp)
	lw      s3, 8(sp)
	lw      s4, 12(sp)
	addi    sp, sp, 16
