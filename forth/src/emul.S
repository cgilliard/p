# emul ( a b out -- )   the product of two extension elements (4 cells each,
# by address; out may be either): the schoolbook product into w[0..6] (on
# the data stack), then x^4 = 11 folds w[4..6] back down.  RV32I, branch-
# free arithmetic (see src/p2core.S); a0 a, a1 b, a2 out, t2 p.
	.option norelax

	.macro FADD dst, x, y           # dst = x + y mod p; uses t4
	add     \dst, \x, \y
	sltu    t4, \dst, t2
	addi    t4, t4, -1
	and     t4, t4, t2
	sub     \dst, \dst, t4
	.endm

	.macro FMUL dst, ra, rb         # dst = ra * rb mod p; uses t0, t3, t4
	slli    t0, \rb, 1
	li      t3, 0
	.rept 31
	slli    t3, t3, 1
	sltu    t4, t3, t2
	addi    t4, t4, -1
	and     t4, t4, t2
	sub     t3, t3, t4
	srai    t4, t0, 31
	and     t4, t4, \ra
	add     t3, t3, t4
	sltu    t4, t3, t2
	addi    t4, t4, -1
	and     t4, t4, t2
	sub     t3, t3, t4
	slli    t0, t0, 1
	.endr
	mv      \dst, t3
	.endm

	.macro TIMES11 x                # x = 11 x mod p; uses t1, t4
	FADD    t1, \x, \x              # 2x
	FADD    t5, t1, t1              # 4x
	FADD    t5, t5, t5              # 8x
	FADD    t5, t5, t1              # 10x
	FADD    \x, t5, \x              # 11x
	.endm

	lw      a2, 0(sp)               # out
	lw      a1, 4(sp)               # b
	lw      a0, 8(sp)               # a
	addi    sp, sp, -16             # 3 popped, w[0..6] pushed (28 bytes)
	sw      zero, 0(sp)
	sw      zero, 4(sp)
	sw      zero, 8(sp)
	sw      zero, 12(sp)
	sw      zero, 16(sp)
	sw      zero, 20(sp)
	sw      zero, 24(sp)
	lui     t2, 0x78000
	addi    t2, t2, 1               # p
	li      a3, 0                   # i (bytes)
outer:
	li      a4, 0                   # j (bytes)
inner:
	add     t5, a0, a3
	lw      a5, 0(t5)
	add     t5, a1, a4
	lw      a6, 0(t5)
	FMUL    a7, a5, a6
	add     t5, a3, a4
	add     t5, t5, sp
	lw      t6, 0(t5)
	FADD    t6, t6, a7
	sw      t6, 0(t5)               # w[i + j] += a[i] b[j]
	addi    a4, a4, 4
	li      t5, 16
	blt     a4, t5, inner
	addi    a3, a3, 4
	blt     a3, t5, outer
	lw      a5, 16(sp)              # out[k] = w[k] + 11 w[k + 4], k < 3
	TIMES11 a5
	lw      a6, 0(sp)
	FADD    a6, a6, a5
	lw      a5, 20(sp)
	TIMES11 a5
	lw      a7, 4(sp)
	FADD    a7, a7, a5
	lw      a5, 24(sp)
	TIMES11 a5
	lw      t6, 8(sp)
	FADD    t6, t6, a5
	lw      a5, 12(sp)
	sw      a6, 0(a2)
	sw      a7, 4(a2)
	sw      t6, 8(a2)
	sw      a5, 12(a2)
	addi    sp, sp, 28
