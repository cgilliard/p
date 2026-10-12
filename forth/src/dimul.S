# dimul ( a b -- a*b mod q )   Dilithium's q = 8380417 = 2^23 - 2^13 + 1, a and
# b below q: the 46-bit product by shift and add (RV32I has no multiply),
# then reduced with 2^23 = 2^13 - 1 (mod q), folded twice to stay in 32
# bits, and q taken off while it's over (src/dilithium.fam).
	.option norelax
	lw      a1, 0(sp)               # b
	lw      a0, 4(sp)               # a
	addi    sp, sp, 4
	li      a2, 0                   # the product: a2 low, a3 high
	li      a3, 0
	mv      a5, a0                  # a, shifted: a5 low, a4 high
	li      a4, 0
	beqz    a1, red
1:
	andi    t0, a1, 1
	beqz    t0, 2f
	add     a2, a2, a5
	sltu    t0, a2, a5
	add     a3, a3, a4
	add     a3, a3, t0
2:
	slli    a4, a4, 1
	srli    t0, a5, 31
	or      a4, a4, t0
	slli    a5, a5, 1
	srli    a1, a1, 1
	bnez    a1, 1b
red:
	# x = H 2^23 + L;  H = H1 2^10 + H0;  x = H1 2^13 - H1 + H0 2^13 - H + L (mod q)
	srli    t0, a2, 23
	slli    t1, a3, 9
	or      t0, t0, t1              # H
	li      t1, 0x7FFFFF
	and     t2, a2, t1              # L
	srli    t3, t0, 10              # H1
	andi    t4, t0, 0x3FF           # H0
	slli    t5, t3, 13
	add     t2, t2, t5
	slli    t5, t4, 13
	add     t2, t2, t5
	sub     t2, t2, t3
	sub     t2, t2, t0
	li      t5, 0xFFC002            # 2q: the sum is now positive, below 2^27
	add     t2, t2, t5
	srli    t3, t2, 23              # fold again: below 2^23 + 2^17
	and     t2, t2, t1
	slli    t4, t3, 13
	add     t2, t2, t4
	sub     t2, t2, t3
	li      t5, 0x7FE001            # q
	bltu    t2, t5, 3f
	sub     t2, t2, t5
3:
	bltu    t2, t5, 4f
	sub     t2, t2, t5
4:
	sw      t2, 0(sp)
