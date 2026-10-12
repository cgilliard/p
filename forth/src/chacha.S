# chblk ( in out -- )   the ChaCha20 block function: 16 words in (the
# constants, key, counter, nonce), 16 words out (the rounds' result plus the
# input: the keystream).  s0, s2 and s4 are saved on the data stack.  Written
# by tools/chacha_s.py; assembled by tools/s2words.py.
	.option norelax
	addi    sp, sp, -12
	sw      s0, 0(sp)
	sw      s2, 4(sp)
	sw      s4, 8(sp)
	lw      s2, 16(sp)              # in
	lw      a0, 0(s2)
	lw      a1, 4(s2)
	lw      a2, 8(s2)
	lw      a3, 12(s2)
	lw      a4, 16(s2)
	lw      a5, 20(s2)
	lw      a6, 24(s2)
	lw      a7, 28(s2)
	lw      t0, 32(s2)
	lw      t1, 36(s2)
	lw      t2, 40(s2)
	lw      t3, 44(s2)
	lw      t4, 48(s2)
	lw      t5, 52(s2)
	lw      t6, 56(s2)
	lw      s0, 60(s2)
	li      s2, 10
round:
	add a0, a0, a4
	xor t4, t4, a0
	slli s4, t4, 16
	srli t4, t4, 16
	or t4, t4, s4
	add t0, t0, t4
	xor a4, a4, t0
	slli s4, a4, 12
	srli a4, a4, 20
	or a4, a4, s4
	add a0, a0, a4
	xor t4, t4, a0
	slli s4, t4, 8
	srli t4, t4, 24
	or t4, t4, s4
	add t0, t0, t4
	xor a4, a4, t0
	slli s4, a4, 7
	srli a4, a4, 25
	or a4, a4, s4
	add a1, a1, a5
	xor t5, t5, a1
	slli s4, t5, 16
	srli t5, t5, 16
	or t5, t5, s4
	add t1, t1, t5
	xor a5, a5, t1
	slli s4, a5, 12
	srli a5, a5, 20
	or a5, a5, s4
	add a1, a1, a5
	xor t5, t5, a1
	slli s4, t5, 8
	srli t5, t5, 24
	or t5, t5, s4
	add t1, t1, t5
	xor a5, a5, t1
	slli s4, a5, 7
	srli a5, a5, 25
	or a5, a5, s4
	add a2, a2, a6
	xor t6, t6, a2
	slli s4, t6, 16
	srli t6, t6, 16
	or t6, t6, s4
	add t2, t2, t6
	xor a6, a6, t2
	slli s4, a6, 12
	srli a6, a6, 20
	or a6, a6, s4
	add a2, a2, a6
	xor t6, t6, a2
	slli s4, t6, 8
	srli t6, t6, 24
	or t6, t6, s4
	add t2, t2, t6
	xor a6, a6, t2
	slli s4, a6, 7
	srli a6, a6, 25
	or a6, a6, s4
	add a3, a3, a7
	xor s0, s0, a3
	slli s4, s0, 16
	srli s0, s0, 16
	or s0, s0, s4
	add t3, t3, s0
	xor a7, a7, t3
	slli s4, a7, 12
	srli a7, a7, 20
	or a7, a7, s4
	add a3, a3, a7
	xor s0, s0, a3
	slli s4, s0, 8
	srli s0, s0, 24
	or s0, s0, s4
	add t3, t3, s0
	xor a7, a7, t3
	slli s4, a7, 7
	srli a7, a7, 25
	or a7, a7, s4
	add a0, a0, a5
	xor s0, s0, a0
	slli s4, s0, 16
	srli s0, s0, 16
	or s0, s0, s4
	add t2, t2, s0
	xor a5, a5, t2
	slli s4, a5, 12
	srli a5, a5, 20
	or a5, a5, s4
	add a0, a0, a5
	xor s0, s0, a0
	slli s4, s0, 8
	srli s0, s0, 24
	or s0, s0, s4
	add t2, t2, s0
	xor a5, a5, t2
	slli s4, a5, 7
	srli a5, a5, 25
	or a5, a5, s4
	add a1, a1, a6
	xor t4, t4, a1
	slli s4, t4, 16
	srli t4, t4, 16
	or t4, t4, s4
	add t3, t3, t4
	xor a6, a6, t3
	slli s4, a6, 12
	srli a6, a6, 20
	or a6, a6, s4
	add a1, a1, a6
	xor t4, t4, a1
	slli s4, t4, 8
	srli t4, t4, 24
	or t4, t4, s4
	add t3, t3, t4
	xor a6, a6, t3
	slli s4, a6, 7
	srli a6, a6, 25
	or a6, a6, s4
	add a2, a2, a7
	xor t5, t5, a2
	slli s4, t5, 16
	srli t5, t5, 16
	or t5, t5, s4
	add t0, t0, t5
	xor a7, a7, t0
	slli s4, a7, 12
	srli a7, a7, 20
	or a7, a7, s4
	add a2, a2, a7
	xor t5, t5, a2
	slli s4, t5, 8
	srli t5, t5, 24
	or t5, t5, s4
	add t0, t0, t5
	xor a7, a7, t0
	slli s4, a7, 7
	srli a7, a7, 25
	or a7, a7, s4
	add a3, a3, a4
	xor t6, t6, a3
	slli s4, t6, 16
	srli t6, t6, 16
	or t6, t6, s4
	add t1, t1, t6
	xor a4, a4, t1
	slli s4, a4, 12
	srli a4, a4, 20
	or a4, a4, s4
	add a3, a3, a4
	xor t6, t6, a3
	slli s4, t6, 8
	srli t6, t6, 24
	or t6, t6, s4
	add t1, t1, t6
	xor a4, a4, t1
	slli s4, a4, 7
	srli a4, a4, 25
	or a4, a4, s4
	addi    s2, s2, -1
	beqz    s2, out
	j       round
out:
	sw      s0, -4(sp)              # x15, to free s0
	lw      s2, 16(sp)              # in
	lw      s4, 12(sp)              # out
	lw      s0, 0(s2)
	add     a0, a0, s0
	sw      a0, 0(s4)
	lw      s0, 4(s2)
	add     a1, a1, s0
	sw      a1, 4(s4)
	lw      s0, 8(s2)
	add     a2, a2, s0
	sw      a2, 8(s4)
	lw      s0, 12(s2)
	add     a3, a3, s0
	sw      a3, 12(s4)
	lw      s0, 16(s2)
	add     a4, a4, s0
	sw      a4, 16(s4)
	lw      s0, 20(s2)
	add     a5, a5, s0
	sw      a5, 20(s4)
	lw      s0, 24(s2)
	add     a6, a6, s0
	sw      a6, 24(s4)
	lw      s0, 28(s2)
	add     a7, a7, s0
	sw      a7, 28(s4)
	lw      s0, 32(s2)
	add     t0, t0, s0
	sw      t0, 32(s4)
	lw      s0, 36(s2)
	add     t1, t1, s0
	sw      t1, 36(s4)
	lw      s0, 40(s2)
	add     t2, t2, s0
	sw      t2, 40(s4)
	lw      s0, 44(s2)
	add     t3, t3, s0
	sw      t3, 44(s4)
	lw      s0, 48(s2)
	add     t4, t4, s0
	sw      t4, 48(s4)
	lw      s0, 52(s2)
	add     t5, t5, s0
	sw      t5, 52(s4)
	lw      s0, 56(s2)
	add     t6, t6, s0
	sw      t6, 56(s4)
	lw      s0, -4(sp)
	lw      a0, 60(s2)
	add     s0, s0, a0
	sw      s0, 60(s4)
	lw      s0, 0(sp)
	lw      s2, 4(sp)
	lw      s4, 8(sp)
	addi    sp, sp, 20              # the three saved, and the two arguments
