# p1blk ( h r m hibit -- )   one Poly1305 block: h = (h + m + hibit 2^128) r
# mod 2^130 - 5, h and r (and 5r) as 26-bit limbs: h at a0 (5 words,
# updated), r at a1 (r0..r4, then 5r1..5r4), the 16 bytes at a2, hibit (2^24,
# or 0 for a last block padded by hand) in a3.  Written by tools/poly_s.py;
# assembled by tools/s2words.py.
	.option norelax
	lw      a3, 0(sp)               # hibit
	lw      a2, 4(sp)               # the block
	lw      a1, 8(sp)               # r
	lw      a0, 12(sp)              # h
	addi    sp, sp, 16
	lw t0, 0(a0)
	lw t1, 4(a0)
	lw t2, 8(a0)
	lw t3, 12(a0)
	lw t4, 16(a0)
	lbu a4, 0(a2)
	lbu t5, 1(a2)
	slli t5, t5, 8
	or a4, a4, t5
	lbu t5, 2(a2)
	slli t5, t5, 16
	or a4, a4, t5
	lbu t5, 3(a2)
	slli t5, t5, 24
	or a4, a4, t5
	lbu a5, 4(a2)
	lbu t5, 5(a2)
	slli t5, t5, 8
	or a5, a5, t5
	lbu t5, 6(a2)
	slli t5, t5, 16
	or a5, a5, t5
	lbu t5, 7(a2)
	slli t5, t5, 24
	or a5, a5, t5
	lbu a6, 8(a2)
	lbu t5, 9(a2)
	slli t5, t5, 8
	or a6, a6, t5
	lbu t5, 10(a2)
	slli t5, t5, 16
	or a6, a6, t5
	lbu t5, 11(a2)
	slli t5, t5, 24
	or a6, a6, t5
	lbu a7, 12(a2)
	lbu t5, 13(a2)
	slli t5, t5, 8
	or a7, a7, t5
	lbu t5, 14(a2)
	slli t5, t5, 16
	or a7, a7, t5
	lbu t5, 15(a2)
	slli t5, t5, 24
	or a7, a7, t5
	lui t6, 0x4000
	addi t6, t6, -1
	and t5, a4, t6
	add t0, t0, t5
	srli t5, a4, 26
	slli a4, a5, 6
	or t5, t5, a4
	and t5, t5, t6
	add t1, t1, t5
	srli t5, a5, 20
	slli a5, a6, 12
	or t5, t5, a5
	and t5, t5, t6
	add t2, t2, t5
	srli t5, a6, 14
	slli a6, a7, 18
	or t5, t5, a6
	and t5, t5, t6
	add t3, t3, t5
	srli t5, a7, 8
	or t5, t5, a3
	add t4, t4, t5
	li a4, 0
	li a5, 0
	lw a3, 0(a1)
	mv a6, t0
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 32(a1)
	mv a6, t1
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 28(a1)
	mv a6, t2
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 24(a1)
	mv a6, t3
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 20(a1)
	mv a6, t4
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	sw a4, -8(sp)
	sw a5, -4(sp)
	li a4, 0
	li a5, 0
	lw a3, 4(a1)
	mv a6, t0
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 0(a1)
	mv a6, t1
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 32(a1)
	mv a6, t2
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 28(a1)
	mv a6, t3
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 24(a1)
	mv a6, t4
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	sw a4, -16(sp)
	sw a5, -12(sp)
	li a4, 0
	li a5, 0
	lw a3, 8(a1)
	mv a6, t0
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 4(a1)
	mv a6, t1
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 0(a1)
	mv a6, t2
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 32(a1)
	mv a6, t3
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 28(a1)
	mv a6, t4
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	sw a4, -24(sp)
	sw a5, -20(sp)
	li a4, 0
	li a5, 0
	lw a3, 12(a1)
	mv a6, t0
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 8(a1)
	mv a6, t1
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 4(a1)
	mv a6, t2
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 0(a1)
	mv a6, t3
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 32(a1)
	mv a6, t4
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	sw a4, -32(sp)
	sw a5, -28(sp)
	li a4, 0
	li a5, 0
	lw a3, 16(a1)
	mv a6, t0
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 12(a1)
	mv a6, t1
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 8(a1)
	mv a6, t2
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 4(a1)
	mv a6, t3
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	lw a3, 0(a1)
	mv a6, t4
	mv a7, a3
	li t5, 0
1:
	andi t6, a6, 1
	beqz t6, 2f
	add a4, a4, a7
	sltu t6, a4, a7
	add a5, a5, t5
	add a5, a5, t6
2:
	slli t5, t5, 1
	srli t6, a7, 31
	or t5, t5, t6
	slli a7, a7, 1
	srli a6, a6, 1
	bnez a6, 1b
	sw a4, -40(sp)
	sw a5, -36(sp)
	lui t6, 0x4000
	addi t6, t6, -1
	li a6, 0
	lw a4, -8(sp)
	lw a5, -4(sp)
	add a4, a4, a6
	sltu t5, a4, a6
	add a5, a5, t5
	and t0, a4, t6
	srli a6, a4, 26
	slli a5, a5, 6
	or a6, a6, a5
	lw a4, -16(sp)
	lw a5, -12(sp)
	add a4, a4, a6
	sltu t5, a4, a6
	add a5, a5, t5
	and t1, a4, t6
	srli a6, a4, 26
	slli a5, a5, 6
	or a6, a6, a5
	lw a4, -24(sp)
	lw a5, -20(sp)
	add a4, a4, a6
	sltu t5, a4, a6
	add a5, a5, t5
	and t2, a4, t6
	srli a6, a4, 26
	slli a5, a5, 6
	or a6, a6, a5
	lw a4, -32(sp)
	lw a5, -28(sp)
	add a4, a4, a6
	sltu t5, a4, a6
	add a5, a5, t5
	and t3, a4, t6
	srli a6, a4, 26
	slli a5, a5, 6
	or a6, a6, a5
	lw a4, -40(sp)
	lw a5, -36(sp)
	add a4, a4, a6
	sltu t5, a4, a6
	add a5, a5, t5
	and t4, a4, t6
	srli a6, a4, 26
	slli a5, a5, 6
	or a6, a6, a5
	slli t5, a6, 2
	add a6, a6, t5
	add t0, t0, a6
	srli a6, t0, 26
	and t0, t0, t6
	add t1, t1, a6
	sw t0, 0(a0)
	sw t1, 4(a0)
	sw t2, 8(a0)
	sw t3, 12(a0)
	sw t4, 16(a0)
