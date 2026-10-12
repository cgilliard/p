# kf1600 ( state rc scratch -- )   Keccak-f[1600], the 24 rounds: the state
# (200 bytes, 25 lanes of two words, low first), the round constants (24
# lanes, from src/keccak.fam), a scratch of 240 bytes.  Written by
# tools/keccak_s.py; assembled by tools/s2words.py.
	.option norelax
	lw      a2, 0(sp)               # scratch
	lw      a1, 4(sp)               # round constants
	lw      a0, 8(sp)               # state
	addi    sp, sp, 12
	li      a3, 24
round:
	lw t0, 0(a0)
	lw t1, 4(a0)
	lw t2, 40(a0)
	xor t0, t0, t2
	lw t2, 44(a0)
	xor t1, t1, t2
	lw t2, 80(a0)
	xor t0, t0, t2
	lw t2, 84(a0)
	xor t1, t1, t2
	lw t2, 120(a0)
	xor t0, t0, t2
	lw t2, 124(a0)
	xor t1, t1, t2
	lw t2, 160(a0)
	xor t0, t0, t2
	lw t2, 164(a0)
	xor t1, t1, t2
	sw t0, 200(a2)
	sw t1, 204(a2)
	lw t0, 8(a0)
	lw t1, 12(a0)
	lw t2, 48(a0)
	xor t0, t0, t2
	lw t2, 52(a0)
	xor t1, t1, t2
	lw t2, 88(a0)
	xor t0, t0, t2
	lw t2, 92(a0)
	xor t1, t1, t2
	lw t2, 128(a0)
	xor t0, t0, t2
	lw t2, 132(a0)
	xor t1, t1, t2
	lw t2, 168(a0)
	xor t0, t0, t2
	lw t2, 172(a0)
	xor t1, t1, t2
	sw t0, 208(a2)
	sw t1, 212(a2)
	lw t0, 16(a0)
	lw t1, 20(a0)
	lw t2, 56(a0)
	xor t0, t0, t2
	lw t2, 60(a0)
	xor t1, t1, t2
	lw t2, 96(a0)
	xor t0, t0, t2
	lw t2, 100(a0)
	xor t1, t1, t2
	lw t2, 136(a0)
	xor t0, t0, t2
	lw t2, 140(a0)
	xor t1, t1, t2
	lw t2, 176(a0)
	xor t0, t0, t2
	lw t2, 180(a0)
	xor t1, t1, t2
	sw t0, 216(a2)
	sw t1, 220(a2)
	lw t0, 24(a0)
	lw t1, 28(a0)
	lw t2, 64(a0)
	xor t0, t0, t2
	lw t2, 68(a0)
	xor t1, t1, t2
	lw t2, 104(a0)
	xor t0, t0, t2
	lw t2, 108(a0)
	xor t1, t1, t2
	lw t2, 144(a0)
	xor t0, t0, t2
	lw t2, 148(a0)
	xor t1, t1, t2
	lw t2, 184(a0)
	xor t0, t0, t2
	lw t2, 188(a0)
	xor t1, t1, t2
	sw t0, 224(a2)
	sw t1, 228(a2)
	lw t0, 32(a0)
	lw t1, 36(a0)
	lw t2, 72(a0)
	xor t0, t0, t2
	lw t2, 76(a0)
	xor t1, t1, t2
	lw t2, 112(a0)
	xor t0, t0, t2
	lw t2, 116(a0)
	xor t1, t1, t2
	lw t2, 152(a0)
	xor t0, t0, t2
	lw t2, 156(a0)
	xor t1, t1, t2
	lw t2, 192(a0)
	xor t0, t0, t2
	lw t2, 196(a0)
	xor t1, t1, t2
	sw t0, 232(a2)
	sw t1, 236(a2)
	lw t0, 208(a2)
	lw t1, 212(a2)
	slli t2, t0, 1
	srli a7, t1, 31
	or t2, t2, a7
	slli t3, t1, 1
	srli a7, t0, 31
	or t3, t3, a7
	lw t5, 232(a2)
	lw t6, 236(a2)
	xor t2, t2, t5
	xor t3, t3, t6
	lw t4, 0(a0)
	xor t4, t4, t2
	sw t4, 0(a0)
	lw t4, 4(a0)
	xor t4, t4, t3
	sw t4, 4(a0)
	lw t4, 40(a0)
	xor t4, t4, t2
	sw t4, 40(a0)
	lw t4, 44(a0)
	xor t4, t4, t3
	sw t4, 44(a0)
	lw t4, 80(a0)
	xor t4, t4, t2
	sw t4, 80(a0)
	lw t4, 84(a0)
	xor t4, t4, t3
	sw t4, 84(a0)
	lw t4, 120(a0)
	xor t4, t4, t2
	sw t4, 120(a0)
	lw t4, 124(a0)
	xor t4, t4, t3
	sw t4, 124(a0)
	lw t4, 160(a0)
	xor t4, t4, t2
	sw t4, 160(a0)
	lw t4, 164(a0)
	xor t4, t4, t3
	sw t4, 164(a0)
	lw t0, 216(a2)
	lw t1, 220(a2)
	slli t2, t0, 1
	srli a7, t1, 31
	or t2, t2, a7
	slli t3, t1, 1
	srli a7, t0, 31
	or t3, t3, a7
	lw t5, 200(a2)
	lw t6, 204(a2)
	xor t2, t2, t5
	xor t3, t3, t6
	lw t4, 8(a0)
	xor t4, t4, t2
	sw t4, 8(a0)
	lw t4, 12(a0)
	xor t4, t4, t3
	sw t4, 12(a0)
	lw t4, 48(a0)
	xor t4, t4, t2
	sw t4, 48(a0)
	lw t4, 52(a0)
	xor t4, t4, t3
	sw t4, 52(a0)
	lw t4, 88(a0)
	xor t4, t4, t2
	sw t4, 88(a0)
	lw t4, 92(a0)
	xor t4, t4, t3
	sw t4, 92(a0)
	lw t4, 128(a0)
	xor t4, t4, t2
	sw t4, 128(a0)
	lw t4, 132(a0)
	xor t4, t4, t3
	sw t4, 132(a0)
	lw t4, 168(a0)
	xor t4, t4, t2
	sw t4, 168(a0)
	lw t4, 172(a0)
	xor t4, t4, t3
	sw t4, 172(a0)
	lw t0, 224(a2)
	lw t1, 228(a2)
	slli t2, t0, 1
	srli a7, t1, 31
	or t2, t2, a7
	slli t3, t1, 1
	srli a7, t0, 31
	or t3, t3, a7
	lw t5, 208(a2)
	lw t6, 212(a2)
	xor t2, t2, t5
	xor t3, t3, t6
	lw t4, 16(a0)
	xor t4, t4, t2
	sw t4, 16(a0)
	lw t4, 20(a0)
	xor t4, t4, t3
	sw t4, 20(a0)
	lw t4, 56(a0)
	xor t4, t4, t2
	sw t4, 56(a0)
	lw t4, 60(a0)
	xor t4, t4, t3
	sw t4, 60(a0)
	lw t4, 96(a0)
	xor t4, t4, t2
	sw t4, 96(a0)
	lw t4, 100(a0)
	xor t4, t4, t3
	sw t4, 100(a0)
	lw t4, 136(a0)
	xor t4, t4, t2
	sw t4, 136(a0)
	lw t4, 140(a0)
	xor t4, t4, t3
	sw t4, 140(a0)
	lw t4, 176(a0)
	xor t4, t4, t2
	sw t4, 176(a0)
	lw t4, 180(a0)
	xor t4, t4, t3
	sw t4, 180(a0)
	lw t0, 232(a2)
	lw t1, 236(a2)
	slli t2, t0, 1
	srli a7, t1, 31
	or t2, t2, a7
	slli t3, t1, 1
	srli a7, t0, 31
	or t3, t3, a7
	lw t5, 216(a2)
	lw t6, 220(a2)
	xor t2, t2, t5
	xor t3, t3, t6
	lw t4, 24(a0)
	xor t4, t4, t2
	sw t4, 24(a0)
	lw t4, 28(a0)
	xor t4, t4, t3
	sw t4, 28(a0)
	lw t4, 64(a0)
	xor t4, t4, t2
	sw t4, 64(a0)
	lw t4, 68(a0)
	xor t4, t4, t3
	sw t4, 68(a0)
	lw t4, 104(a0)
	xor t4, t4, t2
	sw t4, 104(a0)
	lw t4, 108(a0)
	xor t4, t4, t3
	sw t4, 108(a0)
	lw t4, 144(a0)
	xor t4, t4, t2
	sw t4, 144(a0)
	lw t4, 148(a0)
	xor t4, t4, t3
	sw t4, 148(a0)
	lw t4, 184(a0)
	xor t4, t4, t2
	sw t4, 184(a0)
	lw t4, 188(a0)
	xor t4, t4, t3
	sw t4, 188(a0)
	lw t0, 200(a2)
	lw t1, 204(a2)
	slli t2, t0, 1
	srli a7, t1, 31
	or t2, t2, a7
	slli t3, t1, 1
	srli a7, t0, 31
	or t3, t3, a7
	lw t5, 224(a2)
	lw t6, 228(a2)
	xor t2, t2, t5
	xor t3, t3, t6
	lw t4, 32(a0)
	xor t4, t4, t2
	sw t4, 32(a0)
	lw t4, 36(a0)
	xor t4, t4, t3
	sw t4, 36(a0)
	lw t4, 72(a0)
	xor t4, t4, t2
	sw t4, 72(a0)
	lw t4, 76(a0)
	xor t4, t4, t3
	sw t4, 76(a0)
	lw t4, 112(a0)
	xor t4, t4, t2
	sw t4, 112(a0)
	lw t4, 116(a0)
	xor t4, t4, t3
	sw t4, 116(a0)
	lw t4, 152(a0)
	xor t4, t4, t2
	sw t4, 152(a0)
	lw t4, 156(a0)
	xor t4, t4, t3
	sw t4, 156(a0)
	lw t4, 192(a0)
	xor t4, t4, t2
	sw t4, 192(a0)
	lw t4, 196(a0)
	xor t4, t4, t3
	sw t4, 196(a0)
	lw t0, 0(a0)
	lw t1, 4(a0)
	mv t2, t0
	mv t3, t1
	sw t2, 0(a2)
	sw t3, 4(a2)
	lw t0, 40(a0)
	lw t1, 44(a0)
	slli t2, t1, 4
	srli a7, t0, 28
	or t2, t2, a7
	slli t3, t0, 4
	srli a7, t1, 28
	or t3, t3, a7
	sw t2, 128(a2)
	sw t3, 132(a2)
	lw t0, 80(a0)
	lw t1, 84(a0)
	slli t2, t0, 3
	srli a7, t1, 29
	or t2, t2, a7
	slli t3, t1, 3
	srli a7, t0, 29
	or t3, t3, a7
	sw t2, 56(a2)
	sw t3, 60(a2)
	lw t0, 120(a0)
	lw t1, 124(a0)
	slli t2, t1, 9
	srli a7, t0, 23
	or t2, t2, a7
	slli t3, t0, 9
	srli a7, t1, 23
	or t3, t3, a7
	sw t2, 184(a2)
	sw t3, 188(a2)
	lw t0, 160(a0)
	lw t1, 164(a0)
	slli t2, t0, 18
	srli a7, t1, 14
	or t2, t2, a7
	slli t3, t1, 18
	srli a7, t0, 14
	or t3, t3, a7
	sw t2, 112(a2)
	sw t3, 116(a2)
	lw t0, 8(a0)
	lw t1, 12(a0)
	slli t2, t0, 1
	srli a7, t1, 31
	or t2, t2, a7
	slli t3, t1, 1
	srli a7, t0, 31
	or t3, t3, a7
	sw t2, 80(a2)
	sw t3, 84(a2)
	lw t0, 48(a0)
	lw t1, 52(a0)
	slli t2, t1, 12
	srli a7, t0, 20
	or t2, t2, a7
	slli t3, t0, 12
	srli a7, t1, 20
	or t3, t3, a7
	sw t2, 8(a2)
	sw t3, 12(a2)
	lw t0, 88(a0)
	lw t1, 92(a0)
	slli t2, t0, 10
	srli a7, t1, 22
	or t2, t2, a7
	slli t3, t1, 10
	srli a7, t0, 22
	or t3, t3, a7
	sw t2, 136(a2)
	sw t3, 140(a2)
	lw t0, 128(a0)
	lw t1, 132(a0)
	slli t2, t1, 13
	srli a7, t0, 19
	or t2, t2, a7
	slli t3, t0, 13
	srli a7, t1, 19
	or t3, t3, a7
	sw t2, 64(a2)
	sw t3, 68(a2)
	lw t0, 168(a0)
	lw t1, 172(a0)
	slli t2, t0, 2
	srli a7, t1, 30
	or t2, t2, a7
	slli t3, t1, 2
	srli a7, t0, 30
	or t3, t3, a7
	sw t2, 192(a2)
	sw t3, 196(a2)
	lw t0, 16(a0)
	lw t1, 20(a0)
	slli t2, t1, 30
	srli a7, t0, 2
	or t2, t2, a7
	slli t3, t0, 30
	srli a7, t1, 2
	or t3, t3, a7
	sw t2, 160(a2)
	sw t3, 164(a2)
	lw t0, 56(a0)
	lw t1, 60(a0)
	slli t2, t0, 6
	srli a7, t1, 26
	or t2, t2, a7
	slli t3, t1, 6
	srli a7, t0, 26
	or t3, t3, a7
	sw t2, 88(a2)
	sw t3, 92(a2)
	lw t0, 96(a0)
	lw t1, 100(a0)
	slli t2, t1, 11
	srli a7, t0, 21
	or t2, t2, a7
	slli t3, t0, 11
	srli a7, t1, 21
	or t3, t3, a7
	sw t2, 16(a2)
	sw t3, 20(a2)
	lw t0, 136(a0)
	lw t1, 140(a0)
	slli t2, t0, 15
	srli a7, t1, 17
	or t2, t2, a7
	slli t3, t1, 15
	srli a7, t0, 17
	or t3, t3, a7
	sw t2, 144(a2)
	sw t3, 148(a2)
	lw t0, 176(a0)
	lw t1, 180(a0)
	slli t2, t1, 29
	srli a7, t0, 3
	or t2, t2, a7
	slli t3, t0, 29
	srli a7, t1, 3
	or t3, t3, a7
	sw t2, 72(a2)
	sw t3, 76(a2)
	lw t0, 24(a0)
	lw t1, 28(a0)
	slli t2, t0, 28
	srli a7, t1, 4
	or t2, t2, a7
	slli t3, t1, 28
	srli a7, t0, 4
	or t3, t3, a7
	sw t2, 40(a2)
	sw t3, 44(a2)
	lw t0, 64(a0)
	lw t1, 68(a0)
	slli t2, t1, 23
	srli a7, t0, 9
	or t2, t2, a7
	slli t3, t0, 23
	srli a7, t1, 9
	or t3, t3, a7
	sw t2, 168(a2)
	sw t3, 172(a2)
	lw t0, 104(a0)
	lw t1, 108(a0)
	slli t2, t0, 25
	srli a7, t1, 7
	or t2, t2, a7
	slli t3, t1, 25
	srli a7, t0, 7
	or t3, t3, a7
	sw t2, 96(a2)
	sw t3, 100(a2)
	lw t0, 144(a0)
	lw t1, 148(a0)
	slli t2, t0, 21
	srli a7, t1, 11
	or t2, t2, a7
	slli t3, t1, 21
	srli a7, t0, 11
	or t3, t3, a7
	sw t2, 24(a2)
	sw t3, 28(a2)
	lw t0, 184(a0)
	lw t1, 188(a0)
	slli t2, t1, 24
	srli a7, t0, 8
	or t2, t2, a7
	slli t3, t0, 24
	srli a7, t1, 8
	or t3, t3, a7
	sw t2, 152(a2)
	sw t3, 156(a2)
	lw t0, 32(a0)
	lw t1, 36(a0)
	slli t2, t0, 27
	srli a7, t1, 5
	or t2, t2, a7
	slli t3, t1, 27
	srli a7, t0, 5
	or t3, t3, a7
	sw t2, 120(a2)
	sw t3, 124(a2)
	lw t0, 72(a0)
	lw t1, 76(a0)
	slli t2, t0, 20
	srli a7, t1, 12
	or t2, t2, a7
	slli t3, t1, 20
	srli a7, t0, 12
	or t3, t3, a7
	sw t2, 48(a2)
	sw t3, 52(a2)
	lw t0, 112(a0)
	lw t1, 116(a0)
	slli t2, t1, 7
	srli a7, t0, 25
	or t2, t2, a7
	slli t3, t0, 7
	srli a7, t1, 25
	or t3, t3, a7
	sw t2, 176(a2)
	sw t3, 180(a2)
	lw t0, 152(a0)
	lw t1, 156(a0)
	slli t2, t0, 8
	srli a7, t1, 24
	or t2, t2, a7
	slli t3, t1, 8
	srli a7, t0, 24
	or t3, t3, a7
	sw t2, 104(a2)
	sw t3, 108(a2)
	lw t0, 192(a0)
	lw t1, 196(a0)
	slli t2, t0, 14
	srli a7, t1, 18
	or t2, t2, a7
	slli t3, t1, 14
	srli a7, t0, 18
	or t3, t3, a7
	sw t2, 32(a2)
	sw t3, 36(a2)
	lw t0, 0(a2)
	lw t1, 4(a2)
	lw t2, 8(a2)
	lw t3, 12(a2)
	lw t4, 16(a2)
	lw t5, 20(a2)
	lw t6, 24(a2)
	lw a4, 28(a2)
	lw a5, 32(a2)
	lw a6, 36(a2)
	xori a7, t2, -1
	and a7, a7, t4
	xor a7, a7, t0
	sw a7, 0(a0)
	xori a7, t3, -1
	and a7, a7, t5
	xor a7, a7, t1
	sw a7, 4(a0)
	xori a7, t4, -1
	and a7, a7, t6
	xor a7, a7, t2
	sw a7, 8(a0)
	xori a7, t5, -1
	and a7, a7, a4
	xor a7, a7, t3
	sw a7, 12(a0)
	xori a7, t6, -1
	and a7, a7, a5
	xor a7, a7, t4
	sw a7, 16(a0)
	xori a7, a4, -1
	and a7, a7, a6
	xor a7, a7, t5
	sw a7, 20(a0)
	xori a7, a5, -1
	and a7, a7, t0
	xor a7, a7, t6
	sw a7, 24(a0)
	xori a7, a6, -1
	and a7, a7, t1
	xor a7, a7, a4
	sw a7, 28(a0)
	xori a7, t0, -1
	and a7, a7, t2
	xor a7, a7, a5
	sw a7, 32(a0)
	xori a7, t1, -1
	and a7, a7, t3
	xor a7, a7, a6
	sw a7, 36(a0)
	lw t0, 40(a2)
	lw t1, 44(a2)
	lw t2, 48(a2)
	lw t3, 52(a2)
	lw t4, 56(a2)
	lw t5, 60(a2)
	lw t6, 64(a2)
	lw a4, 68(a2)
	lw a5, 72(a2)
	lw a6, 76(a2)
	xori a7, t2, -1
	and a7, a7, t4
	xor a7, a7, t0
	sw a7, 40(a0)
	xori a7, t3, -1
	and a7, a7, t5
	xor a7, a7, t1
	sw a7, 44(a0)
	xori a7, t4, -1
	and a7, a7, t6
	xor a7, a7, t2
	sw a7, 48(a0)
	xori a7, t5, -1
	and a7, a7, a4
	xor a7, a7, t3
	sw a7, 52(a0)
	xori a7, t6, -1
	and a7, a7, a5
	xor a7, a7, t4
	sw a7, 56(a0)
	xori a7, a4, -1
	and a7, a7, a6
	xor a7, a7, t5
	sw a7, 60(a0)
	xori a7, a5, -1
	and a7, a7, t0
	xor a7, a7, t6
	sw a7, 64(a0)
	xori a7, a6, -1
	and a7, a7, t1
	xor a7, a7, a4
	sw a7, 68(a0)
	xori a7, t0, -1
	and a7, a7, t2
	xor a7, a7, a5
	sw a7, 72(a0)
	xori a7, t1, -1
	and a7, a7, t3
	xor a7, a7, a6
	sw a7, 76(a0)
	lw t0, 80(a2)
	lw t1, 84(a2)
	lw t2, 88(a2)
	lw t3, 92(a2)
	lw t4, 96(a2)
	lw t5, 100(a2)
	lw t6, 104(a2)
	lw a4, 108(a2)
	lw a5, 112(a2)
	lw a6, 116(a2)
	xori a7, t2, -1
	and a7, a7, t4
	xor a7, a7, t0
	sw a7, 80(a0)
	xori a7, t3, -1
	and a7, a7, t5
	xor a7, a7, t1
	sw a7, 84(a0)
	xori a7, t4, -1
	and a7, a7, t6
	xor a7, a7, t2
	sw a7, 88(a0)
	xori a7, t5, -1
	and a7, a7, a4
	xor a7, a7, t3
	sw a7, 92(a0)
	xori a7, t6, -1
	and a7, a7, a5
	xor a7, a7, t4
	sw a7, 96(a0)
	xori a7, a4, -1
	and a7, a7, a6
	xor a7, a7, t5
	sw a7, 100(a0)
	xori a7, a5, -1
	and a7, a7, t0
	xor a7, a7, t6
	sw a7, 104(a0)
	xori a7, a6, -1
	and a7, a7, t1
	xor a7, a7, a4
	sw a7, 108(a0)
	xori a7, t0, -1
	and a7, a7, t2
	xor a7, a7, a5
	sw a7, 112(a0)
	xori a7, t1, -1
	and a7, a7, t3
	xor a7, a7, a6
	sw a7, 116(a0)
	lw t0, 120(a2)
	lw t1, 124(a2)
	lw t2, 128(a2)
	lw t3, 132(a2)
	lw t4, 136(a2)
	lw t5, 140(a2)
	lw t6, 144(a2)
	lw a4, 148(a2)
	lw a5, 152(a2)
	lw a6, 156(a2)
	xori a7, t2, -1
	and a7, a7, t4
	xor a7, a7, t0
	sw a7, 120(a0)
	xori a7, t3, -1
	and a7, a7, t5
	xor a7, a7, t1
	sw a7, 124(a0)
	xori a7, t4, -1
	and a7, a7, t6
	xor a7, a7, t2
	sw a7, 128(a0)
	xori a7, t5, -1
	and a7, a7, a4
	xor a7, a7, t3
	sw a7, 132(a0)
	xori a7, t6, -1
	and a7, a7, a5
	xor a7, a7, t4
	sw a7, 136(a0)
	xori a7, a4, -1
	and a7, a7, a6
	xor a7, a7, t5
	sw a7, 140(a0)
	xori a7, a5, -1
	and a7, a7, t0
	xor a7, a7, t6
	sw a7, 144(a0)
	xori a7, a6, -1
	and a7, a7, t1
	xor a7, a7, a4
	sw a7, 148(a0)
	xori a7, t0, -1
	and a7, a7, t2
	xor a7, a7, a5
	sw a7, 152(a0)
	xori a7, t1, -1
	and a7, a7, t3
	xor a7, a7, a6
	sw a7, 156(a0)
	lw t0, 160(a2)
	lw t1, 164(a2)
	lw t2, 168(a2)
	lw t3, 172(a2)
	lw t4, 176(a2)
	lw t5, 180(a2)
	lw t6, 184(a2)
	lw a4, 188(a2)
	lw a5, 192(a2)
	lw a6, 196(a2)
	xori a7, t2, -1
	and a7, a7, t4
	xor a7, a7, t0
	sw a7, 160(a0)
	xori a7, t3, -1
	and a7, a7, t5
	xor a7, a7, t1
	sw a7, 164(a0)
	xori a7, t4, -1
	and a7, a7, t6
	xor a7, a7, t2
	sw a7, 168(a0)
	xori a7, t5, -1
	and a7, a7, a4
	xor a7, a7, t3
	sw a7, 172(a0)
	xori a7, t6, -1
	and a7, a7, a5
	xor a7, a7, t4
	sw a7, 176(a0)
	xori a7, a4, -1
	and a7, a7, a6
	xor a7, a7, t5
	sw a7, 180(a0)
	xori a7, a5, -1
	and a7, a7, t0
	xor a7, a7, t6
	sw a7, 184(a0)
	xori a7, a6, -1
	and a7, a7, t1
	xor a7, a7, a4
	sw a7, 188(a0)
	xori a7, t0, -1
	and a7, a7, t2
	xor a7, a7, a5
	sw a7, 192(a0)
	xori a7, t1, -1
	and a7, a7, t3
	xor a7, a7, a6
	sw a7, 196(a0)
	lw t0, 0(a1)
	lw t1, 4(a1)
	lw t2, 0(a0)
	xor t2, t2, t0
	sw t2, 0(a0)
	lw t2, 4(a0)
	xor t2, t2, t1
	sw t2, 4(a0)
	addi a1, a1, 8
	addi    a3, a3, -1
	beqz    a3, done
	j       round
done:
