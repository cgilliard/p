# hbadd ( dst a m -- )   add m elements packed 3 bytes each, little-endian,
# at a into the m cells at dst (mod p): the byte hasher's rate, a block of
# elements at a time (src/poseidon2.fam, hbytes).  An element is < 2^24, so
# a cell + one is < 2p: one branch-free reduction.
	.option norelax
	lw      a2, 0(sp)               # m
	lw      a1, 4(sp)               # a
	lw      a0, 8(sp)               # dst
	addi    sp, sp, 12
	lui     t2, 0x78000
	addi    t2, t2, 1               # p
	beqz    a2, done
next:
	lbu     t0, 0(a1)
	lbu     t1, 1(a1)
	slli    t1, t1, 8
	or      t0, t0, t1
	lbu     t1, 2(a1)
	slli    t1, t1, 16
	or      t0, t0, t1              # the element
	lw      t1, 0(a0)
	add     t1, t1, t0
	sltu    t3, t1, t2
	addi    t3, t3, -1
	and     t3, t3, t2
	sub     t1, t1, t3
	sw      t1, 0(a0)
	addi    a1, a1, 3
	addi    a0, a0, 4
	addi    a2, a2, -1
	bnez    a2, next
done:
