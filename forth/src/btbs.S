# btbs ( key ks base stride n strict -- j )   a binary search of the n keys
# (ks bytes each, stride bytes apart from base) of a B+tree node, compared
# as unsigned bytes with the key: strict 0, the first j whose key is >= the
# key (a leaf's place: btpos); strict 1, how many keys are <= it (the child
# to go down: btchild).  j may be n.  (src/btree.fam; no multiply: RV32I.)
	.option norelax
	lw      a5, 0(sp)               # strict
	lw      a4, 4(sp)               # n: hi
	lw      a3, 8(sp)               # stride
	lw      a2, 12(sp)              # base
	lw      a1, 16(sp)              # ks
	lw      a0, 20(sp)              # key
	addi    sp, sp, 20              # six in, one out
	li      t3, 0                   # lo
loop:
	bgeu    t3, a4, done
	add     t4, t3, a4
	srli    t4, t4, 1               # mid
	mv      t5, a2                  # base + mid * stride, by shifts and adds
	mv      t0, t4
	mv      t1, a3
mul:
	beqz    t0, cmp0
	andi    t2, t0, 1
	beqz    t2, mul2
	add     t5, t5, t1
mul2:
	slli    t1, t1, 1
	srli    t0, t0, 1
	j       mul
cmp0:
	li      t2, 0                   # key mid against the key: -1, 0, 1
	mv      t0, t5
	mv      t1, a0
	mv      t6, a1
cmp:
	beqz    t6, cmpd
	lbu     a6, 0(t0)
	lbu     a7, 0(t1)
	bne     a6, a7, cmpne
	addi    t0, t0, 1
	addi    t1, t1, 1
	addi    t6, t6, -1
	j       cmp
cmpne:
	li      t2, 1
	bgeu    a6, a7, cmpd
	li      t2, -1
cmpd:
	bltz    t2, right               # below the key: right
	bnez    t2, left                # above: left
	beqz    a5, left                # equal: left for btpos, right for btchild
right:
	addi    t3, t4, 1
	j       loop
left:
	mv      a4, t4
	j       loop
done:
	sw      t3, 0(sp)
