# mcmp ( a b n -- c )   compare n bytes, unsigned: -1, 0 or 1, at the first
# that differs (src/btree.fam).
	.option norelax
	lw      a2, 0(sp)               # n
	lw      a1, 4(sp)               # b
	lw      a0, 8(sp)               # a
	addi    sp, sp, 8               # three in, one out
	li      t2, 0
	beqz    a2, done
next:
	lbu     t0, 0(a0)
	lbu     t1, 0(a1)
	bne     t0, t1, differ
	addi    a0, a0, 1
	addi    a1, a1, 1
	addi    a2, a2, -1
	bnez    a2, next
	j       done
differ:
	li      t2, 1
	bgeu    t0, t1, done
	li      t2, -1
done:
	sw      t2, 0(sp)
