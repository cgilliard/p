# nzero ( a n -- )   n zero bytes (n may be 0): src/diff.fam.  A word at a
# time when a and n are multiples of 4.
	.option norelax
	lw      a2, 0(sp)               # n
	lw      a1, 4(sp)               # a
	addi    sp, sp, 8
	beqz    a2, done
	or      t1, a1, a2
	andi    t1, t1, 3
	bnez    t1, bytes
words:
	sw      zero, 0(a1)
	addi    a1, a1, 4
	addi    a2, a2, -4
	bnez    a2, words
	j       done
bytes:
	sb      zero, 0(a1)
	addi    a1, a1, 1
	addi    a2, a2, -1
	bnez    a2, bytes
done:
