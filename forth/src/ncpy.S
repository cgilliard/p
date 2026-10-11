# ncpy ( src dst n -- )   copy n bytes forward (n may be 0): src/diff.fam.
# A word at a time when src, dst and n are all multiples of 4.
	.option norelax
	lw      a2, 0(sp)               # n
	lw      a1, 4(sp)               # dst
	lw      a0, 8(sp)               # src
	addi    sp, sp, 12
	beqz    a2, done
	or      t1, a0, a1
	or      t1, t1, a2
	andi    t1, t1, 3
	bnez    t1, bytes
words:
	lw      t0, 0(a0)
	sw      t0, 0(a1)
	addi    a0, a0, 4
	addi    a1, a1, 4
	addi    a2, a2, -4
	bnez    a2, words
	j       done
bytes:
	lbu     t0, 0(a0)
	sb      t0, 0(a1)
	addi    a0, a0, 1
	addi    a1, a1, 1
	addi    a2, a2, -1
	bnez    a2, bytes
done:
