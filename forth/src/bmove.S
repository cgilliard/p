# bmove ( src dst n -- )   copy n bytes; the ranges may overlap: backward
# when dst is inside src's range, else forward (src/btree.fam).  A word at a
# time when src, dst and n are all multiples of 4.
	.option norelax
	lw      a2, 0(sp)               # n
	lw      a1, 4(sp)               # dst
	lw      a0, 8(sp)               # src
	addi    sp, sp, 12
	beqz    a2, done
	or      t1, a0, a1
	or      t1, t1, a2
	andi    t1, t1, 3               # t1: 0 if all aligned
	bgeu    a0, a1, fwd             # dst at or below src: forward
	add     t2, a0, a2
	bgeu    a1, t2, fwd             # dst past src's end: forward
	add     a0, a0, a2              # backward, from the ends
	add     a1, a1, a2
	bnez    t1, bback
wback:
	addi    a0, a0, -4
	addi    a1, a1, -4
	lw      t0, 0(a0)
	sw      t0, 0(a1)
	addi    a2, a2, -4
	bnez    a2, wback
	j       done
bback:
	addi    a0, a0, -1
	addi    a1, a1, -1
	lbu     t0, 0(a0)
	sb      t0, 0(a1)
	addi    a2, a2, -1
	bnez    a2, bback
	j       done
fwd:
	bnez    t1, bfwd
wfwd:
	lw      t0, 0(a0)
	sw      t0, 0(a1)
	addi    a0, a0, 4
	addi    a1, a1, 4
	addi    a2, a2, -4
	bnez    a2, wfwd
	j       done
bfwd:
	lbu     t0, 0(a0)
	sb      t0, 0(a1)
	addi    a0, a0, 1
	addi    a1, a1, 1
	addi    a2, a2, -1
	bnez    a2, bfwd
done:
