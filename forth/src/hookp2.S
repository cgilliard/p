# hookp2 -- run at compile time (a :I body): point p2hook (src/poseidon2.fam),
# whose body starts with a `jal x0, +4` (a no-op), at here: find its entry in
# the compiler's name table (s7 .. s6, 20-byte entries: name lo, hi, kind,
# field0 = entry, field1), and rewrite that first instruction as a jal to the
# output cursor (gp).  Not found, or out of a jal's reach: '?' and the build
# stops, as the compiler's own panic does.
	.option norelax
	li      t5, 0x6F683270          # "p2ho"
	li      t6, 0x00006B6F          # "ok"
	mv      t0, s7
look:
	bgeu    t0, s6, fail
	lw      t1, 0(t0)
	bne     t1, t5, next
	lw      t1, 4(t0)
	bne     t1, t6, next
	lw      t1, 8(t0)
	li      t2, 1                   # a ':' word
	bne     t1, t2, next
	lw      t0, 12(t0)              # its entry: the jal to rewrite
	j       found
next:
	addi    t0, t0, 20
	j       look
found:
	sub     t1, gp, t0              # the offset, here - entry
	srai    t2, t1, 20
	beqz    t2, ok
	li      t3, -1
	bne     t2, t3, fail            # beyond +-1 MiB
ok:
	li      t2, 0x6F                # jal x0, offset
	srli    t3, t1, 12
	andi    t3, t3, 0xFF
	slli    t3, t3, 12
	or      t2, t2, t3
	srli    t3, t1, 11
	andi    t3, t3, 1
	slli    t3, t3, 20
	or      t2, t2, t3
	srli    t3, t1, 1
	andi    t3, t3, 0x3FF
	slli    t3, t3, 21
	or      t2, t2, t3
	srli    t3, t1, 20
	andi    t3, t3, 1
	slli    t3, t3, 31
	or      t2, t2, t3
	sw      t2, 0(t0)
	j       end
fail:
	lui     t0, 0x10000             # UART: '?'
	li      t1, 0x3F
	sb      t1, 0(t0)
	li      t1, 0x0A
	sb      t1, 0(t0)
	lui     t0, 0x100               # the test finisher: fail
	lui     t1, 0x13
	addi    t1, t1, 0x333
	sw      t1, 0(t0)
spin:
	j       spin
end:
