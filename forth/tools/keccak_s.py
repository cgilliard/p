#!/usr/bin/env python3
"""keccak_s -- write src/keccak.S: Keccak-f[1600] in RV32I, unrolled.

Usage: keccak_s.py > src/keccak.S   (then tools/s2words.py src/keccak.S)

A lane is two words (low first, as the state's bytes lie little-endian);
rotations are by constants, so each is three or six shifts and ors.
"""

# rho's rotation r[x][y]
R = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56], [27, 20, 39, 8, 14]]


def lane(x, y):
    return 8 * (x + 5 * y)


def rot(out, dlo, dhi, slo, shi, n):
    """(dlo, dhi) = (slo, shi) rotated left n bits; a7 is scratch."""
    if n == 0:
        out += [f"mv {dlo}, {slo}", f"mv {dhi}, {shi}"]
    elif n == 32:
        out += [f"mv {dlo}, {shi}", f"mv {dhi}, {slo}"]
    else:
        lo, hi, m = (slo, shi, n) if n < 32 else (shi, slo, n - 32)
        out += [f"slli {dlo}, {lo}, {m}", f"srli a7, {hi}, {32 - m}", f"or {dlo}, {dlo}, a7",
                f"slli {dhi}, {hi}, {m}", f"srli a7, {lo}, {32 - m}", f"or {dhi}, {dhi}, a7"]


def main():
    o = []
    # theta: C[x] = A[x,0] ^ .. ^ A[x,4], into the scratch at 200
    for x in range(5):
        o += [f"lw t0, {lane(x, 0)}(a0)", f"lw t1, {lane(x, 0) + 4}(a0)"]
        for y in range(1, 5):
            o += [f"lw t2, {lane(x, y)}(a0)", "xor t0, t0, t2", f"lw t2, {lane(x, y) + 4}(a0)", "xor t1, t1, t2"]
        o += [f"sw t0, {200 + 8 * x}(a2)", f"sw t1, {204 + 8 * x}(a2)"]
    # D[x] = C[x-1] ^ rot(C[x+1], 1), into every lane of column x
    for x in range(5):
        xm, xp = (x - 1) % 5, (x + 1) % 5
        o += [f"lw t0, {200 + 8 * xp}(a2)", f"lw t1, {204 + 8 * xp}(a2)"]
        rot(o, "t2", "t3", "t0", "t1", 1)
        o += [f"lw t5, {200 + 8 * xm}(a2)", f"lw t6, {204 + 8 * xm}(a2)", "xor t2, t2, t5", "xor t3, t3, t6"]
        for y in range(5):
            o += [f"lw t4, {lane(x, y)}(a0)", "xor t4, t4, t2", f"sw t4, {lane(x, y)}(a0)",
                  f"lw t4, {lane(x, y) + 4}(a0)", "xor t4, t4, t3", f"sw t4, {lane(x, y) + 4}(a0)"]
    # rho and pi: B[y, 2x + 3y] = rot(A[x, y], r[x][y]), into the scratch
    for x in range(5):
        for y in range(5):
            o += [f"lw t0, {lane(x, y)}(a0)", f"lw t1, {lane(x, y) + 4}(a0)"]
            rot(o, "t2", "t3", "t0", "t1", R[x][y])
            b = lane(y, (2 * x + 3 * y) % 5)
            o += [f"sw t2, {b}(a2)", f"sw t3, {b + 4}(a2)"]
    # chi: A[x, y] = B[x, y] ^ (~B[x+1, y] & B[x+2, y])
    regs = [("t0", "t1"), ("t2", "t3"), ("t4", "t5"), ("t6", "a4"), ("a5", "a6")]
    for y in range(5):
        for x in range(5):
            o += [f"lw {regs[x][0]}, {lane(x, y)}(a2)", f"lw {regs[x][1]}, {lane(x, y) + 4}(a2)"]
        for x in range(5):
            a, b, c = regs[x], regs[(x + 1) % 5], regs[(x + 2) % 5]
            for h in range(2):
                o += [f"xori a7, {b[h]}, -1", f"and a7, a7, {c[h]}", f"xor a7, a7, {a[h]}", f"sw a7, {lane(x, y) + 4 * h}(a0)"]
    # iota: the round's constant, from the table at a1
    o += ["lw t0, 0(a1)", "lw t1, 4(a1)", "lw t2, 0(a0)", "xor t2, t2, t0", "sw t2, 0(a0)",
          "lw t2, 4(a0)", "xor t2, t2, t1", "sw t2, 4(a0)", "addi a1, a1, 8"]

    print("""# kf1600 ( state rc scratch -- )   Keccak-f[1600], the 24 rounds: the state
# (200 bytes, 25 lanes of two words, low first), the round constants (24
# lanes, from src/keccak.fam), a scratch of 240 bytes.  Written by
# tools/keccak_s.py; assembled by tools/s2words.py.
	.option norelax
	lw      a2, 0(sp)               # scratch
	lw      a1, 4(sp)               # round constants
	lw      a0, 8(sp)               # state
	addi    sp, sp, 12
	li      a3, 24
round:""")
    for line in o:
        print("\t" + line)
    print("""	addi    a3, a3, -1
	beqz    a3, done
	j       round
done:""")


main()
