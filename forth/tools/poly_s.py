#!/usr/bin/env python3
"""poly_s -- write src/poly.S: one Poly1305 block (RFC 8439) in RV32I, after
poly1305-donna's 32-bit layout: the accumulator h and the key r as five
26-bit limbs, h = (h + block) * r mod 2^130 - 5.  RV32I has no multiply:
each limb product is a shift-and-add loop into a 64-bit sum.

Usage: poly_s.py > src/poly.S   (then tools/s2words.py src/poly.S)
"""

H = ["t0", "t1", "t2", "t3", "t4"]


def mulacc(o, x_mem, y_reg):
    """(a4, a5) += h[x] * y: a6 the multiplier's bits, (a7, t5) the shifted
    multiplicand, t6 scratch."""
    o += [f"mv a6, {x_mem}", f"mv a7, {y_reg}", "li t5, 0",
          "1:", "andi t6, a6, 1", "beqz t6, 2f",
          "add a4, a4, a7", "sltu t6, a4, a7", "add a5, a5, t5", "add a5, a5, t6",
          "2:", "slli t5, t5, 1", "srli t6, a7, 31", "or t5, t5, t6", "slli a7, a7, 1",
          "srli a6, a6, 1", "bnez a6, 1b"]


def main():
    o = []
    # the block, as five limbs, added to h (in t0..t4)
    o += ["lw t0, 0(a0)", "lw t1, 4(a0)", "lw t2, 8(a0)", "lw t3, 12(a0)", "lw t4, 16(a0)"]
    for k in range(4):                                   # the block's words, little-endian, into a4..a7
        r = ["a4", "a5", "a6", "a7"][k]
        o += [f"lbu {r}, {4 * k}(a2)"]
        for b in range(1, 4):
            o += [f"lbu t5, {4 * k + b}(a2)", f"slli t5, t5, {8 * b}", f"or {r}, {r}, t5"]
    o += ["lui t6, 0x4000", "addi t6, t6, -1",           # the limb mask, 2^26 - 1
          "and t5, a4, t6", "add t0, t0, t5",
          "srli t5, a4, 26", "slli a4, a5, 6", "or t5, t5, a4", "and t5, t5, t6", "add t1, t1, t5",
          "srli t5, a5, 20", "slli a5, a6, 12", "or t5, t5, a5", "and t5, t5, t6", "add t2, t2, t5",
          "srli t5, a6, 14", "slli a6, a7, 18", "or t5, t5, a6", "and t5, t5, t6", "add t3, t3, t5",
          "srli t5, a7, 8", "or t5, t5, a3", "add t4, t4, t5"]
    # d_j = sum h_i * (r or 5r), into the scratch below sp: d_j at -8(j+1)
    # r at a1: r0..r4 at 0..16, 5r1..5r4 at 20..32
    R = lambda k: f"{4 * k}(a1)"
    S = lambda k: f"{16 + 4 * k}(a1)"                    # 5 r_k, k = 1..4
    terms = [
        [(0, R(0)), (1, S(4)), (2, S(3)), (3, S(2)), (4, S(1))],
        [(0, R(1)), (1, R(0)), (2, S(4)), (3, S(3)), (4, S(2))],
        [(0, R(2)), (1, R(1)), (2, R(0)), (3, S(4)), (4, S(3))],
        [(0, R(3)), (1, R(2)), (2, R(1)), (3, R(0)), (4, S(4))],
        [(0, R(4)), (1, R(3)), (2, R(2)), (3, R(1)), (4, R(0))],
    ]
    for j, ts in enumerate(terms):
        o += ["li a4, 0", "li a5, 0"]
        for (i, m) in ts:
            o += [f"lw a3, {m}"]
            mulacc(o, H[i], "a3")
        o += [f"sw a4, {-8 * (j + 1)}(sp)", f"sw a5, {-8 * (j + 1) + 4}(sp)"]
    # the carries: h_j = d_j mod 2^26, d_{j+1} += d_j >> 26; then h0 += 5 (d_4 >> 26)
    o += ["lui t6, 0x4000", "addi t6, t6, -1"]           # the mask again (mulacc used t6)
    o += ["li a6, 0"]                                    # the carry
    for j in range(5):
        o += [f"lw a4, {-8 * (j + 1)}(sp)", f"lw a5, {-8 * (j + 1) + 4}(sp)",
              "add a4, a4, a6", "sltu t5, a4, a6", "add a5, a5, t5",
              f"and {H[j]}, a4, t6", "srli a6, a4, 26", "slli a5, a5, 6", "or a6, a6, a5"]
    o += ["slli t5, a6, 2", "add a6, a6, t5", "add t0, t0, a6",      # 5c
          "srli a6, t0, 26", "and t0, t0, t6", "add t1, t1, a6"]
    o += ["sw t0, 0(a0)", "sw t1, 4(a0)", "sw t2, 8(a0)", "sw t3, 12(a0)", "sw t4, 16(a0)"]

    print("""# p1blk ( h r m hibit -- )   one Poly1305 block: h = (h + m + hibit 2^128) r
# mod 2^130 - 5, h and r (and 5r) as 26-bit limbs: h at a0 (5 words,
# updated), r at a1 (r0..r4, then 5r1..5r4), the 16 bytes at a2, hibit (2^24,
# or 0 for a last block padded by hand) in a3.  Written by tools/poly_s.py;
# assembled by tools/s2words.py.
	.option norelax
	lw      a3, 0(sp)               # hibit
	lw      a2, 4(sp)               # the block
	lw      a1, 8(sp)               # r
	lw      a0, 12(sp)              # h
	addi    sp, sp, 16""")
    for line in o:
        print(("" if line.endswith(":") else "\t") + line)


main()
