#!/usr/bin/env python3
"""chacha_s -- write src/chacha.S: the ChaCha20 block function (RFC 8439) in
RV32I, the 20 rounds' quarter-rounds unrolled within a loop of 10.

Usage: chacha_s.py > src/chacha.S   (then tools/s2words.py src/chacha.S)
"""

X = ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "t0", "t1", "t2", "t3", "t4", "t5", "t6", "s0"]


def qr(o, a, b, c, d):
    a, b, c, d = X[a], X[b], X[c], X[d]
    for (p, q, r, n) in ((a, b, d, 16), (c, d, b, 12), (a, b, d, 8), (c, d, b, 7)):
        # p += q; r ^= p; r <<<= n
        o += [f"add {p}, {p}, {q}", f"xor {r}, {r}, {p}", f"slli s4, {r}, {n}", f"srli {r}, {r}, {32 - n}", f"or {r}, {r}, s4"]


def main():
    o = []
    for q in ((0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15),
              (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)):
        qr(o, *q)
    print("""# chblk ( in out -- )   the ChaCha20 block function: 16 words in (the
# constants, key, counter, nonce), 16 words out (the rounds' result plus the
# input: the keystream).  s0, s2 and s4 are saved on the data stack.  Written
# by tools/chacha_s.py; assembled by tools/s2words.py.
	.option norelax
	addi    sp, sp, -12
	sw      s0, 0(sp)
	sw      s2, 4(sp)
	sw      s4, 8(sp)
	lw      s2, 16(sp)              # in""")
    for i, r in enumerate(X):
        print(f"\tlw      {r}, {4 * i}(s2)")
    print("\tli      s2, 10\nround:")
    for line in o:
        print("\t" + line)
    print("""	addi    s2, s2, -1
	beqz    s2, out
	j       round
out:
	sw      s0, -4(sp)              # x15, to free s0
	lw      s2, 16(sp)              # in
	lw      s4, 12(sp)              # out""")
    for i, r in enumerate(X):
        if r == "s0":
            print("\tlw      s0, -4(sp)")
        # out[i] = x_i + in[i], using s0 as the scratch until x15's turn
        tmp = "s0" if i < 15 else "a0"
        print(f"\tlw      {tmp}, {4 * i}(s2)\n\tadd     {r}, {r}, {tmp}\n\tsw      {r}, {4 * i}(s4)")
    print("""	lw      s0, 0(sp)
	lw      s2, 4(sp)
	lw      s4, 8(sp)
	addi    sp, sp, 20              # the three saved, and the two arguments""")


main()
