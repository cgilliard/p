#!/usr/bin/env python3
"""s2fam0_tabernacle — convert src/tabernacle.S into the fam0 hex format that
bin/fam0 compiles into bin/tabernacle.

This is the TABERNACLE generator.  It is deliberately separate from
tools/s2fam0_fam.py (the fam-compiler generator) because the two targets differ
in one crucial way:

  * tools/s2fam0_fam.py (fam):  PREPENDS a `13 00 00 00` nop as the q32 magic
    word, matching scripts/build.sh's injected header for the fam binary.
  * this tool (tabernacle): prepends NOTHING — src/tabernacle.S supplies its
    own first instruction (`addi zero, zero, 0`, the q32 magic), and the result
    is run through bin/fam0 with no injected header.

Both tools share the same hard-won lesson: the bytes must come from a LINKED
object, not a raw `as` listing/object.  tabernacle.S uses LOAD_ADDRESS (an
auipc+addi macro) whose two words carry a PC-relative relocation that `as`
leaves as a placeholder (`auipc gp,0; addi gp,gp,0`) and only the linker
resolves (`auipc gp,0x1; addi gp,gp,904`).  Scraping the un-relocated bytes
silently ships a broken gp.  So we: assemble (-g) -> link at the load address
-> objdump -dl -> emit resolved little-endian bytes with source comments.

Round-trip invariant: compiling the generated .fam0 with bin/fam0 reproduces
the exact binary that `as`+`ld` produce from src/tabernacle.S.  After editing
src/tabernacle.S, regenerate and commit the .fam0.

The fam0 format is one instruction (or .word data) per line as 4 little-endian
hex bytes followed by a `#` source comment, e.g.

    97 11 00 00	# auipc	gp,0x1

`#`-comment lines and blank lines are ignored by bin/fam0.

Usage: s2fam0_tabernacle.py INPUT.S [OUTPUT.fam0]
       (OUTPUT omitted -> stdout)

Requires the riscv64 bare-metal toolchain (as/ld/objdump) + Python 3.  The .S
may `.include` sibling files (e.g. src/tabernacle_dat.S); run from the repo
root so those relative paths resolve.
"""

import os
import re
import subprocess
import sys
import tempfile

AS = "riscv64-unknown-elf-as"
LD = "riscv64-unknown-elf-ld"
ODUMP = "riscv64-unknown-elf-objdump"
MARCH = "rv32i"
MABI = "ilp32"
# tabernacle is loaded here by QEMU.  Its LOAD_ADDRESS/auipc relocations are
# PC-relative so the encoding is base-independent, but we link at the true base
# anyway so any absolute reference resolves correctly and disassembly comments
# show real addresses.
TEXT_BASE = "0x80000000"


def main():
    if len(sys.argv) < 2:
        sys.exit("usage: s2fam0_tabernacle.py INPUT.S [OUTPUT.fam0]")
    src = sys.argv[1]
    dst = sys.argv[2] if len(sys.argv) > 2 else None
    if not os.path.isfile(src):
        sys.exit(f"s2fam0_tabernacle: input not found: {src}")
    src_abs = os.path.abspath(src)

    with tempfile.TemporaryDirectory() as td:
        obj = os.path.join(td, "t.o")
        elf = os.path.join(td, "t.elf")
        # -g so objdump -dl can map each instruction back to its source line.
        subprocess.run(
            [AS, "-g", f"-march={MARCH}", f"-mabi={MABI}", "-o", obj, src],
            check=True,
        )
        subprocess.run(
            [LD, "-m", "elf32lriscv", f"-Ttext={TEXT_BASE}", "-o", elf, obj],
            check=True,
        )
        dis = subprocess.run(
            [ODUMP, "-dl", elf], check=True, capture_output=True, text=True
        ).stdout

    # objdump -dl interleaves source-line markers with instructions, in address
    # order.  A `file:NNN` line sets the current source line; instruction lines
    # look like:  "80000004:\t00001197          \tauipc\tgp,0x1"
    line_re = re.compile(r"^(\S*):(\d+)$")
    insn_re = re.compile(r"^\s*[0-9a-f]+:\t([0-9a-f]{8})\s+(.*)$")
    insns = []  # (src_file, src_line, value_hex, disasm)
    cur_file, cur_line = src_abs, 0
    for ln in dis.splitlines():
        m = line_re.match(ln)
        if m:
            cur_file, cur_line = m.group(1), int(m.group(2))
            continue
        m = insn_re.match(ln)
        if m:
            asm = re.sub(r"\s+", " ", m.group(2)).strip()
            insns.append((cur_file, cur_line, m.group(1), asm))

    if not insns:
        sys.exit("s2fam0_tabernacle: objdump produced no instructions")

    srclines = open(src, encoding="utf-8").read().splitlines()

    def comment(line):
        s = line.rstrip()
        if s.strip() == "":
            return ""
        # Already a comment? keep as-is; otherwise comment-ize so fam0 ignores
        # it (code lines start with hex-ish chars fam0 would try to parse).
        return s if s.lstrip().startswith("#") else "# " + s

    fh = open(dst, "w", encoding="utf-8") if dst else sys.stdout
    w = lambda s="": print(s, file=fh)

    # Emit each instruction as 4 little-endian bytes.  objdump prints the word
    # MSB-first ("00001197"), so reverse to memory order ("97 11 00 00").  For
    # lines that come from the main source file, also echo the intervening
    # source text (headers, labels, comments) so the .fam0 stays readable; for
    # words from .include'd files we skip that (their line numbers index a
    # different file) and rely on the disasm comment.
    last = 0
    for (sfile, sl, val, asm) in insns:
        if sfile == src_abs and sl > last:
            for k in range(last, sl):
                if k < len(srclines):
                    w(comment(srclines[k]))
            last = sl
        le = f"{val[6:8]} {val[4:6]} {val[2:4]} {val[0:2]}".upper()
        w(f"{le}\t# {asm}")

    if fh is not sys.stdout:
        fh.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
