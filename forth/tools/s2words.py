#!/usr/bin/env python3
"""s2words -- assemble a fragment of RV32I (e.g. src/p2core.S) into fam words:
one `XXXXXXXX ,` line per instruction, with its disassembly as a comment, to
paste into a `:` word's body.  The fragment runs inline: it may branch within
itself (branches are resolved by linking), never call or jump out of it.

Usage: s2words.py INPUT.S

Requires the riscv64 bare-metal toolchain (as/ld/objdump/objcopy).
"""

import os
import re
import subprocess
import sys
import tempfile

AS = "riscv64-unknown-elf-as"
LD = "riscv64-unknown-elf-ld"
ODUMP = "riscv64-unknown-elf-objdump"
OBJCOPY = "riscv64-unknown-elf-objcopy"


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    src = sys.argv[1]
    with tempfile.TemporaryDirectory() as td:
        obj, elf, binf = (os.path.join(td, n) for n in ("t.o", "t.elf", "t.bin"))
        subprocess.run([AS, "-march=rv32i", "-mabi=ilp32", "-o", obj, src], check=True)
        subprocess.run([LD, "-m", "elf32lriscv", "-Ttext=0", "-e", "0", "-o", elf, obj], check=True)
        subprocess.run([OBJCOPY, "-O", "binary", elf, binf], check=True)
        image = open(binf, "rb").read()
        dis = subprocess.run([ODUMP, "-d", "-M", "no-aliases", elf], check=True,
                             capture_output=True, text=True).stdout
    asm = {}
    for ln in dis.splitlines():
        m = re.match(r"^\s*([0-9a-f]+):\t[0-9a-f]{8}\s+(.*)$", ln)
        if m:
            asm[int(m.group(1), 16)] = re.sub(r"\s+", " ", m.group(2)).strip()
    if "jalr" in " ".join(asm.values()):
        sys.exit("s2words: jalr in the fragment")
    for off in range(0, len(image), 4):
        word = image[off:off + 4]
        print(f"{word.hex().upper()} ,   \\ {asm.get(off, '')}")


if __name__ == "__main__":
    sys.exit(main())
