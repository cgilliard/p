# MIT License
#
# Copyright (c) 2026 Christopher Gilliard
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

# Register convention:
#   gp  = heap pointer (output cursor; input then output live here)
#   sp  = fam internal stack pointer
#   tp  = cstack pointer (the program's compile-time data stack)
#   s6  = name table cursor (append point)
#   s7  = name table base
#   s8  = cstack top bound (underflow check)
#   s9  = cstack bottom bound (overflow check)
#   s10 = return-id stack bottom
#   s11 = return-id stack pointer
#   s0-s5 = callee saved
#   t0-t6 = caller saved
#   a0-a7 = parameter passing
# ---------------------------------------------------------------------------

.altmacro

.macro LOAD_ADDRESS reg, label
_base\@:
        .equ _offset\@, (\label - _base\@)
        auipc   \reg, %hi(_offset\@)
        addi    \reg, \reg, %lo(_offset\@)
.endm

.set    N_CALLS, 0

# --- call-site emission --------------------------------------------------

.macro EMIT_CALL id, target
    addi    s11, s11, -4
    bltu    s11, s10, __panic           # overflow: s11 dropped below stack base
    li      t0, \id
    sw      t0, 0(s11)
    j       \target
Lret_\id:
.endm

.macro CALL target
    EMIT_CALL %N_CALLS, \target
    .set    N_CALLS, N_CALLS + 1
.endm

.macro RET
    j       __dispatch
.endm

# --- compile-time BST emission ------------------------------------------

# BST <lo>, <hi>  -- emit a search subtree covering id range [lo, hi].
.macro BST lo, hi
    .if \lo > \hi
        j       __dispatch_trap            # empty subtree
    .else
        .if \lo == \hi
            j   Lret_\lo                   # leaf: id must equal lo
        .else
            BST_NODE %((\lo + \hi) / 2), \lo, \hi
        .endif
    .endif
.endm

.macro BST_NODE mid, lo, hi
    li      t1, \mid
    beq     t0, t1, Lret_\mid
    blt     t0, t1, Lleft_\mid
    BST     %(\mid + 1), \hi
Lleft_\mid:
    BST     \lo, %(\mid - 1)
.endm

# BR_IF_WS creg, ws_target, nonws_target
#   Classify the byte already in \creg and branch: to \ws_target if it is
#   whitespace, otherwise to \nonws_target. Clobbers t1.
#
#   Whitespace = space (0x20) plus the control range tab..CR (0x09..0x0D).
#   That's two disjoint pieces, so it takes three tests in sequence:
#       == 0x20   -> ws       (space)
#       <  0x09   -> not ws   (below the tab..CR range)
#       <= 0x0D   -> ws       (inside tab..CR, since we already know >= 0x09)
#       else      -> not ws   (0x0E..0x1F, or anything above space)
.macro BR_IF_WS creg, ws_target, nonws_target
    li      t1, 0x20
    beq     \creg, t1, \ws_target           # space
    li      t1, 0x09
    blt     \creg, t1, \nonws_target        # below tab -> not ws
    li      t1, 0x0D
    ble     \creg, t1, \ws_target           # tab..CR  -> ws
    j       \nonws_target                   # else     -> not ws
.endm

# NEXT_TOKEN cur, end, tokstart, done
#   Skip whitespace from \cur (bounded by \end). If the input is exhausted,
#   branch to \done. Otherwise set \tokstart to the token's first byte and
#   advance \cur to one past the token, so the token spans [\tokstart, \cur).
#   No length cap here -- tokens may be any length (the 8-byte cap is enforced
#   only on word *names*, in the definition handlers). >8-char tokens are not
#   hex and not names, so they fall through to the ??? hook.
#   Clobbers t0, t1. \@-suffixed labels keep it safe to expand more than once.
.macro NEXT_TOKEN cur, end, tokstart, done
.Lnt_ws\@:                                  # skip leading whitespace
    bgeu    \cur, \end, \done               # nothing left
    lbu     t0, 0(\cur)
    BR_IF_WS t0, .Lnt_skip\@, .Lnt_beg\@
.Lnt_skip\@:
    addi    \cur, \cur, 1
    j       .Lnt_ws\@
.Lnt_beg\@:
    mv      \tokstart, \cur                 # token starts here
.Lnt_scan\@:                                # scan to end of token
    bgeu    \cur, \end, .Lnt_end\@
    lbu     t0, 0(\cur)
    BR_IF_WS t0, .Lnt_end\@, .Lnt_chr\@
.Lnt_chr\@:
    addi    \cur, \cur, 1
    j       .Lnt_scan\@
.Lnt_end\@:
.endm

# CHECK_HEAP n, tmp -- panic if writing \n bytes at gp would leave the heap
#   region.  The heap and the fam stack are now DISJOINT fixed regions: the heap
#   is [heap_base, heap_top) and the 1 KiB fam stack sits just above it, with its
#   top pinned in s3 (set once in _start).  So heap_top = s3 - 0x400, a constant,
#   independent of the live stack pointer.  gp+\n == heap_top is fine (last byte
#   at heap_top-1); gp+\n > heap_top panics.  Clobbers \tmp.
.macro CHECK_HEAP n, tmp
    addi    \tmp, gp, (\n + 0x400)      # gp + \n + 0x400  (0x400 = stack size)
    bltu    s3, \tmp, __panic           # gp+\n > heap_top (= s3-0x400) -> panic
.endm

# PROC_COMMA -- handle a ',' token: pop the top cstack value and emit it
#   big-endian (memory order) to the output (gp), advancing gp by 4.
#   Panics on cstack underflow (',' with nothing pushed). Clobbers t0, t1.
.macro PROC_COMMA
    bgeu    tp, s8, __panic             # cstack underflow (nothing to pop)
    CHECK_HEAP 4, t1                    # room for 4 output bytes?
    lw      t0, 0(tp)                   # pop cstack
    addi    tp, tp, 4
    srli    t1, t0, 24                  # emit MSB-first
    sb      t1, 0(gp)
    srli    t1, t0, 16
    sb      t1, 1(gp)
    srli    t1, t0, 8
    sb      t1, 2(gp)
    sb      t0, 3(gp)
    addi    gp, gp, 4
.endm

# PROC_HEX start, end, fail -- parse the token [\start,\end) as an UPPERCASE
#   hex literal and push its value onto the cstack (with overflow check). On
#   any non-hex char, branch to \fail (the word/??? path). Clobbers t0,t1,t3,t4.
.macro PROC_HEX start, end, fail
    sub     t0, \end, \start            # >8 chars can't be a 32-bit hex literal
    li      t1, 8
    bgtu    t0, t1, \fail               #   -> not hex (word / ??? path)
    li      t0, 0                       # accumulator
    mv      t3, \start                  # token cursor
.Lph_d\@:
    bgeu    t3, \end, .Lph_push\@
    lbu     t1, 0(t3)
    li      t4, '0'
    blt     t1, t4, \fail
    li      t4, '9'
    bgt     t1, t4, .Lph_a\@
    addi    t1, t1, -'0'                # 0..9
    j       .Lph_v\@
.Lph_a\@:
    li      t4, 'A'                     # uppercase A-F only; lowercase -> \fail
    blt     t1, t4, \fail
    li      t4, 'F'
    bgt     t1, t4, \fail
    addi    t1, t1, -('A' - 10)         # 10..15
.Lph_v\@:
    slli    t0, t0, 4
    or      t0, t0, t1
    addi    t3, t3, 1
    j       .Lph_d\@
.Lph_push\@:
    addi    tp, tp, -4                  # push value onto cstack
    bltu    tp, s9, __panic             # cstack overflow
    sw      t0, 0(tp)
.endm

# SCAN_NAME start, end, found -- pack the token [\start,\end) (<=8 bytes) into
#   two zero-padded words (t5=lo, t6=hi), then scan the name table [s7, s6).
#   On a name match, branch to \found with t0 = matching entry pointer.
#   Otherwise fall through with t5/t6 = the packed name. Clobbers t0-t3,t5,t6.
.macro SCAN_NAME start, end, found
    li      t5, 0                       # name lo (chars 0..3)
    li      t6, 0                       # name hi (chars 4..7)
    mv      t2, \start                  # token cursor
    li      t3, 0                       # byte index
.Lsn_pk\@:
    bgeu    t2, \end, .Lsn_sc\@
    lbu     t0, 0(t2)
    andi    t1, t3, 3
    slli    t1, t1, 3                   # (index & 3) * 8 = bit offset
    sll     t0, t0, t1
    li      t1, 4
    blt     t3, t1, .Lsn_lo\@           # index < 4 -> lo word
    or      t6, t6, t0
    j       .Lsn_pn\@
.Lsn_lo\@:
    or      t5, t5, t0
.Lsn_pn\@:
    addi    t2, t2, 1
    addi    t3, t3, 1
    j       .Lsn_pk\@
.Lsn_sc\@:
    mv      t0, s7                      # entry cursor
.Lsn_lp\@:
    bgeu    t0, s6, .Lsn_nf\@           # scanned all entries -> not found
    lw      t1, 0(t0)                   # entry name lo
    bne     t1, t5, .Lsn_adv\@
    lw      t1, 4(t0)                   # entry name hi
    bne     t1, t6, .Lsn_adv\@
    j       \found                      # match (t0 = entry pointer)
.Lsn_adv\@:
    addi    t0, t0, 20                  # next entry
    j       .Lsn_lp\@
.Lsn_nf\@:
.endm

_start:
    LOAD_ADDRESS s10, data
    li      t0, 0x1000
    add     s9, s10, t0                 # cstack bottom = data+0x1000 (= RID top)
    mv      s11, s9                     # return-id stack top
    addi    tp, s9, 0x400               # cstack top = bottom + 1 KiB
    mv      s8, tp                      # s8 = cstack top bound (underflow check)
    # Immediate-word region: 256 KB at data+0x1400 (right after the cstack), so a
    # :I body's `j __dispatch` / `j imm_tramp->entry` stay within the 1 MiB jump
    # reach. Header: word0 = bump cursor (next free); word1 = stashed output-gp,
    # nonzero only while a :I body is being compiled (the in-:I flag). The region
    # is addressed later as s10+0x1400 (s10 = data, pinned).
    addi    t2, tp, 8                   # cursor = region base + 8 (past 2-word header)
    sw      t2, 0(tp)                   # word0 = immediate cursor
    sw      zero, 4(tp)                 # word1 = 0 (not in a :I definition)
    li      t0, 0x40000                 # 256 KB immediate region
    add     s7, tp, t0                  # name table base = data+0x41400 (= region end)
    mv      s6, s7                      # name table cursor (empty)
    li      t0, 0x100000                # 1 MB name table
    add     t1, s7, t0                  # call-site table base (after the name table)
    addi    t2, t1, 4                   # first entry slot (word 0 holds the cursor)
    sw      t2, 0(t1)                   # init call-site cursor = base + 4
    li      t0, 0x40000                 # 256 KB call-site table (return-id -> site)
    add     gp, t1, t0                  # heap base = after the call-site table
    # Memory above gp splits into two DISJOINT fixed regions: the heap [gp,
    # gp+64MiB) and a 1 KiB fam stack [gp+64MiB, gp+64MiB+0x400).  sp is the
    # stack top (grows down within its 1 KiB); s3 holds it permanently so the
    # heap ceiling (s3-0x400) is a constant -- no heap/stack relational coupling.
    li      sp, 0x4000400              # 64 MiB heap + 1 KiB fam stack
    add     sp, sp, gp                 # sp = stack top
    mv      s3, sp                     # s3 = stack top (FIXED); heap top = s3-0x400
    mv      a0, gp                      # input start
    CALL    read_all_bytes              # slurp stdin into the heap until EOT
    mv      a1, gp                      # input end
    CALL    compile
    CALL    write_output
    j       exit

# compile -- tokenize and process the input [a0,a1).
#   in:  a0 = input start, a1 = input end, gp = input end (heap top)
#   out: a0 = output start, a1 = output end (compiled bytes on the heap)
# Per token: hex literal -> push to cstack; ',' -> pop+emit; ':M name .. ;' ->
# define a macro (record its body span, emit nothing); a defined name -> expand
# its macro body inline. Macro expansion saves the resume (cursor,limit) on the
# sp stack and switches the cursor to the body span; nesting works via that
# stack. An unmatched ';' or undefined name -> __panic (??? comes later).
#   s1 = source cursor   s2 = current limit (input end, or a macro body end)
#   s3 = sp base (macro-stack-empty marker)   s4/s5 = scratch in :M handler
compile:
    mv      s1, a0                      # source cursor = input start
    mv      s2, a1                      # limit = input end
    # s3 (sp base / macro-stack-empty marker) is pinned in _start; sp == s3 here.
    li      ra, 0                       # ra = current ':' definition skip-jump (0 = none)
    # Output goes on the heap right after the input. Align the cursor (gp =
    # input end) up to a 4-byte boundary; that becomes the output base.
    addi    gp, gp, 3
    andi    gp, gp, -4
    mv      s0, gp                      # s0 = output start (returned in a0)
    # Emit the nop header (13 00 00 00) so the output is itself a runnable
    # binary: the magic q32 checks for, plus a harmless first instruction.
    CHECK_HEAP 4, t1                    # room for the 4-byte header?
    li      t0, 0x13
    sb      t0, 0(gp)
    sb      zero, 1(gp)
    sb      zero, 2(gp)
    sb      zero, 3(gp)
    addi    gp, gp, 4
    # Two prologue slots, skipped by `j +12`:
    #   __ret (s0+8):  backpatched to __ret_chain at EOT; words' ';' jump here.
    #   __ovf (s0+12): a self-loop halt; the emitted RID-overflow check jumps here.
    addi    a0, s0, 16                  # program code begins at s0+16 (past both slots)
    CALL    emit_j                      # `j +12` at s0+4 -> s0+16
    CHECK_HEAP 4, t0
    li      t0, 0x6F                    # __ret slot (s0+8): jal x0, 0 (patched at EOT)
    sw      t0, 0(gp)
    addi    gp, gp, 4
    CHECK_HEAP 4, t0
    li      t0, 0x6F                    # __ovf slot (s0+12): jal x0, 0 = self-loop halt
    sw      t0, 0(gp)
    addi    gp, gp, 4                   # gp = s0+16
    # Relocatable end-of-code load into gp. The `j +12` lands here (s0+16), so
    # these run before any user code; backpatched at EOT to point gp past the
    # whole output. The program derives s10/s11/sp/heap from gp.
    CHECK_HEAP 4, t0
    li      t0, 0x00000197              # auipc gp, 0   (at s0+16, patched at EOT)
    sw      t0, 0(gp)
    addi    gp, gp, 4
    CHECK_HEAP 4, t0
    li      t0, 0x00018193              # addi gp, gp, 0  (at s0+20, patched at EOT)
    sw      t0, 0(gp)
    addi    gp, gp, 4                   # gp = s0+24 (user program starts here)
.Lc_next:
    # Immediate-region overflow guard: while a :I body is compiling (region
    # word1 != 0), the cursor (gp) must stay below s7 (name table = region end).
    li      t0, 0x1400
    add     t0, s10, t0                 # region base
    lw      t1, 4(t0)                   # word1: in-:I flag
    beqz    t1, .Lc_next_tok
    bgeu    gp, s7, __panic             # immediate region full
.Lc_next_tok:
    NEXT_TOKEN s1, s2, t2, .Lc_endspan  # token = [t2, s1)
    sub     t3, s1, t2                  # token length
    li      t4, 1
    bne     t3, t4, .Lc_len2            # not 1 char
    # --- 1-char tokens: ',' ';' ':' ---
    lbu     t0, 0(t2)
    li      t4, ','
    beq     t0, t4, .Lc_comma
    li      t4, ';'
    beq     t0, t4, .Lc_semi
    li      t4, ':'
    beq     t0, t4, .Lc_defcolon
    j       .Lc_hexword
.Lc_len2:
    li      t4, 2
    bne     t3, t4, .Lc_hexword         # not 2 char
    # --- 2-char tokens: ':M' macro, ':I' immediate ---
    lbu     t0, 0(t2)
    li      t4, ':'
    bne     t0, t4, .Lc_hexword
    lbu     t0, 1(t2)
    li      t4, 'M'
    beq     t0, t4, .Lc_defm            # ':M' -> macro definition
    li      t4, 'I'
    beq     t0, t4, .Lc_defimm          # ':I' -> immediate-word definition
    j       .Lc_hexword
.Lc_hexword:
    PROC_HEX t2, s1, .Lc_word           # hex literal? else word/name reference
    j       .Lc_next
.Lc_comma:
    PROC_COMMA
    j       .Lc_next
.Lc_semi:
    # In a :I definition? region word1 (!= 0) holds the stashed output-gp.
    li      t0, 0x1400
    add     t3, s10, t0                 # region base
    lw      t4, 4(t3)                   # stashed output-gp (0 = not in :I)
    beqz    t4, .Lc_semi_word
    # Finish the immediate word: append `j __dispatch` so it returns to fam, save
    # the advanced cursor, restore output-gp, clear the in-:I flag.
    LOAD_ADDRESS a0, __dispatch
    CALL    emit_j                      # emit `j __dispatch` at the immediate cursor
    li      t0, 0x1400
    add     t3, s10, t0                 # reload region base (emit_j clobbered t3)
    sw      gp, 0(t3)                   # word0 = new immediate cursor (past this word)
    lw      gp, 4(t3)                   # restore output gp
    sw      zero, 4(t3)                 # clear the in-:I flag
    j       .Lc_next
.Lc_semi_word:
    beqz    ra, .Lc_unmatched           # not inside a ':' definition -> unmatched
    # finish the word: emit its return, then backpatch the skip-jump
    addi    a0, s0, 8                   # __ret trampoline = s0+8
    CALL    emit_j                      # emit `j __ret` at gp
    mv      a0, ra                      # the skip-jump placeholder
    mv      a1, gp                      # patch it to here (.skip = past body+return)
    CALL    patch_j
    li      ra, 0                       # leave the definition
    j       .Lc_next
.Lc_unmatched:
    j       __panic                     # ';' with no matching definition

# ':M name <body> ;' -- record the body source span as a macro; emit nothing.
.Lc_defm:
    NEXT_TOKEN s1, s2, t2, .Lc_deferr   # read macro name = [t2, s1)
    sub     t0, s1, t2                  # names are capped at 8 bytes
    li      t1, 8
    bgtu    t0, t1, __panic
    mv      s4, t2                      # name start
    mv      s5, s1                      # name end = body start
.Lc_defb:
    NEXT_TOKEN s1, s2, t2, .Lc_deferr   # scan body tokens until ';'
    sub     t3, s1, t2
    li      t4, 1
    bne     t3, t4, .Lc_defb
    lbu     t0, 0(t2)
    li      t4, ';'
    bne     t0, t4, .Lc_defb
    # ';' at [t2, s1): body = [s5, t2)
    mv      a2, s4                      # name start
    mv      a3, s5                      # name end
    li      a4, 0                       # kind = MACRO
    mv      a5, s5                      # field0 = body start
    mv      a6, t2                      # field1 = body end
    CALL    nt_insert
    j       .Lc_next
.Lc_deferr:
    j       __panic                     # malformed definition (premature EOF)

# ': name <body> ;' -- ordinary word. Emit a skip-jump over the body, record
# the entry (kind=word), then let the main loop compile the body until ';'.
.Lc_defcolon:
    NEXT_TOKEN s1, s2, t2, .Lc_deferr   # read word name = [t2, s1)
    sub     t0, s1, t2                  # names are packed into 2 words -> max 8 bytes
    li      t1, 8
    bgtu    t0, t1, __panic
    CHECK_HEAP 4, t0
    li      t0, 0x6F                    # skip-jump placeholder: jal x0, 0
    sw      t0, 0(gp)
    mv      ra, gp                      # ra = skip-jump address (backpatched at ';')
    addi    gp, gp, 4
    mv      a2, t2                      # name start
    mv      a3, s1                      # name end
    li      a4, 1                       # kind = WORD
    mv      a5, gp                      # field0 = entry (body starts here)
    li      a6, 0                       # field1 unused
    CALL    nt_insert
    j       .Lc_next                    # body compiled by the main loop

# ':I name <body> ;' -- immediate word. Record (kind=2, entry = immediate
# cursor), swap gp to the immediate region so the body compiles THERE, then let
# the main loop compile it. ';' appends `j __dispatch` and restores output-gp.
.Lc_defimm:
    NEXT_TOKEN s1, s2, t2, .Lc_deferr   # read word name = [t2, s1)
    sub     t0, s1, t2                  # names are capped at 8 bytes
    li      t1, 8
    bgtu    t0, t1, __panic
    li      t0, 0x1400
    add     t3, s10, t0                 # region base
    lw      t4, 0(t3)                   # immediate cursor = this word's entry
    mv      a2, t2                      # name start
    mv      a3, s1                      # name end
    li      a4, 2                       # kind = IMMEDIATE
    mv      a5, t4                      # field0 = entry (immediate cursor)
    li      a6, 0                       # field1 unused
    CALL    nt_insert
    li      t0, 0x1400
    add     t3, s10, t0                 # reload region base (nt_insert clobbered t3)
    sw      gp, 4(t3)                   # word1 = stashed output-gp (in-:I flag)
    lw      gp, 0(t3)                   # gp = immediate cursor -> body emits to region
    j       .Lc_next

# A name token -- look it up; macro -> expand inline, word -> call, immediate -> run.
.Lc_word:
    mv      s4, t2                      # stash token start (nt_lookup's SCAN_NAME clobbers t2)
    sub     t0, s1, t2                  # token length
    li      t1, 8
    bgtu    t0, t1, .Lc_tryunk          # >8 chars: not a name -> ??? hook
    mv      a2, t2                      # name start
    mv      a3, s1                      # name end
    CALL    nt_lookup                   # a4=found, a5=kind, a6=field0, a7=field1
    beqz    a4, .Lc_tryunk              # not defined -> ??? hook
    li      t0, 2
    beq     a5, t0, .Lc_invimm          # kind == 2 -> run the immediate word now
    bnez    a5, .Lc_callword            # kind == 1 (word) -> call (Part 2)
    # macro -- save resume point, jump into the body
    addi    sp, sp, -8
    addi    t0, s3, -0x400              # t0 = stack floor (= heap top)
    bltu    sp, t0, __panic             # macro nesting overflowed its 1 KiB stack
    sw      s1, 0(sp)                   # resume cursor
    sw      s2, 4(sp)                   # resume limit
    mv      s1, a6                      # cursor = body start
    mv      s2, a7                      # limit  = body end
    j       .Lc_next
# A reference to a word (a6 = entry from nt_lookup): emit a call --
#   push a fresh return-id onto the OUTPUT's RID stack, then `j entry`.
#   Record (return-id -> return-site) in the call-site table for the EOT
#   __ret_chain (Part 2b).
.Lc_callword:
    li      t3, 0x100000
    add     t3, s7, t3                  # t3 = call-site table base
    lw      t4, 0(t3)                   # t4 = cursor (next free entry)
    sub     t5, t4, t3
    addi    t5, t5, -4
    srli    t5, t5, 2                   # t5 = return-id r = (cursor - base - 4)/4
    li      a0, 0xFFCD8D93              # addi s11, s11, -4
    CALL    emit_word
    li      a0, 0x01ADF463             # bgeu s11, s10, +8  (skip trap-jump if no overflow)
    CALL    emit_word
    addi    a0, s0, 12                 # j __ovf  (RID-overflow halt; trampoline, 1 MiB reach)
    CALL    emit_j
    mv      a0, t5                      # li t0, r   (lui+addi: r may exceed 2047)
    li      a1, 0x2B7                   #   lui t0, 0
    li      a2, 0x28293                 #   addi t0, t0, 0
    CALL    emit_li
    li      a0, 0x005DA023              # sw t0, 0(s11)
    CALL    emit_word
    mv      a0, a6                      # j entry
    CALL    emit_j
    sw      gp, 0(t4)                   # site[r] = return point (current gp)
    addi    t4, t4, 4
    li      t0, 0x40000
    add     t0, t3, t0                  # call-site table end
    bgeu    t4, t0, __panic             # call-site table overflow
    sw      t4, 0(t3)                   # store updated cursor
    j       .Lc_next
# Unknown token: not a builtin, not hex, not a defined word, or longer than 8
# bytes. Invoke the user's ':I ???' handler if defined -- a0 = token start,
# a1 = token length; ??? reads those and may advance s1 (the source cursor) to
# consume more input (e.g. a quoted string spanning spaces). No handler -> panic.
.Lc_tryunk:
    CALL    find_qqq                    # a4 = found, a6 = ??? entry (kind=2)
    beqz    a4, .Lc_undef               # no ??? defined -> undefined token
    LOAD_ADDRESS a0, imm_tramp
    mv      a1, a6                      # target = ??? entry
    CALL    patch_j                     # imm_tramp := `j ???`
    mv      a0, s4                      # a0 = token start (t2 was clobbered by nt_lookup)
    sub     a1, s1, s4                  # a1 = token length
    CALL    imm_tramp                   # run ??? with the token in a0/a1
    j       .Lc_next
.Lc_undef:
    j       __panic                     # unknown token and no ??? handler

# An immediate-word reference (a6 = entry in the region): run it now. Patch the
# shared trampoline to `j entry`, then CALL it; the body returns via `j __dispatch`,
# popping the CALL's return-id back here. The body emits into whatever gp points
# at -- the output at top level, or the enclosing :I body's region slot.
.Lc_invimm:
    LOAD_ADDRESS a0, imm_tramp          # trampoline slot address
    mv      a1, a6                      # target = immediate entry
    CALL    patch_j                     # imm_tramp := `j entry`
    CALL    imm_tramp                   # push return-id, j imm_tramp -> entry -> __dispatch
    j       .Lc_next

# Reached the current limit. Pop a saved macro frame, or finish at top level.
.Lc_endspan:
    beq     sp, s3, .Lc_done            # macro stack empty -> done
    lw      s1, 0(sp)                   # resume cursor
    lw      s2, 4(sp)                   # resume limit
    addi    sp, sp, 8
    j       .Lc_next
.Lc_done:
    # Halt at the program end: a program that runs off its end -- or whose
    # final action is a call that returns to the EOT position -- lands here
    # instead of falling into __ret_chain. (A real program exits before this.)
    mv      a0, gp
    CALL    emit_j                      # `j .` at the program end
    # Generate __ret_chain after it: pop the return-id, range-check it (a
    # corrupt id halts), then a balanced BST mapping return-id -> return-site
    # (O(log n) per return vs. the old linear chain).
    mv      t6, gp                      # t6 = __ret_chain start (for the backpatch)
    li      a0, 0x000DA283              # lw t0, 0(s11)   (pop return-id)
    CALL    emit_word
    li      a0, 0x004D8D93              # addi s11, s11, 4
    CALL    emit_word
    li      t3, 0x100000
    add     t3, s7, t3                  # t3 = call-site table base
    lw      t4, 0(t3)                   # t4 = cursor (one past last entry)
    sub     t5, t4, t3
    addi    t5, t5, -4
    srli    t5, t5, 2                   # t5 = N (number of call sites)
    # Range check: li t1, N ; bltu t0, t1, +8 ; j .  -- a popped id >= N (a
    # corrupt RID stack) halts rather than jumping to a bogus BST leaf.
    mv      a0, t5                      # li t1, N   (lui+addi: N may exceed 2047)
    li      a1, 0x337                   #   lui t1, 0
    li      a2, 0x30313                 #   addi t1, t1, 0
    CALL    emit_li
    li      a0, 0x0062E463             # bltu t0, t1, +8  (skip the halt if id < N)
    CALL    emit_word
    li      a0, 0x6F                   # j .   (bad-id halt; skipped when id < N)
    CALL    emit_word
    li      a0, 0                       # lo = 0
    addi    a1, t5, -1                  # hi = N - 1
    CALL    gen_bst                     # emit the balanced BST over [0, N-1]
    addi    a0, s0, 8                   # patch the __ret trampoline (s0+8) ...
    mv      a1, t6                      # ... to jump to __ret_chain
    CALL    patch_j
    addi    a0, s0, 16                  # patch the prologue gp-load (auipc @ s0+16) ...
    mv      a1, gp                      # ... to point gp at the end of the output
    CALL    patch_la
    mv      a0, s0                      # output start
    mv      a1, gp                      # output end
    RET

# nt_insert -- a2=tok start, a3=tok end, a4=kind, a5=field0, a6=field1.
#   Appends a 20-byte entry to the name table. __panic on a duplicate name
#   (redefinition is a compile error) or table overflow. Preserves a0/a1
#   (compile's cursor + limit). Clobbers t0-t6, a2, a3.
nt_insert:
    SCAN_NAME a2, a3, .Lin_dup          # name already defined -> duplicate
    addi    t1, s6, 20                  # cursor after this entry
    li      t2, 0x100000
    add     t2, s7, t2                  # name table end
    bgtu    t1, t2, __panic             # table overflow
    sw      t5, 0(s6)                   # name lo
    sw      t6, 4(s6)                   # name hi
    sw      a4, 8(s6)                   # kind
    sw      a5, 12(s6)                  # field0
    sw      a6, 16(s6)                  # field1
    addi    s6, s6, 20                  # advance cursor
    RET
.Lin_dup:
    j       __panic                     # redefinition is a compile error

# nt_lookup -- a2=tok start, a3=tok end. Returns a4=found(1/0); when found,
#   a5=kind, a6=field0, a7=field1. Preserves a0/a1. Clobbers t0-t6, a2, a3.
#   (Not yet exercised -- the reference path that uses it comes with ':'.)
nt_lookup:
    SCAN_NAME a2, a3, .Llk_found
    li      a4, 0                       # not found
    RET
.Llk_found:
    lw      a5, 8(t0)                   # kind
    lw      a6, 12(t0)                  # field0
    lw      a7, 16(t0)                  # field1
    li      a4, 1                       # found
    RET

# encode_jal -- a0 = signed byte offset; returns a0 = `jal x0, offset` word
#   (builds the scrambled J-type immediate). Clobbers t0, t1.
#   The J-immediate is 21-bit signed (+-1 MiB), so an offset beyond that can't be
#   encoded -- bail to __panic rather than silently emit a truncated/wrong jump.
#   This makes the no-jalr ~1 MiB output ceiling a clean error, not a miscompile.
encode_jal:
    srai    t0, a0, 20                  # in range iff offset>>20 is 0 or -1
    beqz    t0, 1f
    li      t1, -1
    bne     t0, t1, __panic             # |offset| >= 1 MiB -> not encodable
1:
    li      t0, 0x6F                    # opcode | rd=x0
    srli    t1, a0, 11                  # imm[11] -> bit 20
    andi    t1, t1, 1
    slli    t1, t1, 20
    or      t0, t0, t1
    srli    t1, a0, 12                  # imm[19:12] -> bits 19:12
    andi    t1, t1, 0xFF
    slli    t1, t1, 12
    or      t0, t0, t1
    srli    t1, a0, 1                   # imm[10:1] -> bits 30:21
    andi    t1, t1, 0x3FF
    slli    t1, t1, 21
    or      t0, t0, t1
    srli    t1, a0, 20                  # imm[20] -> bit 31
    andi    t1, t1, 1
    slli    t1, t1, 31
    or      t0, t0, t1
    mv      a0, t0
    RET

# emit_j -- a0 = target address; emit `jal x0, target-gp` at gp, advance gp.
#   The word is stored little-endian (the CPU's fetch order), unlike ',' which
#   stores user-typed memory-order bytes. Clobbers t0, t1, a0.
emit_j:
    sub     a0, a0, gp                  # off = target - gp
    CALL    encode_jal                  # a0 = instruction word
    CHECK_HEAP 4, t0
    sw      a0, 0(gp)
    addi    gp, gp, 4
    RET

# patch_j -- a0 = jump-slot address, a1 = target; overwrite the slot with
#   `jal x0, target-slot`. Clobbers t0, t1, a0, a1, a2.
patch_j:
    mv      a2, a0                      # a2 = slot address
    sub     a0, a1, a2                  # off = target - slot
    CALL    encode_jal                  # a0 = instruction word
    sw      a0, 0(a2)
    RET

# patch_la -- a0 = address of an `auipc gp` (paired `addi gp,gp` at a0+4),
#   a1 = target. Rewrites the pair to load `target` PC-relative: off = target-a0;
#   auipc gets %hi(off)=(off+0x800)>>12 in imm[31:12], addi gets %lo(off)=off&0xFFF
#   in imm[31:20]. Placeholders are `auipc gp,0`=0x197 / `addi gp,gp,0`=0x18193.
#   Clobbers a2-a5.
patch_la:
    sub     a2, a1, a0                  # off = target - auipc address
    li      a3, 0x800
    add     a3, a2, a3
    srli    a3, a3, 12                  # a3 = %hi(off)
    slli    a3, a3, 12
    ori     a3, a3, 0x197               # rebuild `auipc gp, %hi`
    sw      a3, 0(a0)
    slli    a4, a2, 20                  # %lo(off) -> imm[31:20]
    li      a5, 0x18193
    or      a4, a4, a5                  # rebuild `addi gp, gp, %lo`
    sw      a4, 4(a0)
    RET

# gen_bst -- a0 = lo, a1 = hi.  Emit a balanced BST node covering return-id
#   range [lo, hi] into the output at gp:
#       li t1, mid ; bne t0,t1,+8 ; j site[mid]   (hit)
#       bge t0,t1,+8 ; j Lleft                     (t0<mid -> left subtree)
#       <right subtree>  (fall-through, t0>mid)    Lleft: <left subtree>
#   A leaf (lo==hi) is just `j site[lo]`; the range check upstream guarantees
#   a valid id reaches the right leaf. Recursive: lo/hi/mid/jleft live in a
#   16-byte sp frame across the two recursive calls. site[id] = *((s7+0x100000)
#   + 4 + id*4).  Clobbers t0-t6, a0-a1 (frame-saved values reloaded each time).
gen_bst:
    blt     a1, a0, .Lgb_done           # lo > hi: empty subtree
    bne     a0, a1, .Lgb_node           # lo != hi: internal node
    li      t3, 0x100004                # leaf: lo == hi -> j site[lo]
    add     t3, s7, t3                  # &site[0]
    slli    t4, a0, 2
    add     t3, t3, t4                  # &site[lo]
    lw      a0, 0(t3)
    CALL    emit_j
.Lgb_done:
    RET
.Lgb_node:
    addi    sp, sp, -16                 # frame: [lo, hi, mid, jleft]
    addi    t0, s3, -0x400              # t0 = stack floor (= heap top)
    bltu    sp, t0, __panic             # frame overflowed its 1 KiB stack
    sw      a0, 0(sp)                   # lo
    sw      a1, 4(sp)                   # hi
    add     t3, a0, a1
    srli    t3, t3, 1
    sw      t3, 8(sp)                   # mid = (lo + hi) / 2
    mv      a0, t3                      # li t1, mid   (lui+addi: mid may exceed 2047)
    li      a1, 0x337                   #   lui t1, 0
    li      a2, 0x30313                 #   addi t1, t1, 0
    CALL    emit_li
    li      a0, 0x00629463             # bne t0, t1, +8  (skip the hit jump)
    CALL    emit_word
    li      t3, 0x100004                # j site[mid]
    add     t3, s7, t3
    lw      t4, 8(sp)
    slli    t4, t4, 2
    add     t3, t3, t4
    lw      a0, 0(t3)
    CALL    emit_j
    li      a0, 0x0062D463             # bge t0, t1, +8  (t0>=mid -> skip left jump)
    CALL    emit_word
    mv      t5, gp                      # jleft = slot of the placeholder j
    sw      t5, 12(sp)
    li      a0, 0x6F                   # j Lleft  (placeholder, backpatched below)
    CALL    emit_word
    lw      t3, 8(sp)                   # recurse right: gen_bst(mid+1, hi)
    addi    a0, t3, 1
    lw      a1, 4(sp)
    CALL    gen_bst
    # Patch the left-jump placeholder. The left subtree is gen_bst(lo, mid-1),
    # which is EMPTY when mid==lo (a 2-element node [lo, lo+1]). For a valid id
    # the t0<mid edge is then unreachable -- but a corrupt RID could take it, so
    # point it at a `j .` self-loop halt rather than at the next code / EOF
    # (which is where `gp` lands when nothing follows). Matches the upstream
    # range-check sentinel; keeps the CFG closed and every dead edge bounded.
    lw      t3, 8(sp)                   # mid
    lw      t4, 0(sp)                   # lo
    lw      a0, 12(sp)                  # Lleft placeholder slot
    beq     t3, t4, .Lgb_left_empty     # mid==lo -> left empty -> halt, no recurse
    mv      a1, gp                      # left non-empty: Lleft -> left subtree (gp)
    CALL    patch_j
    lw      a0, 0(sp)                   # recurse left: gen_bst(lo, mid-1)
    lw      t3, 8(sp)
    addi    a1, t3, -1
    CALL    gen_bst
    addi    sp, sp, 16
    RET
.Lgb_left_empty:
    mv      a1, a0                      # target = the j's own address -> `j .` halt
    CALL    patch_j
    addi    sp, sp, 16
    RET

# imm_tramp -- one-slot trampoline for invoking an immediate word at a runtime-
#   determined address without jalr. .Lc_invimm patches this to `j <entry>` then
#   `CALL imm_tramp`; the body returns via `j __dispatch`. Only reached via that
#   CALL (the preceding RET means it is never fallen into); the self-loop is just
#   a safe placeholder if it somehow runs unpatched.
imm_tramp:
    j       imm_tramp

# find_qqq -- look up the immediate word named "???" (packed name lo=0x003F3F3F,
#   hi=0). Returns a4=1 and a6=entry if a kind=2 entry exists, else a4=0.
#   Preserves t2/s1 (the caller's token span). Clobbers t0,t1,t3,t5,t6,a4,a6.
find_qqq:
    li      t5, 0x003F3F3F              # "???" packed (3 x '?')
    li      t6, 0
    mv      t3, s7                      # scan from the name table base
.Lfq_lp:
    bgeu    t3, s6, .Lfq_nf             # scanned all entries -> not found
    lw      t0, 0(t3)
    bne     t0, t5, .Lfq_adv
    lw      t0, 4(t3)
    bne     t0, t6, .Lfq_adv
    lw      t0, 8(t3)                   # kind
    li      t1, 2
    bne     t0, t1, .Lfq_adv            # only an immediate ??? is invocable
    lw      a6, 12(t3)                  # field0 = entry
    li      a4, 1
    RET
.Lfq_adv:
    addi    t3, t3, 20
    j       .Lfq_lp
.Lfq_nf:
    li      a4, 0
    RET

# emit_word -- a0 = instruction word; store it at gp (little-endian), advance gp.
#   Clobbers t0, a0.
emit_word:
    CHECK_HEAP 4, t0
    sw      a0, 0(gp)
    addi    gp, gp, 4
    RET

# emit_li -- emit `li <reg>, a0` as lui+addi so the value can be any 32-bit number
#   (a single addi caps at +-2048; this is what lifts the 2047 call-site limit).
#   a1 = `lui <reg>,0` template word, a2 = `addi <reg>,<reg>,0` template word.
#   hi=(v+0x800)>>12 in the lui imm, lo=v&0xFFF in the addi imm (sign-extended).
#   Builds both words into a3/a4 (a-regs survive emit_word's RID return); uses
#   only t0 + a0/a3/a4, so t1-t6 callers (.Lc_callword, gen_bst) are preserved.
emit_li:
    li      t0, 0x800
    add     t0, a0, t0
    srli    t0, t0, 12                  # hi = (v + 0x800) >> 12
    slli    t0, t0, 12
    or      a3, t0, a1                  # complete `lui <reg>, hi`
    slli    t0, a0, 20                  # lo (v's low 12 bits) -> imm[31:20]
    or      a4, t0, a2                  # complete `addi <reg>, <reg>, lo`
    mv      a0, a3
    CALL    emit_word
    mv      a0, a4
    CALL    emit_word
    RET

write_output:
    li      t0, 0x10000000              # UART base
1:  lbu     t1, 5(t0)
    andi    t1, t1, 0x20                # LSR THR-empty
    beqz    t1, 1b
    bgeu     a0, a1, 2f
    lbu     t1, 0(a0)
    sb      t1, 0(t0)                   # THR
    addi    a0, a0, 1
    j       1b
2:  RET

read_all_bytes:
    li      t0, 0x10000000              # UART base
    li      t2, 0x04                    # EOT sentinel
1:  lbu     t1, 5(t0)                   # LSR
    andi    t1, t1, 0x01                # DR bit -- byte available?
    beqz    t1, 1b
    lbu     t1, 0(t0)                   # RBR -- read byte
    beq     t1, t2, 2f                  # EOT -> stop
    CHECK_HEAP 1, t3                    # room for 1 input byte?
    sb      t1, 0(gp)                   # store at heap
    addi    gp, gp, 1                   # bump
    j       1b
2:  RET

exit:
    li      t0, 0x100000                # SiFive test finisher
    li      t1, 0x5555                  # shutdown
    sw      t1, 0(t0)
1:  j       1b

__panic:
    li      t0, 0x10000000              # UART base
    li      a0, '?'
1:  lbu     t1, 5(t0)
    andi    t1, t1, 0x20
    beqz    t1, 1b
    sb      a0, 0(t0)
    li      a0, '\n'
2:  lbu     t1, 5(t0)
    andi    t1, t1, 0x20
    beqz    t1, 2b
    sb      a0, 0(t0)
    li      t0, 0x100000                # SiFive test finisher
    li      t1, 0x00013333              # FAIL with exit code 1 (NOT 0x5555/PASS)
    sw      t1, 0(t0)
1:  j       1b                          # spin until QEMU exits

__dispatch:
    lw      t0, 0(s11)                  # pop return id
    addi    s11, s11, 4
    li      t1, N_CALLS
    bgeu    t0, t1, __dispatch_trap     # out-of-range id -> trap
    BST     0, %(N_CALLS - 1)
__dispatch_trap:
1:  j       1b

data:
