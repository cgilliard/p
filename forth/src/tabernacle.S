# ──────────────────────────────────────────────────────────────────────────────
# src/tabernacle.S — sealed bootstrap loader for famchain.
#
# Built via:
#     python3 tools/s2fam0_tabernacle.py src/tabernacle.S src/tabernacle.fam0
#     run bin/tabernacle.uncompressed bin/fam0 src/tabernacle.fam0
# (src/tabernacle.fam0 is checked in; scripts/build.sh runs only the second
#  step — rerun the generator after editing this file.)
#
# Boot ABI (we set up our own gp via auto-prologue below):
#     PC = 0x80000000     entry of this binary
#     gp = end_marker     byte just past tabernacle.bin
#                         (full_node.bin is concatenated after, so
#                          gp = full_node base; gp-40 = config [nchunks,bin_size,hash].)
#
# Calling convention — NO JALR.  Subroutines are reached via direct `j`
# with a per-call-site dispatch tag.  Mirrors the CALL/BST macros in
# src/fam.S; pinned registers:
#     s11 = current return ID (set by CALL)
#     s10 = RID-stack ptr     (decreases on push)
#     s9  = RID-stack bottom  (bounds check)
#     s7  = full_node base    (page-aligned, persists for handoff)
# Callee saves nothing on RID stack itself; CALL pushes/pops s11.
# ──────────────────────────────────────────────────────────────────────────────

	.text
	.globl _start

# ── Constants ─────────────────────────────────────────────────────────────
	.equ UART_BASE,         0x10000000
	.equ UART_LSR,                 0x5
	.equ UART_RX_READY,            0x1
	.equ SHUTDOWN_ADDR,       0x100000
	.equ SHUTDOWN_PASS,         0x5555
	.equ SHUTDOWN_FAIL,        0x13333

	.equ STACK_SIZE,         0x100000      # 1 MiB data stack
	.equ RID_BASE_OFF,       0x100000      # RID stack lives just above sp top
	.equ RID_SIZE,             0x1000      # 256 frames × 16 B header (overkill)
	.equ PAGE_SIZE,             0x1000
	.equ NEG_PAGE_SIZE,     0xFFFFF000
	.equ PAGE_MASK,              0xFFF

	# BIN_SIZE and NCHUNKS are data words at gp-36 and gp-40,
	# patched by scripts/build.sh after compiling tabernacle.fam0.

	.equ SEED_LIST_OFFSET,      0xA000
	.equ TIMETIK,               0x9FFC
	.equ BPSAVE,                0x9FF8
	.equ WD_TICK,               0x9FE0      # watchdog: last-progress mtime (4 B)
	.equ DBGFLAG,               0x9FD8      # debug flag (4 B): 0=quiet, 1=verbose
	.equ NETFLAG,               0x9FCC      # network (4 B): 0 = main, 1 = dev
	.equ MAX_SEEDS,                 16
	.equ DEFAULT_TIMEOUT_TK, 0x05F5E100
	.equ MTIME_ADDR,         0x200BFF8      # CLINT mtime (RV virt machine)
	.equ MT_KHZ,                 10000      # mtime frequency in kHz (10 MHz)
	# NB_BMAP — chunk-received bitmap.  ceil(NCHUNKS / 8) bytes.
	# At 8 KB max NCHUNKS supported (= 64K bits).
	.equ NB_BMAP,               0xA080
	.equ NB_BMAP_BYTES,           1024


# ── Static-dispatch macros (no JALR), lifted from src/fam.S ───────────────
	.altmacro
	.set _CSN, 0

.macro CALL target
	.set _CSN, _CSN + 1
	addi    s10, s10, -4
	bgeu    s10, s9, .L_call_ok_\@
	j       panic
.L_call_ok_\@:
	sw      s11, 0(s10)
	li      s11, _CSN
	j       \target
	EMIT_LABEL %_CSN
	lw      s11, 0(s10)
	addi    s10, s10, 4
.endm

.macro EMIT_LABEL n
.L_csret_\n:
.endm

.macro BST lo, hi
	BST_R %\lo, %\hi
.endm
.macro BST_R lo, hi
	.if \hi == \lo
.L_bst_\lo\()_\hi:
		j .L_csret_\lo
	.else
		.set _BST_MID, (\lo + \hi) / 2
		BST_NODE %\lo, %\hi, %_BST_MID, %(_BST_MID - 1), %(_BST_MID + 1)
	.endif
.endm
.macro BST_NODE lo, hi, mid, lhi, rlo
.L_bst_\lo\()_\hi:
	li      t0, \mid
	.if \lhi >= \lo
		bge s11, t0, .L_bst_\lo\()_\hi\()_R
		j   .L_bst_\lo\()_\lhi
.L_bst_\lo\()_\hi\()_R:
	.endif
	.if \rlo <= \hi
		ble s11, t0, .L_bst_\lo\()_\hi\()_E
		j   .L_bst_\rlo\()_\hi
.L_bst_\lo\()_\hi\()_E:
	.endif
	j       .L_csret_\mid
	.if \lhi >= \lo
		BST_R %\lo, %\lhi
	.endif
	.if \rlo <= \hi
		BST_R %\rlo, %\hi
	.endif
.endm

# PC-relative load-address (avoids `la` which doesn't relax under -march=rv32i).
.macro LOAD_ADDRESS reg, label
_base\@:
	.equ _offset\@, (\label - _base\@)
	auipc   \reg, %pcrel_hi(\label)
	addi    \reg, \reg, %pcrel_lo(_base\@)
.endm

# ──────────────────────────────────────────────────────────────────────────────
# _start
# ──────────────────────────────────────────────────────────────────────────────

_start:
	# ── §0 Auto-prologue (NOP magic + gp = end_marker). ──────────────
	addi    zero, zero, 0
	LOAD_ADDRESS gp, end_marker

	# ── §1 Page-align s7, then carve sp / s10 / s9 above it. ─────────
	# s7 = full_node base (page-aligned).
	# sp     = s7 + STACK_SIZE              (data stack top, grows down)
	# s10    = s7 + STACK_SIZE + RID_SIZE   (RID stack top, grows down)
	# s9     = s7 + STACK_SIZE              (RID stack bottom — when s10
	#                                        reaches s9 we're full)
	mv      s7, gp
	lw      t0, -36(gp)
	add     s7, s7, t0
	li      t0, PAGE_MASK
	add     s7, s7, t0
	li      t0, NEG_PAGE_SIZE
	and     s7, s7, t0

	li      t0, STACK_SIZE
	add     sp, s7, t0
	mv      s9, sp                          # RID bottom = sp top
	li      t0, RID_SIZE
	add     s10, s9, t0                     # RID top
	# Per fam.S convention, s11 starts at 0 (no enclosing call frame).
	li      s11, 0

	# ── §2 Zero 0xB000 bytes at s7 (covers virtio queues + buffers + the
	#     control / seed-list / chunk-bitmap region around 0xA000). ──
	mv      t0, s7
	li      t1, 0x2C00                     # 0xB000 / 4 = 0x2C00 words
zero_top:
	sw      zero, 0(t0)
	addi    t0, t0, 4
	addi    t1, t1, -1
	bne     t1, zero, zero_top

	# UART base in s8 (callee-saved across CALL).
	lui     s8, %hi(UART_BASE)
	li      t3, 0                           # skip_phase2 flag


# ──────────────────────────────────────────────────────────────────────────────
# UART config parser — reads
#   "<bind_port> <debug> <timeout_ms> <network> <ip:port> ...\004"
# (network: 0 main, 1 dev; the ip:ports are the seeds).
# Storing parsed state at:
#   s4               = bind_port
#   s7 + DBGFLAG     = debug flag (0=quiet, 1=verbose)
#   s7 + TIMETIK     = timeout in MTIME ticks
#   s7 + NETFLAG     = network
#   s7 + BPSAVE      = bind_port (mirror)
#   s7 + SEED_LIST_OFFSET = [u8 count][N × 6 B (4 IP + 2 LE port)]
# ──────────────────────────────────────────────────────────────────────────────

# ── Phase 1: bind_port ────────────────────────────────────────────────────
	li      s6, 0
ph1_top:
	lbu     t0, UART_LSR(s8)
	andi    t0, t0, UART_RX_READY
	beqz    t0, ph1_top
	lbu     t6, 0(s8)

	li      t0, 4
	bne     t6, t0, 1f
	li      t3, 1
	j       ph1_done
1:	addi    t0, t6, -'0'
	li      t1, 10
	bgeu    t0, t1, ph1_done

	slli    t1, s6, 3
	slli    t4, s6, 1
	add     s6, t1, t4
	add     s6, s6, t0
	j       ph1_top
ph1_done:
	mv      s4, s6

# ── Phase 1a: debug flag ─────────────────────────────────────────────────
	bnez    t3, ph1a_skip
	li      s6, 0
ph1a_top:
	lbu     t0, UART_LSR(s8)
	andi    t0, t0, UART_RX_READY
	beqz    t0, ph1a_top
	lbu     t6, 0(s8)

	li      t0, 4
	bne     t6, t0, 1f
	li      t3, 1
	j       ph1a_done
1:	addi    t0, t6, -'0'
	li      t1, 10
	bgeu    t0, t1, ph1a_done

	slli    t1, s6, 3
	slli    t4, s6, 1
	add     s6, t1, t4
	add     s6, s6, t0
	j       ph1a_top
ph1a_done:
ph1a_skip:
	li      t0, DBGFLAG
	add     t0, s7, t0
	sw      s6, 0(t0)

# ── Phase 1b: timeout_ms ──────────────────────────────────────────────────
	bnez    t3, ph1b_skip
	li      s6, 0
ph1b_top:
	lbu     t0, UART_LSR(s8)
	andi    t0, t0, UART_RX_READY
	beqz    t0, ph1b_top
	lbu     t6, 0(s8)

	li      t0, 4
	bne     t6, t0, 1f
	li      t3, 1
	j       ph1b_done
1:	addi    t0, t6, -'0'
	li      t1, 10
	bgeu    t0, t1, ph1b_done

	slli    t1, s6, 3
	slli    t4, s6, 1
	add     s6, t1, t4
	add     s6, s6, t0
	j       ph1b_top
ph1b_done:
ph1b_skip:


# ── Compute timeout in MTIME ticks → mem[s7 + TIMETIK] ───────────────────
	beqz    s6, timeout_default
	slli    t0, s6, 13
	slli    t1, s6, 11;  add t0, t0, t1
	slli    t1, s6, 8;   sub t0, t0, t1
	slli    t1, s6, 4;   add t0, t0, t1
	j       timeout_store
timeout_default:
	li      t0, DEFAULT_TIMEOUT_TK
timeout_store:
	li      t1, TIMETIK
	add     t1, s7, t1
	sw      t0, 0(t1)

# ── Phase 1c: network ─────────────────────────────────────────────────────
	li      s6, 0
	bnez    t3, ph1c_skip
ph1c_top:
	lbu     t0, UART_LSR(s8)
	andi    t0, t0, UART_RX_READY
	beqz    t0, ph1c_top
	lbu     t6, 0(s8)

	li      t0, 4
	bne     t6, t0, 1f
	li      t3, 1
	j       ph1c_skip
1:	addi    t0, t6, -'0'
	li      t1, 10
	bgeu    t0, t1, ph1c_skip

	slli    t1, s6, 3
	slli    t4, s6, 1
	add     s6, t1, t4
	add     s6, s6, t0
	j       ph1c_top
ph1c_skip:
	li      t0, NETFLAG
	add     t0, s7, t0
	sw      s6, 0(t0)


# ── Phase 2: seed list ────────────────────────────────────────────────────
	li      s5, 0                           # seed count
	bnez    t3, ph2_skip

	li      t2, SEED_LIST_OFFSET
	add     t2, s7, t2
	addi    t2, t2, 1                       # entries base (skip count byte)
	li      s6, 0                           # accumulator
	li      t3, 0                           # field 0..3 = octets, 4 = port

ph2_top:
	lbu     t0, UART_LSR(s8)
	andi    t0, t0, UART_RX_READY
	beqz    t0, ph2_top
	lbu     t6, 0(s8)

	li      t0, 4
	bne     t6, t0, ph2_not_eot
	li      t0, 4
	bne     t3, t0, ph2_done
	li      t0, MAX_SEEDS
	bge     s5, t0, ph2_done
	sh      s6, 4(t2)
	addi    s5, s5, 1
	j       ph2_done

ph2_not_eot:
	addi    t0, t6, -'0'
	li      t1, 10
	bgeu    t0, t1, ph2_sep
	slli    t1, s6, 3
	slli    t4, s6, 1
	add     s6, t1, t4
	add     s6, s6, t0
	j       ph2_top

ph2_sep:
	li      t0, '.'
	bne     t6, t0, ph2_not_dot
	li      t0, 3
	bge     t3, t0, ph2_top
	j       ph2_store_advance
ph2_not_dot:
	li      t0, ':'
	bne     t6, t0, ph2_space
	li      t0, 3
	bne     t3, t0, ph2_top
ph2_store_advance:
	add     t4, t2, t3
	sb      s6, 0(t4)
	addi    t3, t3, 1
	li      s6, 0
	j       ph2_top
ph2_space:
	li      t0, 4
	bne     t3, t0, ph2_reset
	li      t0, MAX_SEEDS
	bge     s5, t0, ph2_reset
	sh      s6, 4(t2)
	addi    s5, s5, 1
	addi    t2, t2, 6
ph2_reset:
	li      s6, 0
	li      t3, 0
	j       ph2_top

ph2_done:
ph2_skip:

	li      t0, SEED_LIST_OFFSET
	add     t0, s7, t0
	sb      s5, 0(t0)
	li      t0, BPSAVE
	add     t0, s7, t0
	sw      s4, 0(t0)


# ──────────────────────────────────────────────────────────────────────────────
# §3 Disk boot:
#     scan_disk → init virtio-blk → read full_node into [s7..s7+BIN_SIZE)
#     → gimli_hash → compare to hash_data → handoff.
# A missing block device or a read error halts (halt_no_disk); a successful
# read whose hash does not match falls through to §5 net boot.
# ──────────────────────────────────────────────────────────────────────────────

	CALL    scan_disk                       # → s3 = disk MMIO base, or fall to halt_d

	# ── Virtio-blk handshake (legacy MMIO) ──
	sw      zero, 0x70(s3)                  # status = 0
	li      t1, 1
	sw      t1, 0x70(s3)                    # status = 1 (ACKNOWLEDGE)
	lw      t1, 0x70(s3)
	ori     t1, t1, 2
	sw      t1, 0x70(s3)                    # status |= 2 (DRIVER)
	sw      zero, 0x20(s3)                  # driver_features = 0
	lw      t1, 0x70(s3)
	ori     t1, t1, 8
	sw      t1, 0x70(s3)                    # status |= 8 (FEATURES_OK)
	lw      t1, 0x70(s3)
	andi    t2, t1, 8
	beqz    t2, halt_no_disk                # FEATURES_OK didn't stick

	li      t1, PAGE_SIZE
	sw      t1, 0x28(s3)                    # V_GPS = 0x1000
	sw      zero, 0x30(s3)                  # V_QSEL = 0
	sw      t1, 0x3C(s3)                    # V_QALGN = 0x1000
	li      t1, 16
	sw      t1, 0x38(s3)                    # V_QNUM = 16
	srli    t1, s7, 12
	sw      t1, 0x40(s3)                    # V_QPFN = s7 >> 12
	lw      t1, 0x70(s3)
	ori     t1, t1, 4
	sw      t1, 0x70(s3)                    # status |= 4 (DRIVER_OK)


# ── Read loop: load BIN_SIZE bytes from disk into [gp..gp+BIN_SIZE). ─────
# gp = full_node base (where the bin gets loaded); s7 = queue/stack base
# (post-full_node, page-aligned).  We mustn't write disk data into s7's
# region or we'd clobber descriptors / status / stack.
	mv      s0, gp                          # dest walker = full_node base
	lw      t0, -36(gp)
	mv      s1, t0                          # bytes remaining
	li      s2, 0                           # sector counter
	li      s6, 0                           # avail idx (was s7 in old; conflict)

read_loop_top:
	beqz    s1, read_done

	# chunk = min(remaining, DSK_CHK), rounded up to sector (512 B).
	li      t0, 0x10000                     # DSK_CHK = 64 KiB
	mv      a3, t0
	bge     s1, t0, 1f
	addi    a3, s1, 0x1FF                   # round up to 512
	li      t0, 0xFFFFFE00                  # NEG_SECT
	and     a3, a3, t0
1:
	mv      a0, s2                          # sector
	addi    s6, s6, 1
	mv      a1, s6                          # avail idx
	mv      a2, s0                          # dest

	# disk_read clobbers a3; save chunk on stack.
	addi    sp, sp, -4
	sw      a3, 0(sp)
	CALL    disk_read
	lw      t0, 0(sp)
	addi    sp, sp, 4

	# disk_read returns a0 = status byte (0 = success).
	bnez    a0, halt_no_disk

	srli    t1, t0, 9                       # chunk / 512
	add     s2, s2, t1

	# s0 += min(t0, s1); s1 -= min(t0, s1).
	bge     s1, t0, 1f
	mv      t0, s1
1:	add     s0, s0, t0
	sub     s1, s1, t0
	j       read_loop_top

read_done:

# ── Hash + check ─────────────────────────────────────────────────────────
	# Allocate 32-B scratch on stack for computed hash.
	addi    sp, sp, -32
	mv      a2, sp                          # output buf
	mv      a0, gp                          # data = full_node base
	lw      a1, -36(gp)
	CALL    gimli_hash

	# Compare 32 bytes at sp vs hash_data (= gp − 32).
	mv      t0, sp
	addi    t1, gp, -32
	li      t2, 8                           # 8 words
hash_cmp:
	lw      t3, 0(t0)
	lw      t4, 0(t1)
	bne     t3, t4, hash_mismatch
	addi    t0, t0, 4
	addi    t1, t1, 4
	addi    t2, t2, -1
	bnez    t2, hash_cmp

	# Match!  Free scratch, set handoff regs, jal over hash data to gp.
	addi    sp, sp, 32

	li      t0, SEED_LIST_OFFSET
	add     a0, s7, t0                      # a0 = seed list ptr
	li      a1, 0                           # a1 = boot source (0 = disk)
	mv      a2, s4                          # a2 = bind_port
	addi    t0, a0, DBGFLAG - SEED_LIST_OFFSET   # t0 = s7 + DBGFLAG (= a0 - 40)
	lw      a3, 0(t0)                       # a3 = debug flag
	mv      a4, gp                          # a4 = full_node base address (handoff arg)
	nop                                     # layout pad
	j       end_marker                      # gp = end_marker = full_node entry


hash_mismatch:
	addi    sp, sp, 32
	li      t6, 'H'
	sb      t6, 0(s8)
	li      t6, '\n'
	sb      t6, 0(s8)
	# Fall through to scan_net.


# ──────────────────────────────────────────────────────────────────────────────
# §5 Net boot.
#   scan_net → (or halt if no virtio-net) → handshake → RX/TX queue setup
#   → mark DRIVER_OK → kick RX → enter the REQ_RANGE seed-fetch loop
#   (probe → lock → batch-fetch via chunk bitmap → gimli_hash → handoff).
# Layout in s7's region:
#     s7 + 0x0000  RX queue 0 page (descriptors, avail, used)
#     s7 + 0x2000  16 × 1536 B RX buffers (= 0x6000 B)
#     s7 + 0x8000  TX queue 1 page
# ──────────────────────────────────────────────────────────────────────────────

	CALL    scan_net                        # → s3 = virtio-net MMIO base

	# ── Reset used.idx after disk path. ────────────────────────────────
	# disk_read uses the same V_QPFN = s7 (legacy MMIO 1-page-per-queue
	# layout) as the net RX queue.  Each disk read bumps the device's
	# used.idx at s7+0x1002 and writes a status entry at s7+0x1004.
	# After the 48 disk reads needed to load a 3 MiB full_node.bin,
	# used.idx = 48; net rx_loop would then walk through 48 phantom
	# 1-byte "packets" pointing into zero-filled buffers, never see a
	# real BIN0 reply in time, and halt 'N'.  Just zero used.flags +
	# used.idx (4 B) — stale used.ring[] entries are harmless since the
	# device overwrites them as it processes new packets.  Don't touch
	# the FSM control region at s7+0x9FDA..0x9FFF (TIMETIK lives there)
	# nor the seed list at s7+0xA000.
	li      t0, 0x1000
	add     t0, s7, t0
	sw      zero, 0(t0)                     # used.flags = used.idx = 0

	# ── Virtio-net handshake (legacy MMIO) ─────────────────────────────
	sw      zero, 0x70(s3)                  # status = 0
	li      t1, 1
	sw      t1, 0x70(s3)                    # status = 1 (ACK)
	lw      t1, 0x70(s3)
	ori     t1, t1, 2
	sw      t1, 0x70(s3)                    # status |= 2 (DRIVER)
	li      t1, 0x8020                      # negotiate F_MAC | F_MRG_RXBUF
	sw      t1, 0x20(s3)                    # V_DRVF
	lw      t1, 0x70(s3)
	ori     t1, t1, 8
	sw      t1, 0x70(s3)                    # status |= 8 (FEATURES_OK)
	li      t1, PAGE_SIZE
	sw      t1, 0x28(s3)                    # V_GPS = 0x1000

	# ── RX queue (queue 0, 16 entries × 1536 B buffers) ───────────────
	sw      zero, 0x30(s3)                  # V_QSEL = 0
	li      t1, 16
	sw      t1, 0x38(s3)                    # V_QNUM = 16
	li      t1, PAGE_SIZE
	sw      t1, 0x3C(s3)                    # V_QALGN
	srli    t1, s7, 12
	sw      t1, 0x40(s3)                    # V_QPFN = s7 >> 12 (RX queue at s7)

	# Populate 16 RX descriptors.  desc base = s7; buffer base = s7+0x2000.
	mv      t0, s7                          # descriptor walker
	li      t6, 0x2000
	add     t2, s7, t6                      # buffer walker = s7 + 0x2000
	li      t3, 0                           # i
	li      t5, 1536
rx_desc_top:
	li      t6, 16
	bge     t3, t6, rx_desc_done
	sw      t2, 0(t0)                       # desc[i].addr = buffer
	sw      zero, 4(t0)                     # addr_hi = 0
	sw      t5, 8(t0)                       # desc[i].len = 1536
	li      t6, 2
	sh      t6, 12(t0)                      # flags = WRITE
	sh      zero, 14(t0)                    # next = 0
	# avail.ring[i] = i  (avail ring at s7 + 256+4)
	addi    t6, s7, 260                     # &avail.ring[0]
	slli    t4, t3, 1                       # i*2
	add     t4, t6, t4                      # &avail.ring[i]
	sh      t3, 0(t4)
	# advance
	addi    t0, t0, 16                      # next descriptor
	add     t2, t2, t5                      # next buffer
	addi    t3, t3, 1
	j       rx_desc_top
rx_desc_done:
	li      t1, 16
	addi    t6, s7, 258                     # avail.idx
	sh      t1, 0(t6)

	# ── TX queue (queue 1, SIZE = 1) ──────────────────────────────────
	# V_QNUM = 1 forces every TX to drain before the next is posted.
	# With V_QNUM = 16, repeated tx_req_range calls let avail.idx run
	# 16+ entries ahead of used.idx whenever slirp couldn't deliver
	# responses (e.g., non-loopback IPs while ARP is pending), tripping
	# QEMU's "Guest moved used index" virtio violation and wedging the
	# device.  Hence V_QNUM = 1.
	li      t1, 1
	sw      t1, 0x30(s3)                    # V_QSEL = 1
	sw      t1, 0x38(s3)                    # V_QNUM = 1
	li      t1, PAGE_SIZE
	sw      t1, 0x3C(s3)
	li      t6, 0x8000
	add     t1, s7, t6
	srli    t1, t1, 12
	sw      t1, 0x40(s3)                    # V_QPFN = (s7+0x8000) >> 12

	# ── Driver ready + kick RX ────────────────────────────────────────
	fence   iorw, ow
	lw      t1, 0x70(s3)
	ori     t1, t1, 4
	sw      t1, 0x70(s3)                    # status |= 4 (DRIVER_OK)
	fence   iorw, ow
	sw      zero, 0x50(s3)                  # notify queue 0 (RX)


# ──────────────────────────────────────────────────────────────────────────────
# §6 Fetching the node from the network, in the node's own protocol
# (src/peer.fam, src/image.fam): magic "TBRN" ("TBRD" on dev), version 12,
# type, body; numbers big-endian.
#
#   GET_HOSTS (1)   nonce u64, max u16, zero padding  (the answer is at most
#                   3x the ask, so it's padded to 48 bytes for 16 hosts)
#   HOSTS (2)       nonce u64, cookie u64, count u16, count x (ip, port)
#   GET_BIN (15)    cookie u64, hash (32), first u32, count u16
#   BIN_CHUNK (16)  hash (32), index u32, up to 1024 bytes
#
# Discovery first: every host in the peer table is asked GET_HOSTS -- the
# seeds, then the hosts they name (127.x becomes 10.0.2.2, this machine under
# QEMU, as the node does for its seed), up to MAX_PEERS.  A HOSTS answer
# (with our nonce, from the host asked) makes it a peer and carries its
# cookie.  Then the image, in windows of WINDOW chunks: every tick, each peer
# that has sent chunks is asked for the next window still missing, and the
# rest are tried every eighth tick (Rust nodes, and nodes with another build,
# never answer).  The seeds are asked only once SEED_WAIT has passed with no
# other peer sending any -- the image comes from the network, not the seeds,
# whenever anyone else has it.  Chunks are taken only from peers, only for
# our hash, each once (the bitmap).  When all are in, the image is hashed:
# a match boots it; a mismatch drops every peer that sent chunks and starts
# over.  No progress for the timeout (discovery or chunks) halts 'N'.
#
# Peer table at s7 + PEERS, MAX_PEERS x 16 B:
#     +0 ip (4 B, network order)  +4 port (2 B, network order)
#     +6 state: 0 new, 1 asked for hosts, 2 a peer (cookie), 3 dropped
#     +7 flags: bit 0 seed, bit 1 sent chunks; bits 4..7 GET_HOSTS asks
#     +8 cookie (8 B, as received)
#
# Pinned registers:
#     s0 = consumed RX used.idx       s1 = chunks received
#     s2 = NCHUNKS                    s3 = virtio-net MMIO base
#     s4 = bind port                  s5 = seed count (parsed)
#     s7 = data region base           s8 = UART base
#     gp = full_node base (write target)
# Per packet: a2 = RX buffer, a1 = its bytes, a7 = its descriptor.
# ──────────────────────────────────────────────────────────────────────────────

	.equ PEERS,                 0xA800      # peer table
	.equ MAX_PEERS,                 32
	.equ NPEERS,                0x9FD0      # entries in the peer table (4 B)
	.equ NETMAGIC,              0x9FD4      # "TBRN" or "TBRD", as a LE word
	.equ CURSOR,                0x9FC8      # next chunk to ask for (4 B)
	.equ LASTTICK,              0x9FC4      # mtime of the last tick (4 B)
	.equ T_START,               0x9FC0      # mtime the fetch started (4 B)
	.equ HAVE_NS,               0x9FBC      # a non-seed peer has sent chunks (4 B)
	.equ TICKN,                 0x9FB8      # ticks so far (4 B)
	.equ NONCE,                 0x9FB0      # our GET_HOSTS nonce (8 B)
	.equ ADDRTMP,               0x9FA8      # a seed's address, as a host's (6 B)
	.equ TICK_TK,              2500000      # 250 ms a tick
	.equ SEED_WAIT_TK,        30000000      # 3 s before asking seeds for chunks
	.equ WINDOW,                    32      # chunks a GET_BIN
	.equ PKT,                   0x8236      # the TX payload (frame + 42)

	li      t1, 1
	sw      t1, 0x30(s3)                    # V_QSEL = 1 (TX)
	fence   iorw, ow

	li      t0, 0x1000
	add     t0, s7, t0
	lhu     s0, 2(t0)                       # consumed = the device's used.idx
	li      s1, 0
	lw      s2, -40(gp)                     # NCHUNKS

	# Our magic: dev ("TBRD") or main ("TBRN").
	li      t0, NETFLAG
	add     t0, s7, t0
	lw      t1, 0(t0)
	li      t2, 0x4E524254                  # "TBRN"
	beqz    t1, 1f
	li      t2, 0x44524254                  # "TBRD"
1:	li      t0, NETMAGIC
	add     t0, s7, t0
	sw      t2, 0(t0)

	# The nonce: the time, and "TABN".
	li      t0, MTIME_ADDR
	lw      t1, 0(t0)
	li      t0, NONCE
	add     t0, s7, t0
	sw      t1, 0(t0)
	li      t1, 0x4E424154
	sw      t1, 4(t0)

	# Clocks: the start, the watchdog; the first tick is now.
	li      t0, MTIME_ADDR
	lw      t1, 0(t0)
	li      t0, T_START
	add     t0, s7, t0
	sw      t1, 0(t0)
	li      t0, WD_TICK
	add     t0, s7, t0
	sw      t1, 0(t0)
	li      t0, TICK_TK
	sub     t1, t1, t0
	li      t0, LASTTICK
	add     t0, s7, t0
	sw      t1, 0(t0)

	# The seeds into the peer table (their ports are LE in the seed list).
	li      s6, 0
seed_top:
	bge     s6, s5, seed_done
	li      t0, SEED_LIST_OFFSET
	add     t0, s7, t0
	addi    t0, t0, 1
	slli    t1, s6, 2
	add     t0, t0, t1
	slli    t1, s6, 1
	add     t0, t0, t1                      # &seed[s6]
	li      a0, ADDRTMP
	add     a0, s7, a0
	lbu     t1, 0(t0); sb t1, 0(a0)
	lbu     t1, 1(t0); sb t1, 1(a0)
	lbu     t1, 2(t0); sb t1, 2(a0)
	lbu     t1, 3(t0); sb t1, 3(a0)
	lbu     t1, 5(t0); sb t1, 4(a0)         # port, big-endian
	lbu     t1, 4(t0); sb t1, 5(a0)
	li      a1, 1                           # a seed
	CALL    add_peer
	addi    s6, s6, 1
	j       seed_top
seed_done:
	li      t0, NPEERS
	add     t0, s7, t0
	lw      t0, 0(t0)
	beqz    t0, halt_no_net                 # no one to ask

# ── The loop: a packet, or else (when it's time) a tick. ────────────────
net_loop:
	bge     s1, s2, net_done
	fence   iorw, iorw
	li      t6, 0x1000
	add     t0, s7, t6                      # RX used ring
	lhu     t1, 2(t0)
	beq     t1, s0, net_idle
	andi    t2, s0, 15
	slli    t2, t2, 3
	add     t2, t0, t2
	lw      a7, 4(t2)                       # descriptor
	lw      a1, 8(t2)                       # bytes written
	slli    t3, a7, 4
	add     t3, s7, t3
	lw      a2, 0(t3)                       # buffer

	lhu     t4, 24(a2)                      # ethertype
	li      t5, 0x0608
	beq     t4, t5, arp_reply
	li      t5, 0x0008
	bne     t4, t5, rx_refill
	lbu     t4, 48(a2)                      # UDP destination port
	slli    t4, t4, 8
	lbu     t5, 49(a2)
	or      t4, t4, t5
	bne     t4, s4, rx_refill
	addi    t0, a1, -60                     # at least our header
	bltz    t0, rx_refill
	li      t0, NETMAGIC
	add     t0, s7, t0
	lhu     t1, 0(t0)
	lhu     t4, 54(a2)
	bne     t4, t1, rx_refill
	lhu     t1, 2(t0)
	lhu     t4, 56(a2)
	bne     t4, t1, rx_refill
	lbu     t4, 58(a2)
	li      t5, 12                          # version
	bne     t4, t5, rx_refill
	lbu     t4, 59(a2)                      # type
	li      t5, 2
	beq     t4, t5, rx_hosts
	li      t5, 16
	beq     t4, t5, rx_chunk
	j       rx_refill

# HOSTS: nonce 60, cookie 68, count 76, hosts 78.
rx_hosts:
	addi    t0, a1, -78
	bltz    t0, rx_refill
	li      t0, NONCE
	add     t0, s7, t0
	addi    t1, a2, 60
	li      t2, 8
1:	lbu     t3, 0(t0)
	lbu     t4, 0(t1)
	bne     t3, t4, rx_refill               # not our nonce
	addi    t0, t0, 1
	addi    t1, t1, 1
	addi    t2, t2, -1
	bnez    t2, 1b
	CALL    find_src
	beqz    a5, rx_refill
	lbu     t0, 6(a5)
	li      t1, 1
	bne     t0, t1, rx_refill               # only the hosts we asked
	li      t0, 2
	sb      t0, 6(a5)                       # a peer
	addi    t0, a2, 68
	addi    t1, a5, 8
	li      t2, 8
1:	lbu     t3, 0(t0)                       # its cookie for us
	sb      t3, 0(t1)
	addi    t0, t0, 1
	addi    t1, t1, 1
	addi    t2, t2, -1
	bnez    t2, 1b
	lbu     a3, 76(a2)                      # count
	slli    a3, a3, 8
	lbu     t0, 77(a2)
	or      a3, a3, t0
	addi    a4, a1, -78                     # bytes of hosts
	addi    a6, a2, 78                      # the next host
rh_host:
	beqz    a3, rh_done
	addi    a4, a4, -6
	bltz    a4, rh_done
	mv      a0, a6
	li      a1, 0                           # not a seed
	CALL    add_peer
	addi    a6, a6, 6
	addi    a3, a3, -1
	j       rh_host
rh_done:
	CALL    progress
	j       rx_refill

# BIN_CHUNK: hash 60, index 92, data 96.
rx_chunk:
	addi    t0, a1, -97
	bltz    t0, rx_refill
	CALL    find_src
	beqz    a5, rx_refill
	lbu     t0, 6(a5)
	li      t1, 2
	bne     t0, t1, rx_refill               # only peers (and not dropped)
	addi    t0, a2, 60
	addi    t1, gp, -32                     # our hash
	li      t2, 32
1:	lbu     t3, 0(t0)
	lbu     t4, 0(t1)
	bne     t3, t4, rx_refill               # another build
	addi    t0, t0, 1
	addi    t1, t1, 1
	addi    t2, t2, -1
	bnez    t2, 1b
	lbu     t4, 92(a2)                      # index
	lbu     t0, 93(a2)
	slli    t4, t4, 8
	or      t4, t4, t0
	lbu     t0, 94(a2)
	slli    t4, t4, 8
	or      t4, t4, t0
	lbu     t0, 95(a2)
	slli    t4, t4, 8
	or      t4, t4, t0
	bgeu    t4, s2, rx_refill
	srli    t6, t4, 3                       # the bitmap: once each
	li      t3, NB_BMAP
	add     t3, s7, t3
	add     t3, t3, t6
	lbu     t6, 0(t3)
	andi    t2, t4, 7
	li      t1, 1
	sll     t1, t1, t2
	and     t2, t6, t1
	bnez    t2, rx_refill
	or      t6, t6, t1
	sb      t6, 0(t3)
	lbu     t0, 7(a5)                       # the peer has sent chunks
	ori     t0, t0, 2
	sb      t0, 7(a5)
	andi    t0, t0, 1
	bnez    t0, 1f
	li      t0, HAVE_NS
	add     t0, s7, t0
	li      t1, 1
	sw      t1, 0(t0)
1:	slli    t5, t4, 10
	add     t5, gp, t5                      # dst = gp + index * 1024
	addi    a3, a2, 96
	addi    a4, a1, -96
	li      t6, 1024
	ble     a4, t6, 1f
	mv      a4, t6
1:	lw      t6, -36(gp)                     # no further than the image's end
	add     t6, gp, t6
	sub     t6, t6, t5
	ble     a4, t6, 1f
	mv      a4, t6
1:	blez    a4, 2f
	lbu     t6, 0(a3)
	sb      t6, 0(t5)
	addi    a3, a3, 1
	addi    t5, t5, 1
	addi    a4, a4, -1
	j       1b
2:	addi    s1, s1, 1
	CALL    progress
	j       rx_refill

arp_reply:
	# Build ARP reply directly into the shared TX buffer at s7+0x820C
	# (vnet hdr at s7+0x8200, 12 B).  Single NTX_BUF at +0x8200.  42-byte
	# frame.
	li      t6, 0x820C
	add     a3, s7, t6                      # frame base
	# Ethernet: dst = sender of ARP req (a2+18, 6 bytes) via halfwords.
	lhu     t4, 18(a2); sh t4, 0(a3)
	lhu     t4, 20(a2); sh t4, 2(a3)
	lhu     t4, 22(a2); sh t4, 4(a3)
	# src MAC = 52:54:00:12:34:56 via halfwords
	li      t4, 0x5452; sh t4, 6(a3)
	li      t4, 0x1200; sh t4, 8(a3)
	li      t4, 0x5634; sh t4, 10(a3)
	# ethertype 0x0806 (LE: {06,08})
	li      t4, 0x0608; sh t4, 12(a3)
	# ARP body: HW type, proto, lengths (6 B) via halfwords.
	lhu     t4, 26(a2); sh t4, 14(a3)
	lhu     t4, 28(a2); sh t4, 16(a3)
	lhu     t4, 30(a2); sh t4, 18(a3)
	# op = 2 (reply) BE: {00,02} → LE halfword 0x0200
	li      t4, 0x0200; sh t4, 20(a3)
	# sender (us): MAC copied from Ethernet src (offset 6), IP 10.0.2.15
	lhu     t4, 6(a3);  sh t4, 22(a3)
	lhu     t4, 8(a3);  sh t4, 24(a3)
	lhu     t4, 10(a3); sh t4, 26(a3)
	li      t4, 0x000A; sh t4, 28(a3)
	li      t4, 0x0F02; sh t4, 30(a3)
	# target = incoming sender MAC (pkt+34) + IP (pkt+40) via halfwords.
	lhu     t4, 34(a2); sh t4, 32(a3)
	lhu     t4, 36(a2); sh t4, 34(a3)
	lhu     t4, 38(a2); sh t4, 36(a3)
	lhu     t4, 40(a2); sh t4, 38(a3)
	lhu     t4, 42(a2); sh t4, 40(a3)
	li      a0, 54                          # 12 vnet + 42 ARP frame
	CALL    tx_submit
	j       rx_refill

rx_refill:
	# Repost the consumed descriptor (a7).
	addi    t0, s7, 256                     # RX avail base
	lhu     t1, 2(t0)                       # avail.idx
	andi    t2, t1, 15
	slli    t2, t2, 1
	add     t2, t0, t2
	sh      a7, 4(t2)                       # ring[idx%16] = descriptor
	addi    t1, t1, 1
	sh      t1, 2(t0)                       # avail.idx += 1
	fence   iorw, ow
	sw      zero, 0x50(s3)                  # notify RX queue 0
	addi    s0, s0, 1                       # consumed++
	j       net_loop

# ── Nothing arrived: the watchdog, and the tick. ─────────────────────────
net_idle:
	li      t0, MTIME_ADDR
	lw      t1, 0(t0)                       # now
	li      t0, WD_TICK
	add     t0, s7, t0
	lw      t2, 0(t0)
	sub     t2, t1, t2
	li      t0, TIMETIK
	add     t0, s7, t0
	lw      t3, 0(t0)
	bgeu    t2, t3, halt_no_net             # no progress for the timeout
	li      t0, LASTTICK
	add     t0, s7, t0
	lw      t2, 0(t0)
	sub     t2, t1, t2
	li      t3, TICK_TK
	bltu    t2, t3, net_loop
	sw      t1, 0(t0)                       # a tick
	li      t0, TICKN
	add     t0, s7, t0
	lw      t2, 0(t0)
	addi    t2, t2, 1
	sw      t2, 0(t0)

	# Seeds may be asked for chunks: no other peer has sent any, and
	# SEED_WAIT has passed.  a6 = 1 if so.
	li      a6, 0
	li      t0, HAVE_NS
	add     t0, s7, t0
	lw      t0, 0(t0)
	bnez    t0, 1f
	li      t0, T_START
	add     t0, s7, t0
	lw      t0, 0(t0)
	sub     t0, t1, t0
	li      t2, SEED_WAIT_TK
	bltu    t0, t2, 1f
	li      a6, 1
1:
	# Walk the table: discovery, then the image.
	li      a5, PEERS
	add     a5, s7, a5
	li      t0, NPEERS
	add     t0, s7, t0
	lw      a4, 0(t0)                       # entries left
tick_peer:
	beqz    a4, net_loop
	lbu     t0, 6(a5)                       # state
	beqz    t0, tp_ask                      # new: ask for hosts
	li      t1, 1
	beq     t0, t1, tp_asked
	li      t1, 2
	beq     t0, t1, tp_peer
	j       tp_next
tp_asked:
	# Asked, no answer yet: again every fourth tick, four times in all.
	li      t0, TICKN
	add     t0, s7, t0
	lw      t0, 0(t0)
	andi    t0, t0, 3
	bnez    t0, tp_next
	lbu     t0, 7(a5)
	srli    t1, t0, 4
	li      t2, 4
	bltu    t1, t2, tp_ask
	li      t0, 3                           # never answered: dropped
	sb      t0, 6(a5)
	j       tp_next
tp_ask:
	li      t0, 1
	sb      t0, 6(a5)
	lbu     t0, 7(a5)
	addi    t0, t0, 0x10                    # one more ask
	sb      t0, 7(a5)
	CALL    send_get_hosts
	j       tp_next
tp_peer:
	lbu     t0, 7(a5)
	andi    t1, t0, 1
	beqz    t1, 1f
	beqz    a6, tp_next                     # a seed: not yet
1:	andi    t1, t0, 2
	bnez    t1, 2f                          # has sent chunks: every tick
	li      t0, TICKN                       # else every eighth
	add     t0, s7, t0
	lw      t0, 0(t0)
	andi    t0, t0, 7
	bnez    t0, tp_next
2:	CALL    next_missing                    # a0 = the first chunk to ask for
	bltz    a0, net_loop                    # nothing missing
	CALL    send_get_bin
tp_next:
	addi    a5, a5, 16
	addi    a4, a4, -1
	j       tick_peer

# ── All chunks in: hash, and boot or start over. ──────────────────────────
net_done:
	addi    sp, sp, -32
	mv      a2, sp
	mv      a0, gp
	lw      a1, -36(gp)
	CALL    gimli_hash
	mv      t0, sp
	addi    t1, gp, -32
	li      t2, 8
net_hash_cmp:
	lw      t3, 0(t0)
	lw      t4, 0(t1)
	bne     t3, t4, net_hash_mismatch
	addi    t0, t0, 4
	addi    t1, t1, 4
	addi    t2, t2, -1
	bnez    t2, net_hash_cmp

	# Match!
	addi    sp, sp, 32
	li      t0, SEED_LIST_OFFSET
	add     a0, s7, t0
	li      a1, 1                           # boot source = net
	mv      a2, s4
	addi    t0, a0, DBGFLAG - SEED_LIST_OFFSET   # t0 = s7 + DBGFLAG (= a0 - 40)
	lw      a3, 0(t0)                       # a3 = debug flag
	mv      a4, gp                          # a4 = full_node base address (handoff arg)
	nop                                     # layout pad
	j       end_marker

net_hash_mismatch:
	addi    sp, sp, 32
	li      t6, 'H'
	sb      t6, 0(s8)
	li      t6, '\n'
	sb      t6, 0(s8)
	# Drop every peer that sent chunks; forget the chunks; again.
	li      a5, PEERS
	add     a5, s7, a5
	li      t0, NPEERS
	add     t0, s7, t0
	lw      a4, 0(t0)
1:	beqz    a4, 2f
	lbu     t0, 7(a5)
	andi    t1, t0, 2
	beqz    t1, 3f
	andi    t0, t0, 0xFD
	sb      t0, 7(a5)
	li      t0, 3
	sb      t0, 6(a5)
3:	addi    a5, a5, 16
	addi    a4, a4, -1
	j       1b
2:	li      t0, NB_BMAP
	add     t0, s7, t0
	li      t1, NB_BMAP_BYTES / 4
1:	sw      zero, 0(t0)
	addi    t0, t0, 4
	addi    t1, t1, -1
	bnez    t1, 1b
	li      s1, 0
	li      t0, HAVE_NS
	add     t0, s7, t0
	sw      zero, 0(t0)
	CALL    progress
	j       net_loop
halt_no_disk:
panic:
	li      t6, 'N'
	j       halt_tail

halt_no_net:
	li      t6, 'N'
	beqz    s1, halt_tail
	li      t6, 'H'
halt_tail:
	sb      t6, 0(s8)
	li      t6, '\n'
	sb      t6, 0(s8)
	lui     t0, %hi(SHUTDOWN_ADDR)
	li      t1, SHUTDOWN_FAIL
	sw      t1, 0(t0)
1:	j       1b


# ──────────────────────────────────────────────────────────────────────────────
# scan_disk — walk virtio MMIO from V_SCAN_S down to V_SCAN_E looking for
#             a device with magic = 'virt' and device_id = 2 (block).
# Out:    s3 = MMIO base of the found device.
# Trashes: t0..t2.  Returns via dispatch.
# Falls through to caller's halt_no_disk path if no device found (back-jumps
# via `j halt_no_disk` instead of dispatching, so we don't pollute the BST).
# ──────────────────────────────────────────────────────────────────────────────

scan_disk:
	li      t1, 2                           # device_id we want (virtio-blk)
	j       scan_common

# ──────────────────────────────────────────────────────────────────────────────
# scan_net — same as scan_disk but looking for device_id=1 (virtio-net).
# ──────────────────────────────────────────────────────────────────────────────

scan_net:
	li      t1, 1                           # virtio-net

scan_common:
	lui     s3, 0x10008                     # start at top virtio-mmio slot
	lui     t2, 0x10001                     # lower bound (s3 >= t2)
	lui     t3, 0xFFFFF                     # -PAGE_SIZE (sign-extended u20<<12)
1:	bge     s3, t2, 2f
	j       halt_no_disk
2:	lw      t0, 8(s3)                       # device_id
	beq     t0, t1, dispatch                # found → return
	add     s3, s3, t3                      # next slot down
	j       1b


# ──────────────────────────────────────────────────────────────────────────────
# disk_read — issue a virtio-blk READ for one chunk.
#   In:   a0 = sector,  a1 = avail idx,  a2 = dest,  a3 = byte count.
#         s3 = MMIO base, s7 = queue base (page-aligned).
#   Out:  a0 = status byte (0 = success, nonzero = failure).
#   Trashes: t0..t6.  Returns via dispatch.
# Layout (offsets from s7):
#   0x000..0x180  descriptor table (3 descs × 16 B = 48 B used)
#   0x100..       available ring   (offset 256 from descriptor table)
#   0x1200        status byte   (1 B)
#   0x1202        request header (16 B)
# ──────────────────────────────────────────────────────────────────────────────

disk_read:
	mv      t1, s7                          # t1 = queue base
	li      t3, 0x1200
	add     t3, s7, t3                      # t3 = status byte addr
	addi    t2, t3, 2                       # t2 = req hdr addr

	# Request header (16 B at t2): type=READ(0), reserved=0, sector(lo,hi).
	sw      zero, 0(t2)
	sw      zero, 4(t2)
	sw      a0, 8(t2)
	sw      zero, 12(t2)

	# Descriptor[0]: req hdr.
	sw      t2, 0(t1)
	sw      zero, 4(t1)
	li      t4, 16
	sw      t4, 8(t1)
	li      t4, 1
	sh      t4, 12(t1)                      # flags = NEXT
	sh      t4, 14(t1)                      # next  = 1
	sw      t4, 0x28(t1)                    # desc[2].len = 1

	# Descriptor[1]: data buffer.
	sw      a2, 16(t1)
	sw      zero, 20(t1)
	sw      a3, 24(t1)
	li      t4, 2
	sh      t4, 30(t1)                      # next  = 2
	sh      t4, 0x2C(t1)                    # desc[2].flags = WRITE
	li      t4, 3
	sh      t4, 28(t1)                      # desc[1].flags = NEXT|WRITE

	# Descriptor[2]: status byte.
	sw      t3, 32(t1)
	sw      zero, 36(t1)
	sh      zero, 0x2E(t1)                  # next = 0

	# Available ring at t1+256.
	addi    t4, t1, 256
	sh      zero, 0(t4)                     # avail.flags = 0
	li      t5, 0xFF
	sb      t5, 0(t3)                       # status byte = 0xFF (init)
	sh      a1, 2(t4)                       # avail.ring[0]
	sh      zero, 4(t4)                     # avail.idx (placeholder)

	fence   iorw, ow
	# Notify device.
	sw      zero, 0x50(s3)

	# Poll status byte (no watchdog yet — virtio-blk under qemu always responds).
dr_poll:
	lbu     t4, 0(t3)
	li      t5, 0xFF
	beq     t4, t5, dr_poll

	fence   ir, iorw
	mv      a0, t4
	j       dispatch


# ──────────────────────────────────────────────────────────────────────────────
# gimli_permute — 384-bit Gimli permutation, 24 rounds.
#   In/out:  state at a0 (12 × 32-bit LE words).
#   Trashes: t0..t6, s0, s1.
#   Returns via `j dispatch`.
#
# Per round (r descending 24..1):
#   for col in 0..3:
#       x = rotl(state[col],     24)
#       y = rotl(state[col + 4],  9)
#       z =       state[col + 8]
#       state[col + 8] = x ^ (z << 1) ^ ((y & z) << 2)
#       state[col + 4] = y ^ x        ^ ((x | z) << 1)
#       state[col]     = z ^ y        ^ ((x & y) << 3)
#   if r % 4 == 0: small-swap + state[0] ^= 0x9e377900 | r
#   if r % 4 == 2: big-swap
# ──────────────────────────────────────────────────────────────────────────────

gimli_permute:
	# Save s0/s1 — callees must per RISC-V ABI; gimli_hash relies on s1.
	addi    sp, sp, -8
	sw      s0, 0(sp)
	sw      s1, 4(sp)
	mv      s0, a0                          # state base
	li      s1, 24                          # round counter

gp_round:
	mv      a0, s0
	li      t6, 4

gp_col:
	lw      t3, 0(a0)
	lw      t4, 16(a0)
	lw      t5, 32(a0)

	# x = rotl(t3, 24)
	slli    t0, t3, 24
	srli    t1, t3, 8
	or      t0, t0, t1

	# y = rotl(t4, 9)
	slli    t1, t4, 9
	srli    t2, t4, 23
	or      t1, t1, t2

	# state[col]     = z ^ y ^ ((x & y) << 3)
	and     t3, t0, t1
	slli    t3, t3, 3
	xor     t3, t3, t5
	xor     t3, t3, t1
	sw      t3, 0(a0)

	# state[col + 4] = y ^ x ^ ((x | z) << 1)
	or      t4, t0, t5
	slli    t4, t4, 1
	xor     t4, t4, t1
	xor     t4, t4, t0
	sw      t4, 16(a0)

	# state[col + 8] = x ^ (z << 1) ^ ((y & z) << 2)
	and     t2, t1, t5
	slli    t2, t2, 2
	slli    t5, t5, 1
	xor     t5, t5, t0
	xor     t5, t5, t2
	sw      t5, 32(a0)

	addi    a0, a0, 4
	addi    t6, t6, -1
	bnez    t6, gp_col

	andi    t0, s1, 3
	bnez    t0, gp_check_2
	# Small swap.
	lw      t0, 0(s0)
	lw      t1, 4(s0)
	sw      t1, 0(s0)
	sw      t0, 4(s0)
	lw      t0, 8(s0)
	lw      t1, 12(s0)
	sw      t1, 8(s0)
	sw      t0, 12(s0)
	# Round constant.
	li      t0, 0x9E377900
	or      t0, t0, s1
	lw      t1, 0(s0)
	xor     t1, t1, t0
	sw      t1, 0(s0)
	j       gp_next

gp_check_2:
	li      t1, 2
	bne     t0, t1, gp_next
	# Big swap.
	lw      t0, 0(s0)
	lw      t1, 8(s0)
	sw      t1, 0(s0)
	sw      t0, 8(s0)
	lw      t0, 4(s0)
	lw      t1, 12(s0)
	sw      t1, 4(s0)
	sw      t0, 12(s0)

gp_next:
	addi    s1, s1, -1
	bnez    s1, gp_round
	lw      s0, 0(sp)
	lw      s1, 4(sp)
	addi    sp, sp, 8
	j       dispatch


# ──────────────────────────────────────────────────────────────────────────────
# gimli_hash — sponge construction over gimli_permute.
#   a0 = data ptr,  a1 = length,  a2 = 32-byte output buf.
#   Uses s0..s3 internally; saves and restores all of them so callers'
#   pinned values survive (s3 in particular is the virtio-net MMIO base,
#   without which post-hash net I/O would silently target stack memory).
#   Returns via `j dispatch`.
# ──────────────────────────────────────────────────────────────────────────────

gimli_hash:
	addi    sp, sp, -64
	sw      s0,  0(sp)                      # save callee-saved s-regs we
	sw      s1,  4(sp)                      # use as scratch (s3 in
	sw      s2,  8(sp)                      # particular is the virtio-net
	sw      s3, 12(sp)                      # MMIO base — must be preserved)
	# state base = sp + 16 (12 words = 48 bytes, fits in sp+16..sp+64)

	li      t0, 12
	addi    t1, sp, 16
gh_zero:
	sw      zero, 0(t1)
	addi    t1, t1, 4
	addi    t0, t0, -1
	bnez    t0, gh_zero

	addi    s0, sp, 16                      # state base
	mv      s1, a0                          # data ptr
	mv      s2, a1                          # remaining
	mv      s3, a2                          # output buf

gh_absorb:
	li      t0, 16
	blt     s2, t0, gh_pad

	mv      t2, s0
	mv      t3, s1
	li      t4, 4
gh_xor_abs:
	lw      t0, 0(t3)
	lw      t1, 0(t2)
	xor     t1, t1, t0
	sw      t1, 0(t2)
	addi    t2, t2, 4
	addi    t3, t3, 4
	addi    t4, t4, -1
	bnez    t4, gh_xor_abs

	mv      a0, s0
	CALL    gimli_permute

	addi    s1, s1, 16
	addi    s2, s2, -16
	j       gh_absorb

gh_pad:
	beqz    s2, gh_pad_skipcopy
	mv      t2, s0
	mv      t3, s1
	mv      t4, s2
gh_pad_copy:
	lbu     t0, 0(t3)
	lbu     t1, 0(t2)
	xor     t1, t1, t0
	sb      t1, 0(t2)
	addi    t2, t2, 1
	addi    t3, t3, 1
	addi    t4, t4, -1
	bnez    t4, gh_pad_copy
gh_pad_skipcopy:

	add     t0, s0, s2
	lbu     t1, 0(t0)
	xori    t1, t1, 0x01
	sb      t1, 0(t0)

	lbu     t1, 15(s0)
	xori    t1, t1, 0x80
	sb      t1, 15(s0)

	lbu     t1, 47(s0)
	xori    t1, t1, 0x01
	sb      t1, 47(s0)

	mv      a0, s0
	CALL    gimli_permute

	# Squeeze first 16 B.
	lw      t0, 0(s0)
	sw      t0, 0(s3)
	lw      t0, 4(s0)
	sw      t0, 4(s3)
	lw      t0, 8(s0)
	sw      t0, 8(s3)
	lw      t0, 12(s0)
	sw      t0, 12(s3)

	mv      a0, s0
	CALL    gimli_permute

	# Squeeze second 16 B.
	lw      t0, 0(s0)
	sw      t0, 16(s3)
	lw      t0, 4(s0)
	sw      t0, 20(s3)
	lw      t0, 8(s0)
	sw      t0, 24(s3)
	lw      t0, 12(s0)
	sw      t0, 28(s3)

	lw      s0,  0(sp)
	lw      s1,  4(sp)
	lw      s2,  8(sp)
	lw      s3, 12(sp)
	addi    sp, sp, 64
	j       dispatch


# ──────────────────────────────────────────────────────────────────────────────
# progress — the watchdog's last progress is now.  Trashes t0, t1.
# ──────────────────────────────────────────────────────────────────────────────
progress:
	li      t0, MTIME_ADDR
	lw      t1, 0(t0)
	li      t0, WD_TICK
	add     t0, s7, t0
	sw      t1, 0(t0)
	j       dispatch

# ──────────────────────────────────────────────────────────────────────────────
# add_peer — a0 = an address (ip 4 B, port 2 B, network order), a1 = flags.
#   Added to the peer table, new, unless it's there already, the table is
#   full, or the address is 0.x.x.x or port 0.  127.x.x.x is 10.0.2.2.
#   Trashes t0..t6.
# ──────────────────────────────────────────────────────────────────────────────
add_peer:
	lbu     t0, 0(a0)
	lbu     t1, 1(a0)
	lbu     t2, 2(a0)
	lbu     t3, 3(a0)
	lbu     t4, 4(a0)
	lbu     t5, 5(a0)
	beqz    t0, ap_done
	li      t6, 127
	bne     t0, t6, 1f
	li      t0, 10
	li      t1, 0
	li      t2, 2
	li      t3, 2
1:	slli    t1, t1, 8
	or      t0, t0, t1
	slli    t2, t2, 16
	or      t0, t0, t2
	slli    t3, t3, 24
	or      t0, t0, t3                      # the ip, as it sits in memory
	slli    t5, t5, 8
	or      t4, t4, t5                      # the port, likewise
	beqz    t4, ap_done
	li      t1, PEERS
	add     t1, s7, t1
	li      t2, NPEERS
	add     t2, s7, t2
	lw      t3, 0(t2)
	mv      t5, t3
2:	beqz    t5, 3f
	lw      t6, 0(t1)
	bne     t6, t0, 4f
	lhu     t6, 4(t1)
	beq     t6, t4, ap_done                 # there already
4:	addi    t1, t1, 16
	addi    t5, t5, -1
	j       2b
3:	li      t6, MAX_PEERS
	bge     t3, t6, ap_done                 # full
	sw      t0, 0(t1)
	sh      t4, 4(t1)
	sb      zero, 6(t1)
	sb      a1, 7(t1)
	sw      zero, 8(t1)
	sw      zero, 12(t1)
	addi    t3, t3, 1
	sw      t3, 0(t2)
ap_done:
	j       dispatch

# ──────────────────────────────────────────────────────────────────────────────
# find_src — a2 = an RX buffer.  a5 = the peer table's entry for the packet's
#   source (ip and port), or 0.  Trashes t0..t3.
# ──────────────────────────────────────────────────────────────────────────────
find_src:
	lbu     t0, 38(a2)
	lbu     t1, 39(a2)
	slli    t1, t1, 8
	or      t0, t0, t1
	lbu     t1, 40(a2)
	slli    t1, t1, 16
	or      t0, t0, t1
	lbu     t1, 41(a2)
	slli    t1, t1, 24
	or      t0, t0, t1
	lbu     t2, 46(a2)
	lbu     t1, 47(a2)
	slli    t1, t1, 8
	or      t2, t2, t1
	li      a5, PEERS
	add     a5, s7, a5
	li      t3, NPEERS
	add     t3, s7, t3
	lw      t3, 0(t3)
1:	beqz    t3, 2f
	lw      t1, 0(a5)
	bne     t1, t0, 3f
	lhu     t1, 4(a5)
	beq     t1, t2, fs_done
3:	addi    a5, a5, 16
	addi    t3, t3, -1
	j       1b
2:	li      a5, 0
fs_done:
	j       dispatch

# ──────────────────────────────────────────────────────────────────────────────
# next_missing — a0 = the first chunk not yet received at or after CURSOR
#   (wrapping), or -1 if none; CURSOR moves a window past it.  Trashes t0..t5.
# ──────────────────────────────────────────────────────────────────────────────
next_missing:
	li      t0, CURSOR
	add     t0, s7, t0
	lw      a0, 0(t0)
	mv      t5, s2                          # chunks left to look at
	li      t4, NB_BMAP
	add     t4, s7, t4
1:	beqz    t5, nm_none
	bltu    a0, s2, 2f
	li      a0, 0
2:	srli    t1, a0, 3
	add     t1, t4, t1
	lbu     t1, 0(t1)
	andi    t2, a0, 7
	srl     t1, t1, t2
	andi    t1, t1, 1
	beqz    t1, 3f
	addi    a0, a0, 1
	addi    t5, t5, -1
	j       1b
3:	addi    t1, a0, WINDOW
	sw      t1, 0(t0)
	j       dispatch
nm_none:
	li      a0, -1
	j       dispatch

# ──────────────────────────────────────────────────────────────────────────────
# put_hdr — a0 = type: our header (magic, version 12, type) at PKT.
#   Trashes t0, t1.
# ──────────────────────────────────────────────────────────────────────────────
put_hdr:
	li      t0, PKT
	add     t0, s7, t0
	li      t1, NETMAGIC
	add     t1, s7, t1
	lw      t1, 0(t1)
	sb      t1, 0(t0)
	srli    t1, t1, 8
	sb      t1, 1(t0)
	srli    t1, t1, 8
	sb      t1, 2(t0)
	srli    t1, t1, 8
	sb      t1, 3(t0)
	li      t1, 12
	sb      t1, 4(t0)
	sb      a0, 5(t0)
	j       dispatch

# ──────────────────────────────────────────────────────────────────────────────
# send_get_hosts — a5 = a peer table entry: GET_HOSTS (our nonce, 16 hosts),
#   padded to 48 bytes.  Trashes t0..t6, a0, a1.
# ──────────────────────────────────────────────────────────────────────────────
send_get_hosts:
	li      a0, 1
	CALL    put_hdr
	li      t0, PKT + 6
	add     t0, s7, t0
	li      t1, NONCE
	add     t1, s7, t1
	li      t2, 8
1:	lbu     t3, 0(t1)
	sb      t3, 0(t0)
	addi    t0, t0, 1
	addi    t1, t1, 1
	addi    t2, t2, -1
	bnez    t2, 1b
	sb      zero, 0(t0)                     # max = 16
	li      t1, 16
	sb      t1, 1(t0)
	addi    t0, t0, 2
	li      t2, 32                          # padding
1:	sb      zero, 0(t0)
	addi    t0, t0, 1
	addi    t2, t2, -1
	bnez    t2, 1b
	mv      a0, a5
	li      a1, 48
	CALL    tx_udp
	j       dispatch

# ──────────────────────────────────────────────────────────────────────────────
# send_get_bin — a5 = a peer table entry, a0 = the first chunk: GET_BIN (its
#   cookie, our hash, a0, WINDOW).  Trashes t0..t6, a0, a1.
# ──────────────────────────────────────────────────────────────────────────────
send_get_bin:
	li      t0, PKT + 46                    # first (u32, big-endian)
	add     t0, s7, t0
	srli    t1, a0, 24
	sb      t1, 0(t0)
	srli    t1, a0, 16
	sb      t1, 1(t0)
	srli    t1, a0, 8
	sb      t1, 2(t0)
	sb      a0, 3(t0)
	sb      zero, 4(t0)                     # count
	li      t1, WINDOW
	sb      t1, 5(t0)
	li      a0, 15
	CALL    put_hdr
	li      t0, PKT + 6
	add     t0, s7, t0
	addi    t1, a5, 8                       # the cookie
	li      t2, 8
1:	lbu     t3, 0(t1)
	sb      t3, 0(t0)
	addi    t0, t0, 1
	addi    t1, t1, 1
	addi    t2, t2, -1
	bnez    t2, 1b
	addi    t1, gp, -32                     # our hash
	li      t2, 32
1:	lbu     t3, 0(t1)
	sb      t3, 0(t0)
	addi    t0, t0, 1
	addi    t1, t1, 1
	addi    t2, t2, -1
	bnez    t2, 1b
	mv      a0, a5
	li      a1, 52
	CALL    tx_udp
	j       dispatch

# ──────────────────────────────────────────────────────────────────────────────
# tx_udp — a0 = a peer table entry, a1 = the payload's length (at PKT): the
#   Ethernet, IPv4 and UDP headers to it, from the bind port, and send.
#   Trashes t0..t6, a0, a1.
# ──────────────────────────────────────────────────────────────────────────────
tx_udp:
	li      t0, 0x820C
	add     t0, s7, t0                      # frame
	# ── Ethernet (14 B): dst gateway MAC, src guest MAC, ethertype 0x0800 ──
	li      t1, 0x52; sb t1, 0(t0)
	li      t1, 0x55; sb t1, 1(t0)
	li      t1, 0x0A; sb t1, 2(t0)
	sb      zero, 3(t0)
	li      t1, 0x02; sb t1, 4(t0); sb t1, 5(t0)
	li      t1, 0x52; sb t1, 6(t0)
	li      t1, 0x54; sb t1, 7(t0)
	sb      zero, 8(t0)
	li      t1, 0x12; sb t1, 9(t0)
	li      t1, 0x34; sb t1, 10(t0)
	li      t1, 0x56; sb t1, 11(t0)
	li      t1, 0x08; sb t1, 12(t0)
	sb      zero, 13(t0)
	# ── IPv4 (20 B) at frame + 14 ──
	addi    t0, t0, 14
	li      t1, 0x45; sb t1, 0(t0)
	sb      zero, 1(t0)
	addi    t1, a1, 28                      # total length
	srli    t2, t1, 8
	sb      t2, 2(t0)
	sb      t1, 3(t0)
	sh      zero, 4(t0)
	sh      zero, 6(t0)
	li      t1, 64; sb t1, 8(t0)
	li      t1, 17; sb t1, 9(t0)             # UDP
	sh      zero, 10(t0)                     # checksum placeholder
	li      t1, 10; sb t1, 12(t0)
	sb      zero, 13(t0)
	li      t1, 2;  sb t1, 14(t0)
	li      t1, 15; sb t1, 15(t0)
	lbu     t1, 0(a0); sb t1, 16(t0)        # dst IP
	lbu     t1, 1(a0); sb t1, 17(t0)
	lbu     t1, 2(a0); sb t1, 18(t0)
	lbu     t1, 3(a0); sb t1, 19(t0)
	# IPv4 header checksum.
	mv      t1, t0
	li      t2, 10
	li      t3, 0
1:	lbu     t4, 0(t1)
	slli    t4, t4, 8
	lbu     t5, 1(t1)
	or      t4, t4, t5
	add     t3, t3, t4
	addi    t1, t1, 2
	addi    t2, t2, -1
	bnez    t2, 1b
	srli    t4, t3, 16
	li      t5, 0xFFFF
	and     t3, t3, t5
	add     t3, t3, t4
	srli    t4, t3, 16
	add     t3, t3, t4
	and     t3, t3, t5
	xor     t3, t3, t5
	srli    t1, t3, 8
	sb      t1, 10(t0)
	sb      t3, 11(t0)
	# ── UDP (8 B) at frame + 34 ──
	addi    t0, t0, 20
	srli    t1, s4, 8
	sb      t1, 0(t0)
	sb      s4, 1(t0)
	lbu     t1, 4(a0); sb t1, 2(t0)         # dst port
	lbu     t1, 5(a0); sb t1, 3(t0)
	addi    t1, a1, 8                       # length
	srli    t2, t1, 8
	sb      t2, 4(t0)
	sb      t1, 5(t0)
	sh      zero, 6(t0)                     # UDP csum (optional in IPv4)
	addi    a0, a1, 54                      # 12 vnet + 42 headers + payload
	CALL    tx_submit
	j       dispatch
# ──────────────────────────────────────────────────────────────────────────────
# tx_submit — post the shared TX buffer (s7+0x8200) as desc[0], bump
# avail.idx, fence+notify, and spin-wait for the device to drain.
#
# In:  a0 = total frame length (vnet hdr + Ethernet frame)
# Uses pinned: s3 (net MMIO), s7 (data region)
# Trashes: t0..t5.  Returns via dispatch.
# ──────────────────────────────────────────────────────────────────────────────
tx_submit:
	li      t0, 0x8200
	add     t0, s7, t0
	sw      zero, 0(t0)                     # zero vnet hdr (12 B)
	sw      zero, 4(t0)
	sw      zero, 8(t0)
	li      t1, 0x8000
	add     t1, s7, t1                      # TX queue base
	sw      t0, 0(t1)                       # desc[0].addr
	sw      zero, 4(t1)
	sw      a0, 8(t1)                       # desc[0].len
	sh      zero, 12(t1)
	sh      zero, 14(t1)
	addi    t2, t1, 16                      # avail ring (queue_size=1)
	sh      zero, 4(t2)                     # ring[0] = desc 0
	lhu     t3, 2(t2)
	addi    t3, t3, 1
	sh      t3, 2(t2)                       # avail.idx += 1
	fence   iorw, ow
	li      t3, 1
	sw      t3, 0x50(s3)                    # V_QNTFY = 1 (TX queue)
	li      t5, 1000000
	li      t3, 0x9000
	add     t3, s7, t3                      # TX used ring base
	li      t4, 0x8010
	add     t4, s7, t4                      # TX avail ring base
	lhu     t0, 2(t4)                       # avail.idx target
1:	lhu     t1, 2(t3)                       # used.idx
	beq     t1, t0, 2f
	addi    t5, t5, -1
	bnez    t5, 1b
2:	j       dispatch


# ──────────────────────────────────────────────────────────────────────────────
# dispatch — single shared resume point.  Looks up s11 (return ID) in the
# BST and jumps to the corresponding .L_csret_<N> label (which sits right
# after each CALL site, where execution resumes).
# ──────────────────────────────────────────────────────────────────────────────

dispatch:
	BST 1, %_CSN


# ──────────────────────────────────────────────────────────────────────────────
# Config, patched by scripts/build.sh (patch_config): [nchunks][bin_size][hash].
# ──────────────────────────────────────────────────────────────────────────────
	.word 0x00000000                        # nchunks
	.word 0x00000000                        # bin_size
	.word 0xb8623615                        # hash (Gimli, 32 bytes)
	.word 0x981f578b
	.word 0xcdcaa182
	.word 0xcffd9910
	.word 0xc7fc60eb
	.word 0x28bb5b53
	.word 0xd9dbf4e9
	.word 0xc120b2d9
end_marker:
