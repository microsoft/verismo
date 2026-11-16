.section .note.Xen, "a", @note
.balign 4
.long 4
.long 4
.long 18
.asciz "Xen"
.balign 4
.long pvh_entry
.balign 4

.section .text.boot, "ax"
.code32
/*
 * Bootstrap page tables built below: identical construction to entry.S's
 * (see that file for the full diagram and field-by-field explanation).
 * In short: bootstrap_pml4[0] and [256] both point at the same
 * bootstrap_pdpt[0], which points at bootstrap_pd[0..511] (512 2 MiB huge
 * leaves, entry word 0x83 = PRESENT | WRITABLE | HUGE), so VA 0..1 GiB
 * (low identity) and VA 0xffff_8000_0000_0000..+1 GiB (high direct-map
 * alias) both translate to PA 0..1 GiB. This table is temporary; `bsp_main`
 * replaces it with a table built by the paging crate before starting any AP.
 */
.global pvh_entry
pvh_entry:
    cli
    cld
    movl $boot_stack_top, %esp

    movl $bootstrap_pd, %edi
    xorl %ecx, %ecx
1:
    movl %ecx, %eax
    shll $21, %eax
    orl $0x83, %eax
    movl %eax, (%edi, %ecx, 8)
    movl $0, 4(%edi, %ecx, 8)
    incl %ecx
    cmpl $512, %ecx
    jne 1b

    movl $bootstrap_pd, %eax
    orl $0x3, %eax
    movl %eax, bootstrap_pdpt
    movl $0, bootstrap_pdpt + 4

    movl $bootstrap_pdpt, %eax
    orl $0x3, %eax
    movl %eax, bootstrap_pml4
    movl $0, bootstrap_pml4 + 4
    movl %eax, bootstrap_pml4 + 2048
    movl $0, bootstrap_pml4 + 2052

    movl $bootstrap_pml4, %eax
    movl %eax, %cr3
    movl %cr4, %eax
    orl $(1 << 5), %eax
    movl %eax, %cr4

    movl $0xc0000080, %ecx
    rdmsr
    orl $((1 << 8) | (1 << 11)), %eax
    wrmsr

    lgdt gdt64_pointer
    movl %cr0, %eax
    orl $0x80000001, %eax
    movl %eax, %cr0
    ljmpl $0x08, $long_mode_entry

.code64
long_mode_entry:
    movw $0x10, %ax
    movw %ax, %ds
    movw %ax, %es
    movw %ax, %ss
    leaq boot_stack_top(%rip), %rsp
    xorq %rbp, %rbp
    callq bsp_main
2:
    cli
    hlt
    jmp 2b

.balign 8
gdt64:
    .quad 0
    .quad 0x00af9a000000ffff
    .quad 0x00af92000000ffff
gdt64_end:

gdt64_pointer:
    .word gdt64_end - gdt64 - 1
    .long gdt64

/*
 * Physical image layout (symbolic order, not literal addresses: exact
 * placement is a link detail governed by x86_64-pvh-smp.ld, not a hardware
 * contract). The executable image lives in one PT_LOAD segment above the
 * Xen note and is identity-mapped 1:1 by the bootstrap table above (and,
 * once `bsp_main` runs, by the crate-built table's own low identity mapping).
 *
 *   1 MiB -> .note    (separate PT_NOTE containing the Xen PVH entry)
 *            .text    (start of PT_LOAD: pvh_entry, long_mode_entry, bsp_main, ap_main, ...;
 *                       also this file's AP trampoline code -- see below,
 *                       it links here but never *executes* from here)
 *            .rodata
 *            .data
 *            .bss.boot (this file, below): bootstrap_pml4/pdpt/pd, boot_stack
 *            .bss (smp_guest.rs): TABLE_ARENA.tables[], AP_STACKS[3], WORKER_FRAMES[4]
 *   (higher addresses)
 *
 *   0x8000 (TRAMPOLINE_BASE, far below 1 MiB, fixed by the SIPI vector)
 *            <- the AP trampoline blob is *copied* here at runtime, from
 *               wherever it linked above, by `smp_guest.rs`'s
 *               `install_trampoline`, before the first AP's SIPI is sent.
 *               See the trampoline's own comment below for why it is not
 *               simply linked at this address directly.
 *
 * __boot_image_load_start/__boot_image_load_end bound the 1 MiB+ range; the
 * crate-built table's linker-bounded identity mapping in smp_guest.rs covers
 * that range plus TRAMPOLINE_BASE, or the image stops running (for the range
 * above) or every AP dies at boot (for TRAMPOLINE_BASE) when CR3 switches.
 */
.section .bss.boot, "aw", @nobits
.balign 4096
bootstrap_pml4:
    .skip 4096
bootstrap_pdpt:
    .skip 4096
bootstrap_pd:
    .skip 4096

.balign 16
boot_stack:
    .skip 16384
boot_stack_top:

/*
 * AP real-mode trampoline. SIPI loads CS = vector << 8, IP = 0 with every
 * other segment and general register unspecified except DS = 0 (INIT
 * clears DS's base to 0 on the architectures this test targets), so once
 * copied to physical TRAMPOLINE_BASE this code runs at a fixed low
 * physical/linear address with DS still linear from 0: absolute references
 * below are expressed as TRAMPOLINE_BASE plus an intra-blob offset, not as
 * bare symbols. The bare symbols are only this object's *link* addresses
 * (wherever the linker places this small blob within the main image); the
 * BSP copies the blob from there to TRAMPOLINE_BASE at runtime
 * (`smp_guest.rs`'s `install_trampoline`) before ever sending a SIPI, so the
 * addresses these instructions actually need at runtime never depend on
 * where the blob happened to link. The SIPI vector is TRAMPOLINE_BASE / 4 KiB.
 *
 *   link address (~1 MiB+, wherever .text.trampoline lands)
 *   +--------------------------------------------------+
 *   | ap_trampoline_start .. ap_trampoline_end          |
 *   +--------------------------------------------------+
 *                    | install_trampoline() copies these bytes verbatim
 *                    v (once, before the first SIPI)
 *   TRAMPOLINE_BASE (0x8000, physical)
 *   +--------------------------------------------------+
 *   | (same bytes) <- SIPI vector 0x8 sets CS:IP here   |
 *   +--------------------------------------------------+
 */
.set TRAMPOLINE_BASE, 0x8000

.section .text.trampoline, "ax"
.code16
.global ap_trampoline_start
.balign 4096
ap_trampoline_start:
    cli
    cld
    xorw %ax, %ax
    movw %ax, %ds
    movw %ax, %es
    movw %ax, %ss
    lgdtl TRAMPOLINE_BASE + (ap_gdt_pointer - ap_trampoline_start)
    movl %cr0, %eax
    orl $1, %eax
    movl %eax, %cr0
    ljmpl $0x08, $(TRAMPOLINE_BASE + (ap_protected_mode_entry - ap_trampoline_start))

.balign 8
ap_gdt:
    .quad 0
    .quad 0x00cf9a000000ffff /* 0x08: 32-bit flat code */
    .quad 0x00cf92000000ffff /* 0x10: 32-bit/64-bit flat data */
    .quad 0x00af9a000000ffff /* 0x18: 64-bit code */
ap_gdt_end:

ap_gdt_pointer:
    .word ap_gdt_end - ap_gdt - 1
    .long TRAMPOLINE_BASE + (ap_gdt - ap_trampoline_start)

/*
 * Reads AP_ROOT_PA, AP_STACK_TOP and AP_WORKER_ID with plain (non-atomic)
 * loads: the BSP publishes each with a release store strictly before the
 * SIPI that wakes this trampoline, and x86 IPI delivery orders the AP's
 * first fetch after that store, so no fence is needed here. These globals
 * are ordinary statics linked at their normal (non-relocated) addresses:
 * only code and data inside the copied trampoline blob itself needs the
 * TRAMPOLINE_BASE-relative treatment above.
 */
.code32
ap_protected_mode_entry:
    movw $0x10, %ax
    movw %ax, %ds
    movw %ax, %es
    movw %ax, %ss

    movl %cr4, %eax
    orl $(1 << 5), %eax
    movl %eax, %cr4

    movl AP_ROOT_PA, %eax
    movl %eax, %cr3

    movl $0xc0000080, %ecx
    rdmsr
    orl $((1 << 8) | (1 << 11)), %eax
    wrmsr

    movl %cr0, %eax
    orl $0x80000001, %eax
    movl %eax, %cr0

    ljmpl $0x18, $(TRAMPOLINE_BASE + (ap_long_mode_entry - ap_trampoline_start))

.code64
ap_long_mode_entry:
    movw $0x10, %ax
    movw %ax, %ds
    movw %ax, %es
    movw %ax, %ss
    /*
     * These reads and the final jump target ordinary, non-relocated
     * globals/functions, so they must use absolute (not RIP-relative)
     * addressing: RIP here is TRAMPOLINE_BASE-relative, not this object's
     * link address, and only the encodings above (already expressed via
     * TRAMPOLINE_BASE) are safe under that shift.
     */
    movabs $AP_STACK_TOP, %rax
    movq (%rax), %rsp
    movabs $AP_WORKER_ID, %rax
    movq (%rax), %rdi
    xorq %rbp, %rbp
    movabs $ap_main, %rax
    jmp *%rax
ap_trampoline_end:
