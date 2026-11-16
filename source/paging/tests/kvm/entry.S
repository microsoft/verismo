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
 * Bootstrap page tables built below, 2 MiB (huge) leaf entries throughout:
 *
 *   bootstrap_pml4               bootstrap_pdpt            bootstrap_pd
 *   +----------------------+     +----------------------+  +-----------------------+
 *   | [0]     -> pdpt[0]   |     | [0]  -> pd[0..511]    |  | [0]   PA 0x0000_0000  |  2 MiB
 *   | [1..255]   absent    |     | [1..511]   absent     |  | [1]   PA 0x0020_0000  |  2 MiB
 *   | [256]   -> pdpt[0]   |     +----------------------+  | ...                   |
 *   | [257..511] absent    |                                | [511] PA 0x3fe0_0000  |  2 MiB
 *   +----------------------+                                +-----------------------+
 *
 * PML4[0] selects the low 512 GiB, with only VA 0..1 GiB present.
 * PML4[256] selects the high 512 GiB at 0xffff_8000_0000_0000, with only
 * its first 1 GiB present as the high direct-map alias.
 * Both entries point at the SAME bootstrap_pdpt[0], which points at the SAME
 * bootstrap_pd, so VA 0..1 GiB and VA 0xffff_8000_0000_0000..+1 GiB both
 * translate through identical entries to PA 0..1 GiB. Entry word 0x83 =
 * PRESENT (0x1) | WRITABLE (0x2) | HUGE (0x80); bits 31:21 (2 MiB units)
 * carry `%ecx`, and the low 21 PA bits stay zero (2 MiB alignment).
 * This table is temporary: `kmain`/`bsp_main` replace it with a table built
 * by the paging crate before doing anything the crate's contract governs.
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
    callq kmain
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
 * placement is a link detail governed by x86_64-pvh.ld, not a hardware
 * contract). The executable image lives in one PT_LOAD segment starting
 * above the Xen note and is identity-mapped 1:1 by the bootstrap table.
 *
 *   1 MiB -> .note    (separate PT_NOTE containing the Xen PVH entry)
 *            .text    (start of PT_LOAD: pvh_entry, long_mode_entry, kmain, ...)
 *            .rodata  (gdt64, embedded boot-image signature)
 *            .data
 *            .bss.boot (this file, below): bootstrap_pml4/pdpt/pd, boot_stack
 *            .bss (guest.rs): DIRECT_MAP_ARENA.tables[], DIRECT_MAP_ARENA.probe
 *   (higher addresses)
 *
 * __boot_image_load_start/__boot_image_load_end bound this whole range; the
 * 2 MiB identity page `kmain` maps through the crate's own table must cover
 * at least it, or the image stops running the instant CR3 switches away
 * from the bootstrap table above.
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
