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
