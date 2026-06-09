.globl boot_stack
.globl boot_stack_end
.globl stack_guard_page
.globl verismo_start
.globl verismo_end
.globl _start
.globl ap_entry
_start:
verismo_start:
	cld
	cli
	mov %rsi, %rdi
	call bsp_call
	mov stack_guard_page(%rip), %rax
	mov $0, %rcx
	mov $0, %rdx
	.byte 0xF2, 0x0F, 0x01, 0xFF
	lea boot_stack_end(%rip), %rsp
	call bsp_call
.align 0x1000
ap_entry:
	cld
	cli
	call ap_call
ap_loop:
	jmp ap_loop

.section .data
.align 0x1000
stack_guard_page:
.space 4096
boot_stack:
.space 4096
.space 4096
.space 4096
.space 4096
boot_stack_end:

.section .bss
.align 8
monitor_data_addr:
.space 8
verismo_end: