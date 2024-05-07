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
.align 0x1000
ap_entry:
	cld
	cli
	call ap_call
ap_loop:
	jmp ap_loop

.section .bss
.align 8
monitor_data_addr:
.space 8
verismo_end: