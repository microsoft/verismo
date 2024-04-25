
.macro isr_handler ex:req err=0
.global isr_handler\ex
isr_handler\ex:
.if  \err
.else
    pushq $0 /* Dummy error code for this type */
.endif
    // Push exception code on the stack
    pushq $\ex
    // Ensure 16-byte stack pointer alignment
    // `reserved` in `ExceptionArguments`
    pushq $0x0
    callq dummy_handler_fn

    // We should not return form handle_generic_exception.
    // In case we do, cause a page-fault to ease debugging
    iretq

isr_early.loop\ex:
	hlt
	jmp isr_early.loop\ex
.endm

isr_handler 0
isr_handler 1
isr_handler 2
isr_handler 3
isr_handler 4
isr_handler 5
isr_handler 6
isr_handler 7
isr_handler 8
/* Double-fault is always going to isr_handler_early8 */
isr_handler 9
isr_handler 10,1
isr_handler 11,1
isr_handler 12,1
isr_handler 13,1
isr_handler 14,1
isr_handler 15,1
isr_handler 16
isr_handler 17
isr_handler 18,
/* Machine check is always going to isr_handler_early18 */
isr_handler 19
isr_handler 20
isr_handler 21
// HV
isr_handler 28,1
// VC
isr_handler 29,1

/* Classic PIC interrupts */
isr_handler 32