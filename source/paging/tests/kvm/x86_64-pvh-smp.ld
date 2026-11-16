ENTRY(pvh_entry)

PHDRS
{
    note PT_NOTE FLAGS(4);
    load PT_LOAD FLAGS(7);
}

SECTIONS
{
    . = 1M;

    .note : ALIGN(4)
    {
        KEEP(*(.note.Xen))
    } :note

    .text : ALIGN(4K)
    {
        __boot_image_load_start = .;
        __boot_image_content_start = .;
        KEEP(*(.text.boot))
        *(.text .text.*)
        /*
         * The AP trampoline links here, at its ordinary contiguous address,
         * like any other code: it is never executed in place. The BSP
         * copies it verbatim to the fixed low physical scratch address SIPI
         * requires (`smp_guest.rs`'s `install_trampoline`) before starting
         * any AP. Its own code computes addresses relative to that fixed
         * base (see `entry-smp.S`), so this section needs no special
         * linker placement of its own.
         */
        KEEP(*(.text.trampoline))
    } :load

    .rodata : ALIGN(4K)
    {
        *(.rodata .rodata.*)
        __boot_image_content_end = .;
    } :load

    .data : ALIGN(4K)
    {
        *(.data .data.*)
        *(.got .got.*)
    } :load

    .bss : ALIGN(4K)
    {
        *(.bss.boot)
        *(.bss .bss.*)
        *(COMMON)
        . = ALIGN(4K);
        __boot_image_load_end = .;
    } :load

    /DISCARD/ :
    {
        *(.eh_frame .eh_frame_hdr)
        *(.comment)
    }
}
