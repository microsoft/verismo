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
        KEEP(*(.text.boot))
        *(.text .text.*)
    } :load

    .rodata : ALIGN(4K)
    {
        *(.rodata .rodata.*)
    } :load

    .data : ALIGN(4K)
    {
        *(.data .data.*)
    } :load

    .bss : ALIGN(4K)
    {
        *(.bss.boot)
        *(.bss .bss.*)
        *(COMMON)
    } :load

    /DISCARD/ :
    {
        *(.eh_frame .eh_frame_hdr)
        *(.comment)
    }
}
