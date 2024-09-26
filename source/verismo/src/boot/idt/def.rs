use super::*;
use crate::debug::VPrint;

verus! {

pub const IDT_MAX_ENTRIES: usize_t = 256usize as usize_t;

pub const ENTRY_OPTION_MIN: u16_t = 0xe00;

// 0b1110_0000_0000;
pub const ENTRY_MIN_PRE: u16_t = 0x8e00;

//0b1000_1110_0000_0000;
} // verus!
verismo_simple! {
#[repr(C, align(1))]
#[derive(VPrint)]
pub struct InterruptStackFrame {
    pub reserved: u64,
    pub vector: u64,
    pub exception: u64,
    pub rip: u64,
    pub cs: u64,
    pub rflags: u64,
    pub rsp: u64,
    pub ss: u64,
}
pub type EntryOptions = u16;

#[derive(Copy, VClone)]
#[repr(C, align(1))]
pub struct IDTEntry {
    pub pointer_low: u16,
    pub gdt_selector: u16,
    pub options: u16,
    pub pointer_middle: u16,
    pub pointer_high: u32,
    pub reserved: u32,
}

verus! {

pub type InterruptDescriptorTable = Array<IDTEntry, IDT_MAX_ENTRIES>;

} // verus!
verismo_simple!{
    #[repr(C, packed)]
    #[derive(VDefault)]
    pub struct Idtr {
        /// Size of the DT.
        pub limit: u16,
        /// Pointer to the memory region containing the DT.
        pub base: u64,
    }
}

crate::impl_dpr!{
    IdtBaseLimit, Idtr, "idt", IdtrBaseLimit,
}
}
