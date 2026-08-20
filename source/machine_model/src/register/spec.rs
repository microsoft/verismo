use vstd::prelude::*;

verus! {

/// Value carried by the descriptor-table registers (`IDTR`/`GDTR`).
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct DescriptorTableValue {
    pub limit: u16,
    pub base: u64,
}

// ---------------------------------------------------------------------------
// RFLAGS control/system bits
// ---------------------------------------------------------------------------
/// RFLAGS.TF (Trap Flag), bit 8.
pub const RFLAGS_TF: u64 = 0x100;

/// RFLAGS.IF (Interrupt Enable Flag), bit 9.
pub const RFLAGS_IF: u64 = 0x200;

/// RFLAGS.DF (Direction Flag), bit 10.
pub const RFLAGS_DF: u64 = 0x400;

/// RFLAGS.IOPL (I/O Privilege Level), bits 12-13.
pub const RFLAGS_IOPL: u64 = 0x3000;

/// Bit position of the low bit of RFLAGS.IOPL.
pub const RFLAGS_IOPL_SHIFT: u64 = 12;

/// RFLAGS.NT (Nested Task), bit 14.
pub const RFLAGS_NT: u64 = 0x4000;

/// RFLAGS.RF (Resume Flag), bit 16.
pub const RFLAGS_RF: u64 = 0x1_0000;

/// RFLAGS.VM (Virtual-8086 Mode), bit 17.
pub const RFLAGS_VM: u64 = 0x2_0000;

/// RFLAGS.AC (Alignment Check / Access Control), bit 18.
pub const RFLAGS_AC: u64 = 0x4_0000;

/// RFLAGS.VIF (Virtual Interrupt Flag), bit 19.
pub const RFLAGS_VIF: u64 = 0x8_0000;

/// RFLAGS.VIP (Virtual Interrupt Pending), bit 20.
pub const RFLAGS_VIP: u64 = 0x10_0000;

/// RFLAGS.ID (CPUID-supported Identification), bit 21.
pub const RFLAGS_ID: u64 = 0x20_0000;

/// The persistent control/system portion of RFLAGS.
///
/// The arithmetic/status flags (CF, PF, AF, ZF, SF, OF) are deliberately *not*
/// modeled: they are clobbered by ordinary instructions, so they carry no stable
/// architectural state worth owning as a register token.
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct RflagsControlValue {
    pub trap: bool,
    pub interrupt_enable: bool,
    pub direction: bool,
    pub io_privilege_level: u8,
    pub nested_task: bool,
    pub resume: bool,
    pub virtual_8086: bool,
    pub alignment_check: bool,
    pub virtual_interrupt: bool,
    pub virtual_interrupt_pending: bool,
    pub id: bool,
}

impl RflagsControlValue {
    /// The same control state with `AC` set to `value` and every other field
    /// preserved.
    pub open spec fn with_alignment_check(self, value: bool) -> RflagsControlValue {
        RflagsControlValue { alignment_check: value, ..self }
    }
}

/// Metadata-only contract for a typed register marker: identifies the
/// value type carried by the register.
pub trait RegSpec: Sized {
    type Value;
}

// Fixed (statically-known) register markers. Each is a zero-sized type, so
// there is exactly one instance.
pub struct RflagsControl;

pub struct Rax;

pub struct Rsp;

pub struct Cs;

pub struct Ds;

pub struct Ss;

pub struct Es;

pub struct Gs;

pub struct Cpl;

pub struct Cr0;

pub struct Cr1;

pub struct Cr2;

pub struct Cr3;

pub struct Cr4;

pub struct Xcr0;

pub struct Pkru;

pub struct IdtrBaseLimit;

pub struct GdtrBaseLimit;

/// A model-specific register, identified at runtime by its register
/// number.
pub struct Msr {
    pub register: u32,
}

impl RegSpec for RflagsControl {
    type Value = RflagsControlValue;
}

impl RegSpec for Rax {
    type Value = u64;
}

impl RegSpec for Rsp {
    type Value = u64;
}

impl RegSpec for Cs {
    type Value = u16;
}

impl RegSpec for Ds {
    type Value = u16;
}

impl RegSpec for Ss {
    type Value = u16;
}

impl RegSpec for Es {
    type Value = u16;
}

impl RegSpec for Gs {
    type Value = u16;
}

impl RegSpec for Cpl {
    type Value = u64;
}

impl RegSpec for Cr0 {
    type Value = u64;
}

impl RegSpec for Cr1 {
    type Value = u64;
}

impl RegSpec for Cr2 {
    type Value = u64;
}

impl RegSpec for Cr3 {
    type Value = u64;
}

impl RegSpec for Cr4 {
    type Value = u64;
}

impl RegSpec for Xcr0 {
    type Value = u64;
}

impl RegSpec for Pkru {
    type Value = u32;
}

impl RegSpec for IdtrBaseLimit {
    type Value = DescriptorTableValue;
}

impl RegSpec for GdtrBaseLimit {
    type Value = DescriptorTableValue;
}

impl RegSpec for Msr {
    type Value = u64;
}

} // verus!
