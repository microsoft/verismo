use vstd::prelude::*;

verus! {

/// Value carried by the descriptor-table registers (`IDTR`/`GDTR`).
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct DescriptorTableValue {
    pub limit: u16,
    pub base: u64,
}

// ---------------------------------------------------------------------------
// RFLAGS status (arithmetic) bits
// ---------------------------------------------------------------------------
/// RFLAGS.CF (Carry Flag), bit 0.
pub const RFLAGS_CF: u64 = 0x1;

/// RFLAGS.PF (Parity Flag), bit 2.
pub const RFLAGS_PF: u64 = 0x4;

/// RFLAGS.AF (Auxiliary Carry Flag), bit 4.
pub const RFLAGS_AF: u64 = 0x10;

/// RFLAGS.ZF (Zero Flag), bit 6.
pub const RFLAGS_ZF: u64 = 0x40;

/// RFLAGS.SF (Sign Flag), bit 7.
pub const RFLAGS_SF: u64 = 0x80;

/// RFLAGS.OF (Overflow Flag), bit 11.
pub const RFLAGS_OF: u64 = 0x800;

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
///
/// `PUSHFQ` always stores this bit as 0, so it reads as clear in the pushed
/// image regardless of the hidden architectural value.
pub const RFLAGS_RF: u64 = 0x1_0000;

/// RFLAGS.VM (Virtual-8086 Mode), bit 17.
///
/// `PUSHFQ` always stores this bit as 0 as well.
pub const RFLAGS_VM: u64 = 0x2_0000;

/// RFLAGS.AC (Alignment Check / Access Control), bit 18.
pub const RFLAGS_AC: u64 = 0x4_0000;

/// RFLAGS.VIF (Virtual Interrupt Flag), bit 19.
pub const RFLAGS_VIF: u64 = 0x8_0000;

/// RFLAGS.VIP (Virtual Interrupt Pending), bit 20.
pub const RFLAGS_VIP: u64 = 0x10_0000;

/// RFLAGS.ID (CPUID-supported Identification), bit 21.
pub const RFLAGS_ID: u64 = 0x20_0000;

// ---------------------------------------------------------------------------
// CR4 control bits needed by register operations
// ---------------------------------------------------------------------------
/// CR4.SMAP (Supervisor Mode Access Prevention), bit 21.
///
/// Defined here (rather than in the paging module) so that register operations
/// with SMAP-related preconditions can refer to it without a module cycle; the
/// paging module re-exports it.
pub const CR4_SMAP: u64 = 0x20_0000;

// ---------------------------------------------------------------------------
// CR0 bits needed by register operations
// ---------------------------------------------------------------------------
/// CR0.ET (Extension Type), bit 4.
///
/// On all CPUs modeled here this bit is fixed to 1: it reads back as set no
/// matter what value a `MOV to CR0` writes.
pub const CR0_ET: u64 = 0x10;

// ---------------------------------------------------------------------------
// CR3 bits needed by register operations
// ---------------------------------------------------------------------------
/// CR3 bit 63: the `MOV to CR3` "no-flush" control. This is write-only: it is
/// consumed by the write operation itself and never persists as architectural
/// state, so it must always read back as clear. This is documented explicitly
/// even though it is also excluded by the high-bit reserved mask in
/// `cr3_paging_precondition`, since the write-only semantics (rather than mere
/// reservedness) is the reason it must be clear.
///
/// Defined here (rather than in the paging module) so that the control-register
/// write contract can normalize it away without depending on paging; the paging
/// module re-exports it.
pub const CR3_NOFLUSH: u64 = 0x8000_0000_0000_0000;

/// The raw RFLAGS image of the current CPU.
///
/// `bits` is exactly the 64-bit architectural image that `PUSHFQ` stores: no
/// decoding, masking, or per-field projection is applied. In particular, `PUSHFQ`
/// stores `RF` and `VM` as 0 no matter what the hidden architectural values are,
/// so `bits` is the *observable* RFLAGS image, and the `resume()`/`virtual_8086()`
/// queries below report that image rather than a claim about hidden hardware state.
/// The status flags are included even though ordinary instructions clobber them:
/// this value is a plain (untracked) exec value describing the image, not an
/// ownership token, so knowledge of it is refreshed by whatever operation last
/// constrained it.
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct RflagsValue {
    pub bits: u64,
}

impl RflagsValue {
    // -----------------------------------------------------------------------
    // Status (arithmetic) flags: written by ordinary ALU instructions.
    // -----------------------------------------------------------------------
    /// RFLAGS.CF.
    pub open spec fn carry(self) -> bool {
        (self.bits & RFLAGS_CF) != 0
    }

    /// RFLAGS.PF.
    pub open spec fn parity(self) -> bool {
        (self.bits & RFLAGS_PF) != 0
    }

    /// RFLAGS.AF.
    pub open spec fn auxiliary_carry(self) -> bool {
        (self.bits & RFLAGS_AF) != 0
    }

    /// RFLAGS.ZF.
    pub open spec fn zero(self) -> bool {
        (self.bits & RFLAGS_ZF) != 0
    }

    /// RFLAGS.SF.
    pub open spec fn sign(self) -> bool {
        (self.bits & RFLAGS_SF) != 0
    }

    /// RFLAGS.OF.
    pub open spec fn overflow(self) -> bool {
        (self.bits & RFLAGS_OF) != 0
    }

    // -----------------------------------------------------------------------
    // Control/system flags: persistent mode and control state.
    // -----------------------------------------------------------------------
    /// RFLAGS.TF.
    pub open spec fn trap(self) -> bool {
        (self.bits & RFLAGS_TF) != 0
    }

    /// RFLAGS.IF.
    pub open spec fn interrupt_enable(self) -> bool {
        (self.bits & RFLAGS_IF) != 0
    }

    /// RFLAGS.DF.
    pub open spec fn direction(self) -> bool {
        (self.bits & RFLAGS_DF) != 0
    }

    /// RFLAGS.IOPL, as the 2-bit privilege level it encodes.
    pub open spec fn io_privilege_level(self) -> u8 {
        ((self.bits & RFLAGS_IOPL) >> RFLAGS_IOPL_SHIFT) as u8
    }

    /// RFLAGS.NT.
    pub open spec fn nested_task(self) -> bool {
        (self.bits & RFLAGS_NT) != 0
    }

    /// RFLAGS.RF *as it appears in the image*. `PUSHFQ` clears this bit when it
    /// stores the image, so a value obtained from a `PUSHFQ`-based read reports
    /// `false` here even if the hidden architectural RF is set.
    pub open spec fn resume(self) -> bool {
        (self.bits & RFLAGS_RF) != 0
    }

    /// RFLAGS.VM *as it appears in the image*; see `resume` for the same caveat.
    pub open spec fn virtual_8086(self) -> bool {
        (self.bits & RFLAGS_VM) != 0
    }

    /// RFLAGS.AC.
    pub open spec fn alignment_check(self) -> bool {
        (self.bits & RFLAGS_AC) != 0
    }

    /// RFLAGS.VIF.
    pub open spec fn virtual_interrupt(self) -> bool {
        (self.bits & RFLAGS_VIF) != 0
    }

    /// RFLAGS.VIP.
    pub open spec fn virtual_interrupt_pending(self) -> bool {
        (self.bits & RFLAGS_VIP) != 0
    }

    /// RFLAGS.ID.
    pub open spec fn id(self) -> bool {
        (self.bits & RFLAGS_ID) != 0
    }

    /// The same image with `AC` set to `value` and every other bit, status flags
    /// included, preserved exactly.
    pub open spec fn with_alignment_check(self, value: bool) -> RflagsValue {
        RflagsValue {
            bits: if value {
                self.bits | RFLAGS_AC
            } else {
                self.bits & !RFLAGS_AC
            },
        }
    }
}

/// Metadata-only contract for a typed register marker: identifies the
/// value type carried by the register.
pub trait RegSpec: Sized {
    type Value;
}

/// Marker for registers whose identity is *statically* determined by the marker
/// type alone, i.e. every value of the marker type denotes the same architectural
/// register.
///
/// This is deliberately not implemented for `Msr`, whose identity depends on the
/// runtime `register` number: a `&RegisterPointsTo<Msr>` says nothing about *which*
/// MSR is owned, so a generic read/write keyed only on the marker type would let a
/// caller read or write an arbitrary MSR with a token for a different one. Dynamic
/// MSR access therefore needs a separate future API whose contracts match the
/// requested register number against `token.reg().register` explicitly.
pub trait FixedRegSpec: RegSpec {

}

// Fixed (statically-known) register markers. Each is a zero-sized type, so
// there is exactly one instance.
pub struct Rflags;

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

impl RegSpec for Rflags {
    type Value = RflagsValue;
}

impl FixedRegSpec for Rflags {

}

impl RegSpec for Rax {
    type Value = u64;
}

impl FixedRegSpec for Rax {

}

impl RegSpec for Rsp {
    type Value = u64;
}

impl FixedRegSpec for Rsp {

}

impl RegSpec for Cs {
    type Value = u16;
}

impl FixedRegSpec for Cs {

}

impl RegSpec for Ds {
    type Value = u16;
}

impl FixedRegSpec for Ds {

}

impl RegSpec for Ss {
    type Value = u16;
}

impl FixedRegSpec for Ss {

}

impl RegSpec for Es {
    type Value = u16;
}

impl FixedRegSpec for Es {

}

impl RegSpec for Gs {
    type Value = u16;
}

impl FixedRegSpec for Gs {

}

impl RegSpec for Cpl {
    type Value = u64;
}

impl FixedRegSpec for Cpl {

}

impl RegSpec for Cr0 {
    type Value = u64;
}

impl FixedRegSpec for Cr0 {

}

impl RegSpec for Cr1 {
    type Value = u64;
}

impl FixedRegSpec for Cr1 {

}

impl RegSpec for Cr2 {
    type Value = u64;
}

impl FixedRegSpec for Cr2 {

}

impl RegSpec for Cr3 {
    type Value = u64;
}

impl FixedRegSpec for Cr3 {

}

impl RegSpec for Cr4 {
    type Value = u64;
}

impl FixedRegSpec for Cr4 {

}

impl RegSpec for Xcr0 {
    type Value = u64;
}

impl FixedRegSpec for Xcr0 {

}

impl RegSpec for Pkru {
    type Value = u32;
}

impl FixedRegSpec for Pkru {

}

impl RegSpec for IdtrBaseLimit {
    type Value = DescriptorTableValue;
}

impl FixedRegSpec for IdtrBaseLimit {

}

impl RegSpec for GdtrBaseLimit {
    type Value = DescriptorTableValue;
}

impl FixedRegSpec for GdtrBaseLimit {

}

impl RegSpec for Msr {
    type Value = u64;
}

} // verus!
