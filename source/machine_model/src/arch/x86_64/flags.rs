//! Bit-level register values, defined with `bitflags!`.
//!
//! Values are always built with `from_bits_retain`, never `from_bits_truncate`:
//! control registers carry architectural state outside the named flags (CR3's
//! page-table base address, for example), which must not be dropped.
#[cfg(not(verus_only))]
use bitflags::bitflags;
#[cfg(verus_only)]
use bitflags_verus::bitflags_verus as bitflags;

use vstd::prelude::*;

bitflags! {
    /// The RFLAGS image stored by `PUSHFQ`, held verbatim.
    ///
    /// This is the *observable* image rather than the hidden architectural
    /// state: `PUSHFQ` stores `RF` and `VM` as 0 whatever the hardware holds.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub struct RflagsValue: u64 {
        // Status flags, clobbered by ordinary ALU instructions.
        /// Carry.
        const CF = 0x1;
        /// Parity.
        const PF = 0x4;
        /// Auxiliary carry.
        const AF = 0x10;
        /// Zero.
        const ZF = 0x40;
        /// Sign.
        const SF = 0x80;
        /// Overflow.
        const OF = 0x800;

        // Control/system flags.
        /// Trap.
        const TF = 0x100;
        /// Interrupt enable.
        const IF = 0x200;
        /// Direction.
        const DF = 0x400;
        /// I/O privilege level: a two-bit field, not a flag. Read it with
        /// `RflagsValue::io_privilege_level`.
        const IOPL = 0x3000;
        /// Nested task.
        const NT = 0x4000;
        /// Resume. Always stored as 0 by `PUSHFQ`.
        const RF = 0x1_0000;
        /// Virtual-8086 mode. Always stored as 0 by `PUSHFQ`.
        const VM = 0x2_0000;
        /// Alignment check / access control.
        const AC = 0x4_0000;
        /// Virtual interrupt.
        const VIF = 0x8_0000;
        /// Virtual interrupt pending.
        const VIP = 0x10_0000;
        /// CPUID-supported identification.
        const ID = 0x20_0000;
    }
}

bitflags! {
    /// The value held in CR0.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub struct Cr0Value: u64 {
        /// Protection enable.
        const PE = 0x1;
        /// Extension type. Fixed to 1 on every CPU modeled here, so it reads
        /// back set whatever a `MOV to CR0` writes.
        const ET = 0x10;
        /// Write protect.
        const WP = 0x1_0000;
        /// Not write-through.
        const NW = 0x2000_0000;
        /// Cache disable.
        const CD = 0x4000_0000;
        /// Paging enable.
        const PG = 0x8000_0000;
    }
}

bitflags! {
    /// The value held in CR3.
    ///
    /// Outside the named bits, CR3 holds the physical base address of the
    /// top-level paging structure and, when `CR4.PCIDE` is set, a PCID.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub struct Cr3Value: u64 {
        /// Page-level write-through.
        const PWT = 0x8;
        /// Page-level cache disable.
        const PCD = 0x10;
        /// No-flush control. Write-only: consumed by the write itself, so it
        /// never persists and always reads back clear.
        const NOFLUSH = 0x8000_0000_0000_0000;
    }
}

bitflags! {
    /// The value held in CR4.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub struct Cr4Value: u64 {
        /// Physical address extension.
        const PAE = 0x20;
        /// 57-bit linear addresses.
        const LA57 = 0x1000;
        /// Process-context identifiers enable.
        const PCIDE = 0x2_0000;
        /// Supervisor mode execution prevention.
        const SMEP = 0x10_0000;
        /// Supervisor mode access prevention.
        const SMAP = 0x20_0000;
        /// Protection key enable.
        const PKE = 0x40_0000;
    }
}

bitflags! {
    /// The value held in the EFER MSR (`MSR_EFER`).
    ///
    /// MSR tokens carry a raw `u64`, so this is a reading of that value (see
    /// `efer_value`) rather than the token's own value type.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub struct EferValue: u64 {
        /// Long mode enable.
        const LME = 0x100;
        /// Long mode active.
        const LMA = 0x400;
        /// No-execute enable.
        const NXE = 0x800;
    }
}

verus! {

impl RflagsValue {
    pub open spec fn iopl_shift() -> u64 {
        12
    }

    /// The privilege level encoded by the `IOPL` field.
    pub open spec fn io_privilege_level(self) -> u8 {
        ((self@ & RflagsValue::IOPL@) >> RflagsValue::iopl_shift()) as u8
    }

    /// The flags left architecturally undefined by `MOV to/from CRn` and by
    /// ordinary ALU instructions.
    pub open spec fn status_flags() -> RflagsValue {
        RflagsValue::CF.union(RflagsValue::PF).union(RflagsValue::AF).union(RflagsValue::ZF).union(
            RflagsValue::SF,
        ).union(RflagsValue::OF)
    }

    /// Agrees with `other` on every control/system flag, leaving the status
    /// flags unconstrained.
    pub open spec fn same_control_flags(self, other: RflagsValue) -> bool {
        self.difference(RflagsValue::status_flags()) == other.difference(
            RflagsValue::status_flags(),
        )
    }

    pub open spec fn with_alignment_check(self, value: bool) -> RflagsValue {
        if value {
            self.union(RflagsValue::AC)
        } else {
            self.difference(RflagsValue::AC)
        }
    }
}

/// `DF` is a control flag, so it survives anything that only clobbers the status
/// flags.
pub broadcast proof fn lemma_same_control_flags_preserves_df(a: RflagsValue, b: RflagsValue)
    ensures
        #[trigger] a.same_control_flags(b) ==> a.contains(RflagsValue::DF) == b.contains(
            RflagsValue::DF,
        ),
{
    if a.same_control_flags(b) {
        let sa = a@;
        let sb = b@;
        let mask = RflagsValue::status_flags()@;
        assert(mask == 0x1u64 | 0x4u64 | 0x10u64 | 0x40u64 | 0x80u64 | 0x800u64);
        assert(mask == 0x8d5u64) by (bit_vector)
            requires
                mask == 0x1u64 | 0x4u64 | 0x10u64 | 0x40u64 | 0x80u64 | 0x800u64,
        ;
        assert(a.difference(RflagsValue::status_flags())@ == b.difference(
            RflagsValue::status_flags(),
        )@);
        assert(sa & !0x8d5u64 == sb & !0x8d5u64);
        assert((sa & 0x400u64) == (sb & 0x400u64)) by (bit_vector)
            requires
                sa & !0x8d5u64 == sb & !0x8d5u64,
        ;
    }
}

/// `AC` is a control flag, so setting or clearing it leaves `DF` alone.
pub broadcast proof fn lemma_with_alignment_check_preserves_df(a: RflagsValue, set: bool)
    ensures
        #[trigger] a.with_alignment_check(set).contains(RflagsValue::DF) == a.contains(
            RflagsValue::DF,
        ),
{
    let sa = a@;
    if set {
        assert(a.with_alignment_check(set)@ == sa | 0x4_0000u64);
        assert(((sa | 0x4_0000u64) & 0x400u64) == (sa & 0x400u64)) by (bit_vector);
    } else {
        assert(a.with_alignment_check(set)@ == sa & !0x4_0000u64);
        assert(((sa & !0x4_0000u64) & 0x400u64) == (sa & 0x400u64)) by (bit_vector);
    }
}

} // verus!
