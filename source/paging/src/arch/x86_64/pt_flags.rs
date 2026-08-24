//! x86_64-specific page table entry flags.
#[cfg(not(verus_only))]
use bitflags::bitflags;
#[cfg(verus_only)]
use bitflags_verus::bitflags_verus as bitflags;

use bitflags::Flags;
use bitflags_verus::FlagsSpec;
use builtin_macros::{proof, verus, verus_spec, verus_verify};
use vstd::prelude::*;

use crate::structs::arch_contract::{GenericPageTableFlags, GenericPageTableFlagsSpec};

bitflags! {
    /// x86_64 page table entry flags.
    ///
    /// Bit positions follow the Intel/AMD architecture manuals for
    /// 4-level (PML4) and 5-level (PML5) paging modes.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub struct PTEntryFlags: usize {
        const PRESENT       = 0x1;
        const WRITABLE      = 0x2;
        const USER          = 0x4;
        const WRITE_THROUGH = 0x8;
        const NO_CACHE      = 0x10;
        const ACCESSED      = 0x20;
        const DIRTY         = 0x40;
        const HUGE          = 0x80;
        const GLOBAL        = 0x100;
        const ESCROW        = 0x200;
        const NX            = 0x8000_0000_0000_0000;
    }
}

verus! {

impl GenericPageTableFlagsSpec for PTEntryFlags {
    /// The union of the named flags declared above.
    open spec fn spec_all_bits() -> usize {
        0x8000_0000_0000_03ff
    }

    open spec fn spec_present_bit() -> usize {
        0x1
    }

    open spec fn spec_huge_bit() -> usize {
        0x80
    }

    open spec fn spec_writable_bit() -> usize {
        0x2
    }

    open spec fn spec_user_bit() -> usize {
        0x4
    }

    /// Bit 9, the first of the three the architecture leaves to software in
    /// every entry format.
    open spec fn spec_escrow_bit() -> usize {
        0x200
    }

    fn present_bit() -> (ret: usize) {
        0x1
    }

    fn huge_bit() -> (ret: usize) {
        0x80
    }

    fn writable_bit() -> (ret: usize) {
        0x2
    }

    fn user_bit() -> (ret: usize) {
        0x4
    }

    fn escrow_bit() -> (ret: usize) {
        0x200
    }

    proof fn lemma_flag_bits_wf() {
        broadcast use bitflags_verus::bigflags_axioms;

        assert(1usize & 0x80usize == 0usize) by (bit_vector);
        assert(1usize & 0x8000_0000_0000_03ffusize == 1usize) by (bit_vector);
        assert(0x80usize & 0x8000_0000_0000_03ffusize == 0x80usize) by (bit_vector);
        assert(4usize & 0x8000_0000_0000_03ffusize == 4usize) by (bit_vector);
        assert(0x200usize & 0x1usize == 0usize) by (bit_vector);
        assert(0x200usize & 0x80usize == 0usize) by (bit_vector);
        assert(0x200usize & 0x8000_0000_0000_03ffusize == 0x200usize) by (bit_vector);
        assert(0x2usize & 0x1usize == 0usize) by (bit_vector);
        assert(0x2usize & 0x80usize == 0usize) by (bit_vector);
        assert(0x2usize & 0x200usize == 0usize) by (bit_vector);
        assert(0x2usize & 0x8000_0000_0000_03ffusize == 0x2usize) by (bit_vector);
    }
}

/// Inside `verus!` rather than annotated in place, unlike the rest of the exec
/// code here: Verus verifies a trait impl only as a whole, and an impl outside
/// the macro cannot supply the trait's associated consts.
impl GenericPageTableFlags for PTEntryFlags {
    #[verifier::external_body]
    const PRESENT: Self = Self::PRESENT;

    #[verifier::external_body]
    const WRITABLE: Self = Self::WRITABLE;

    #[verifier::external_body]
    const USER: Self = Self::USER;

    #[verifier::external_body]
    const HUGE: Self = Self::HUGE;

    /// present, writable, user-accessible, and accessed.
    /// ACCESSED & DIRTY => prevent future hardware mutations.
    fn parent_flags() -> Self {
        Self::PRESENT | Self::WRITABLE | Self::USER | Self::ACCESSED | Self::DIRTY
    }

    /// The page table is not accessible by user mode, and is not executable.
    fn self_map_table_flags() -> Self {
        Self::PRESENT | Self::WRITABLE | Self::ACCESSED | Self::DIRTY | Self::NX
    }
}

} // verus!
#[verus_verify]
impl PTEntryFlags {
    #[verus_spec(ret =>
        returns self.contains(Self::WRITABLE)
    )]
    pub fn writable(&self) -> bool {
        self.contains(Self::WRITABLE)
    }

    #[verus_spec(ret =>
        returns self.contains(Self::NX)
    )]
    pub fn nx(&self) -> bool {
        self.contains(Self::NX)
    }

    #[verus_spec(ret =>
        returns self.contains(Self::GLOBAL)
    )]
    pub fn global(&self) -> bool {
        self.contains(Self::GLOBAL)
    }

    pub fn exec() -> Self {
        Self::PRESENT | Self::GLOBAL | Self::ACCESSED
    }

    pub fn data() -> Self {
        Self::PRESENT | Self::GLOBAL | Self::WRITABLE | Self::NX | Self::ACCESSED | Self::DIRTY
    }

    pub fn data_ro() -> Self {
        Self::PRESENT | Self::GLOBAL | Self::NX | Self::ACCESSED
    }

    pub fn task_exec() -> Self {
        Self::PRESENT | Self::ACCESSED
    }

    pub fn task_data() -> Self {
        Self::PRESENT | Self::WRITABLE | Self::NX | Self::ACCESSED | Self::DIRTY
    }

    pub fn task_data_ro() -> Self {
        Self::PRESENT | Self::NX | Self::ACCESSED
    }
}
