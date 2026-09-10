//! x86_64-specific page table entry flags.
use bitflags::bitflags;

use crate::structs::arch_contract::GenericPageTableFlags;

bitflags! {
    /// x86_64 page table entry flags. Bit positions follow the Intel/AMD
    /// architecture manuals for 4-level (PML4) and 5-level (PML5) paging.
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
        const NX            = 0x8000_0000_0000_0000;
    }
}

impl GenericPageTableFlags for PTEntryFlags {
    const PRESENT: Self = Self::PRESENT;

    const WRITABLE: Self = Self::WRITABLE;

    const USER: Self = Self::USER;

    const HUGE: Self = Self::HUGE;

    /// Present, writable, user-accessible, and already accessed and dirty, so
    /// that the hardware never needs to write the entry back.
    fn parent_flags() -> Self {
        Self::PRESENT | Self::WRITABLE | Self::USER | Self::ACCESSED | Self::DIRTY
    }

    /// The page table is not accessible by user mode, and is not executable.
    fn self_map_table_flags() -> Self {
        Self::PRESENT | Self::WRITABLE | Self::ACCESSED | Self::DIRTY | Self::NX
    }
}

impl PTEntryFlags {
    pub fn writable(&self) -> bool {
        self.contains(Self::WRITABLE)
    }

    pub fn nx(&self) -> bool {
        self.contains(Self::NX)
    }

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
