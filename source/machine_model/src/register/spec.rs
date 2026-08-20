use vstd::prelude::*;

verus! {

/// Value carried by the descriptor-table registers (`IDTR`/`GDTR`).
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub ghost struct DescriptorTableValue {
    pub limit: u16,
    pub base: u64,
}

/// Metadata-only contract for a typed register marker: identifies the
/// value type carried by the register and whether two markers denote the
/// same underlying register.
pub trait RegSpec: Sized {
    type Value;

    spec fn same_reg(&self, other: &Self) -> bool;
}

// Fixed (statically-known) register markers. Each is a zero-sized type, so
// there is exactly one instance and `same_reg` is trivially always true.
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
    type Value = u64;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for Rax {
    type Value = u64;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for Rsp {
    type Value = u64;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for Cs {
    type Value = u16;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for Ds {
    type Value = u16;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for Ss {
    type Value = u16;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for Es {
    type Value = u16;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for Gs {
    type Value = u16;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for Cpl {
    type Value = u64;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for Cr0 {
    type Value = u64;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for Cr1 {
    type Value = u64;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for Cr2 {
    type Value = u64;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for Cr3 {
    type Value = u64;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for Cr4 {
    type Value = u64;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for Xcr0 {
    type Value = u64;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for Pkru {
    type Value = u32;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for IdtrBaseLimit {
    type Value = DescriptorTableValue;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for GdtrBaseLimit {
    type Value = DescriptorTableValue;

    open spec fn same_reg(&self, other: &Self) -> bool {
        true
    }
}

impl RegSpec for Msr {
    type Value = u64;

    open spec fn same_reg(&self, other: &Self) -> bool {
        self.register == other.register
    }
}

} // verus!
