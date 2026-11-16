use vstd::prelude::*;

verus! {

use super::flags::{Cr0Value, Cr3Value, Cr4Value, RflagsValue};
use crate::register::reg_trait::{sealed::Sealed, RegSpec};

/// Value carried by the descriptor-table registers (`IDTR`/`GDTR`).
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct DescriptorTableValue {
    pub limit: u16,
    pub base: u64,
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

impl Sealed for Rflags {

}

impl Sealed for Rax {

}

impl Sealed for Rsp {

}

impl Sealed for Cs {

}

impl Sealed for Ds {

}

impl Sealed for Ss {

}

impl Sealed for Es {

}

impl Sealed for Gs {

}

impl Sealed for Cr0 {

}

impl Sealed for Cr1 {

}

impl Sealed for Cr2 {

}

impl Sealed for Cr3 {

}

impl Sealed for Cr4 {

}

impl Sealed for Xcr0 {

}

impl Sealed for Pkru {

}

impl Sealed for IdtrBaseLimit {

}

impl Sealed for GdtrBaseLimit {

}

impl Sealed for Msr {

}

impl RegSpec for Rflags {
    type Value = RflagsValue;

    // Compiled Rust assumes DF is clear at every `asm!` boundary; see
    // `asm.rules.x86-df`. The entry stubs establish it with `cld`, since the CPU
    // does not clear DF on interrupt or exception entry.
    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        !value.contains(RflagsValue::DF)
    }
}

impl RegSpec for Rax {
    type Value = u64;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

impl RegSpec for Rsp {
    type Value = u64;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

/// The current privilege level: the low two bits of the `CS` selector.
///
/// APM Vol. 2, "Segment Selectors"; SDM Vol. 3A, "Segment Selectors".
pub open spec fn cpl(cs: u16) -> u16 {
    cs & 3
}

impl RegSpec for Cs {
    type Value = u16;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

impl RegSpec for Ds {
    type Value = u16;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

impl RegSpec for Ss {
    type Value = u16;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

impl RegSpec for Es {
    type Value = u16;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

impl RegSpec for Gs {
    type Value = u16;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

impl RegSpec for Cr0 {
    type Value = Cr0Value;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

impl RegSpec for Cr1 {
    type Value = u64;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

impl RegSpec for Cr2 {
    type Value = u64;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

impl RegSpec for Cr3 {
    type Value = Cr3Value;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

impl RegSpec for Cr4 {
    type Value = Cr4Value;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

impl RegSpec for Xcr0 {
    type Value = u64;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

impl RegSpec for Pkru {
    type Value = u32;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

impl RegSpec for IdtrBaseLimit {
    type Value = DescriptorTableValue;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

impl RegSpec for GdtrBaseLimit {
    type Value = DescriptorTableValue;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

impl RegSpec for Msr {
    type Value = u64;

    open(crate) spec fn rust_abi_wf(value: Self::Value) -> bool {
        true
    }
}

} // verus!
