// `RegSpec` is sealed by a crate-private supertrait; see its docs.
#![allow(private_bounds, private_interfaces)]

use vstd::prelude::*;

verus! {

/// Crate-private supertrait that seals `RegSpec`: downstream crates cannot name
/// it, so they cannot add a register marker.
pub(crate) mod sealed {
    pub trait Sealed {

    }

}

use super::points_to::{AsmRegisterPointsTo, RustRegisterPointsTo};

/// Metadata-only contract for a typed register marker: identifies the value type
/// carried by the register.
///
/// Sealed so that the register model stays inside this crate's trusted base: no
/// downstream crate can add a marker, which in turn seals every trait bounded by
/// it (`ReadableReg`, `ControlReg`).
pub trait RegSpec: sealed::Sealed + Sized {
    type Value;

    /// The part of this register's value that compiled Rust code is entitled to
    /// assume, and that every operation must therefore preserve. Defined per
    /// target in `crate::arch`.
    spec fn rust_abi_wf(value: Self::Value) -> bool;
}

/// Read access to a single machine register whose identity is the marker type
/// itself, so no dynamic identity precondition is needed.
///
/// Not implementable for `Msr`, whose identity depends on the runtime `register`
/// number; see `Msr::read`.
pub trait ReadableReg: RegSpec {
    /// Trusted: implemented by a single `asm!` block.
    fn asm_read(&self, Tracked(token): Tracked<&AsmRegisterPointsTo<Self>>) -> (result: Self::Value)
        ensures
            token.value() == result,
    ;

    fn read(&self, Tracked(token): Tracked<&RustRegisterPointsTo<Self>>) -> (result: Self::Value)
        ensures
            token.value() == result,
    {
        self.asm_read(Tracked(&token.asm))
    }
}

} // verus!
