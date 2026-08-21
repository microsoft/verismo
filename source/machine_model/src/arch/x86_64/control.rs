// `ControlReg` mentions the crate-private `RegSpec`; see its docs in
// `register::reg_trait`.
#![allow(private_bounds, private_interfaces)]

use vstd::prelude::*;

verus! {

use super::flags::RflagsValue;
use super::spec::{Cpl, Rflags};
use crate::register::points_to::{AsmRegisterPointsTo, RustRegisterPointsTo};
use crate::register::reg_trait::RegSpec;

/// Access to a single control register (`CR0`/`CR3`/`CR4`).
///
/// `MOV to/from CRn` faults with `#GP` outside CPL 0, hence the shared `Cpl`
/// token, and leaves the status flags architecturally undefined, hence the
/// mutable `Rflags` token. Only those flags may change: `IF`, `DF`, `IOPL`,
/// `AC` and the rest survive the write.
pub trait ControlReg: RegSpec {
    /// The value a subsequent read observes after successfully writing `value`,
    /// normalizing bits that do not persist as written (fixed-to-one bits and
    /// write-only control bits).
    spec fn stored_value(&self, value: Self::Value) -> Self::Value;

    /// Trusted: implemented by a single `asm!` block.
    fn asm_read(
        &self,
        Tracked(cpl): Tracked<&AsmRegisterPointsTo<Cpl>>,
        Tracked(rflags): Tracked<&mut AsmRegisterPointsTo<Rflags>>,
        Tracked(token): Tracked<&AsmRegisterPointsTo<Self>>,
    ) -> (result: Self::Value)
        requires
            cpl.value() == 0,
        ensures
            token.value() == result,
            final(rflags).value().same_control_flags(old(rflags).value()),
        no_unwind
    ;

    /// Write `value` to this control register.
    ///
    /// Models only a *successful* write: writing a reserved, unsupported or
    /// otherwise invalid value faults with `#GP`, and those capability/fixed-bit
    /// preconditions are not yet modeled.
    ///
    /// A write can invalidate a downstream paging invariant, which callers must
    /// re-establish before relying on it again.
    /// Trusted: implemented by a single `asm!` block.
    fn asm_write(
        &self,
        value: Self::Value,
        Tracked(cpl): Tracked<&AsmRegisterPointsTo<Cpl>>,
        Tracked(rflags): Tracked<&mut AsmRegisterPointsTo<Rflags>>,
        Tracked(token): Tracked<&mut AsmRegisterPointsTo<Self>>,
    )
        requires
            cpl.value() == 0,
        ensures
            final(token).value() == self.stored_value(value),
            final(rflags).value().same_control_flags(old(rflags).value()),
        no_unwind
    ;
}

} // verus!
