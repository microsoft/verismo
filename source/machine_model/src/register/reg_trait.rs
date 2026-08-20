use vstd::prelude::*;

verus! {

use super::points_to::*;
use super::spec::*;

/// Read access to a single, statically-identified machine register.
///
/// Restricted to `FixedRegSpec`: the marker type *is* the register identity, so no
/// dynamic identity precondition is needed. Dynamically identified registers such
/// as `Msr` cannot implement this trait; they require a separate future API that
/// matches the requested register number against `token.reg().register`.
pub trait ReadableReg: FixedRegSpec {
    /// Read the current value of this register from its token.
    fn read(&self, Tracked(token): Tracked<&RegisterPointsTo<Self>>) -> (result: Self::Value)
        ensures
            token.value() == result,
    ;
}

/// Write access to a single, statically-identified machine register.
///
/// Registers whose architectural writes have side conditions (e.g. RFLAGS control
/// state) deliberately do not implement this trait; they expose narrower trusted
/// operations instead. As with `ReadableReg`, only `FixedRegSpec` markers qualify,
/// so dynamic MSR writes must go through a separate future API with explicit
/// register-number matching.
pub trait WritableReg: FixedRegSpec {
    /// Write a new value to this register's token.
    fn write(&self, value: Self::Value, Tracked(token): Tracked<&mut RegisterPointsTo<Self>>)
        ensures
            final(token).value() == value,
            final(token).reg() == old(token).reg(),
    ;
}

} // verus!
