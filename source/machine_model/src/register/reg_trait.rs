use vstd::prelude::*;

verus! {

use super::points_to::*;
use super::spec::*;

/// Read access to a single, statically-identified machine register.
///
/// The marker type is the register identity, so no dynamic identity precondition
/// is needed: a `RegisterPointsTo<Self>` can only own this register.
pub trait ReadableReg: RegSpec {
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
/// operations instead.
pub trait WritableReg: RegSpec {
    /// Write a new value to this register's token.
    fn write(&self, value: Self::Value, Tracked(token): Tracked<&mut RegisterPointsTo<Self>>)
        ensures
            final(token).value() == value,
            final(token).reg() == old(token).reg(),
    ;
}

} // verus!
