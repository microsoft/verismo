use vstd::prelude::*;

verus! {

use super::points_to::*;
use super::spec::*;

/// Execution contract for a single, statically-identified machine register.
///
/// The marker type is the register identity, so no dynamic identity precondition
/// is needed: a `RegisterPointsTo<Self>` can only own this register.
pub trait ExecutableReg: RegSpec {
    /// Read the current value of this register from its token.
    fn read(&self, Tracked(token): Tracked<&RegisterPointsTo<Self>>) -> (result: Self::Value)
        ensures
            token.value() == result,
    ;

    /// Write a new value to this register's token.
    fn write(&self, value: Self::Value, Tracked(token): Tracked<&mut RegisterPointsTo<Self>>)
        ensures
            final(token).value() == value,
    ;
}

} // verus!
