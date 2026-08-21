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

/// Access to a single control register (`CR0`/`CR3`/`CR4`).
///
/// Control registers are read and written with `MOV to/from CRn`, which fault with
/// `#GP` outside CPL 0, so both operations take a shared `Cpl` token as typed
/// evidence that the current privilege level is 0.
pub trait ControlReg: FixedRegSpec<Value = u64> {
    /// The value that is architecturally retained after successfully writing
    /// `value` to this register, i.e. the value a subsequent read observes.
    ///
    /// This normalizes bits that do not persist as written: fixed-to-one bits and
    /// write-only control bits.
    spec fn stored_value(&self, value: u64) -> u64;

    /// Read the current value of this control register from its token.
    fn read(
        &self,
        Tracked(cpl): Tracked<&RegisterPointsTo<Cpl>>,
        Tracked(token): Tracked<&RegisterPointsTo<Self>>,
    ) -> (result: u64)
        requires
            cpl.value() == 0,
        ensures
            token.value() == result,
    ;

    /// Write `value` to this control register.
    ///
    /// This models only the value retained after a *successful* write: writing a
    /// reserved, unsupported, or otherwise invalid value (e.g. one that violates a
    /// CPU capability requirement or a fixed-bit constraint) faults with `#GP`.
    /// Complete capability/fixed-bit preconditions are deferred; only the stored-value
    /// normalization is modeled here.
    ///
    /// Note: writing a control register can invalidate `PageTableGlobalState::inv`
    /// (which constrains CR0/CR3/CR4 and the ghost mappings). The invariant is
    /// relative to the register state, so callers holding such a state must
    /// re-establish it after any control-register write before relying on it again.
    fn write(
        &self,
        value: u64,
        Tracked(cpl): Tracked<&RegisterPointsTo<Cpl>>,
        Tracked(token): Tracked<&mut RegisterPointsTo<Self>>,
    )
        requires
            cpl.value() == 0,
        ensures
            final(token).value() == self.stored_value(value),
            final(token).reg() == old(token).reg(),
    ;
}

} // verus!
