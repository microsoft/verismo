use vstd::prelude::*;

verus! {

use super::spec::*;

/// A tracked, thread-affine permission/token representing knowledge of the current
/// value of a single machine register.
///
/// The register is identified statically by the marker type `R`, and the value type
/// is fixed by `R::Value`, so identity/value mismatches are unrepresentable.
///
/// The fields are private to this module and there is no public constructor, so a
/// token cannot be forged anywhere else, not even elsewhere in this crate: instances
/// can only be obtained from whatever trusted external-body operation is responsible
/// for producing them (e.g. modeling the initial machine state), and can only be
/// consumed/updated through external-body exec operations taking
/// `Tracked<&mut RegisterPointsTo<R>>`.
pub tracked struct RegisterPointsTo<R: RegSpec> {
    ghost reg: R,
    ghost value: R::Value,
    // `*mut ()` is neither `Send` nor `Sync`, so this field pins the token to the
    // thread that created it and prevents it from being shared or moved across
    // threads.
    not_send_sync: core::marker::PhantomData<*mut ()>,
}

impl<R: RegSpec> RegisterPointsTo<R> {
    /// The register marker identifying which register this token owns.
    ///
    /// Opaque (`closed`): callers may mention it in invariants, but its body is only
    /// known inside this module, which keeps the fields unforgeable.
    pub closed spec fn reg(&self) -> R {
        self.reg
    }

    /// The current value of the register.
    pub closed spec fn value(&self) -> R::Value {
        self.value
    }
}

} // verus!
