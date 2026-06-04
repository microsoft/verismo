// Spec-only `WellFormed`/`IsConstant`/`VTypeCast`/`SpecSize` impls for
// `alloc::vec::Vec`. Moved here from `verismo/src/primitives_e/vec.rs` so the
// orphan rule (both `Vec` and the verus_tspec traits are foreign to verismo)
// is satisfied. The vbox/MutFnTrait-dependent parts stay in verismo.

use alloc::vec::Vec;

use super::*;

verus! {

impl<T: WellFormed> WellFormed for Vec<T> {
    open spec fn wf(&self) -> bool {
        &&& self@.wf()
    }
}

impl<T: IsConstant + WellFormed> IsConstant for Vec<T> {
    open spec fn is_constant(&self) -> bool {
        self@.is_constant()
    }

    open spec fn is_constant_to(&self, vmpl: nat) -> bool {
        &&& self@.is_constant_to(vmpl)
    }
}

impl<T: ToSecSeq> VTypeCast<SecSeqByte> for Vec<T> {
    open spec fn vspec_cast_to(self) -> SecSeqByte {
        self@.vspec_cast_to()
    }
}

impl<T: SpecSize> SpecSize for Vec<T> {
    uninterp spec fn spec_size_def() -> nat;
}

// `IsConstant` for the bare slice type. Moved here from
// `verismo/src/tspec_e/array/array_s.rs` for the same orphan-rule reason as
// the `Vec` impls above.
impl<T: IsConstant + WellFormed> IsConstant for [T] {
    open spec fn is_constant(&self) -> bool {
        self@.is_constant()
    }

    open spec fn is_constant_to(&self, vmpl: nat) -> bool {
        self@.is_constant_to(vmpl)
    }
}

} // verus!
