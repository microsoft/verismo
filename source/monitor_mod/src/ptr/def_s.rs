use verismo_macro::*;

use super::snp::{SnpMemAttr, SwSnpMemAttr};
use super::*;
use crate::debug::VPrint;

verismo_simple! {
    #[repr(C)]
    #[derive(VPrint, Copy)]
    pub struct SnpPPtr<V: IsConstant + WellFormed + SpecSize> {
        pub uptr: usize_t,
        pub dummy: Ghost<V>,
    }

    pub struct SnpPPtrWithPerm<V: IsConstant + WellFormed + SpecSize> {
        pub ptr: SnpPPtr<V>,
        pub perm: Tracked<SnpPointsTo<V>>,
    }
}

verus! {
    impl<T: IsConstant + WellFormed + SpecSize> SnpPPtrWithPerm<T> {
        pub open spec fn wf(&self) -> bool {
            &&& self.perm@@.wf_at(self.ptr.id())
            &&& self.ptr.not_null()
        }
    }

    impl<V: IsConstant + WellFormed + SpecSize> core::marker::Copy for SnpPPtr<V> {
    }

    impl<V: IsConstant + WellFormed + SpecSize> Clone for SnpPPtr<V> {
        #[verifier(external_body)]
        fn clone(&self) -> (ret: Self)
        ensures *self === ret
        {
            SnpPPtr {
                uptr: self.uptr,
                dummy: self.dummy,
            }
        }
    }

    impl<V: IsConstant + WellFormed + SpecSize> SnpPPtr<V> {
        pub open spec fn id(&self) -> int {
            self.uptr as int
        }

        pub open spec fn range_id(&self) -> (int, nat) {
            (self.id(), spec_size::<V>())
        }
    }
}

verismo_simple! {
    #[verifier(external_body)]
    #[verifier::reject_recursive_types_in_ground_variants(V)]
    pub tracked struct SnpPointsTo<V> {
        phantom: marker::PhantomData<V>,
        no_copy: NoCopy,
    }

    pub trait IsSnpPPtr{}

    /// Represents the meaning of a [`PointsTo`] object.
    #[derive(SpecGetter, SpecSetter)]
    pub ghost struct SnpPointsToData<V: IsConstant + WellFormed + SpecSize> {
        pub ptr: int,
        pub value: Option<V>,
        pub snp: SnpMemAttr,
    }

    impl<V: IsConstant + WellFormed + SpecSize> IsSnpPPtr for SnpPointsToData<V> {}

    pub ghost struct SnpPPtrWithSnp<T: IsConstant + WellFormed + SpecSize> {
        pub ptr: SnpPPtr<T>,
        pub snp: SwSnpMemAttr,
    }

    #[verifier(external_body)]
    pub tracked struct SnpPointsToRaw {
        no_copy: NoCopy,
    }
}

verus! {
    impl<T: IsConstant + WellFormed + SpecSize> SnpPointsTo<T> {
        pub open spec fn view(&self) -> SnpPointsToData<T>;
    }
}
