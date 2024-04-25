use super::*;

verismo! {
    impl<T: WellFormed, const N: IndexType> WellFormed for Array<T, N> {
        open spec fn wf(&self) -> bool {
           self@.wf()
        }
    }

    impl<T: IsConstant + WellFormed> IsConstant for [T] {
        open spec fn is_constant(&self) -> bool {
            self@.is_constant()
        }

        open spec fn is_constant_to(&self, vmpl: nat) -> bool {
            self@.is_constant_to(vmpl)
        }
    }

    impl<T: IsConstant + WellFormed, const N: IndexType> IsConstant for Array<T, N> {
        open spec fn is_constant(&self) -> bool {
            self@.is_constant()
        }

        open spec fn is_constant_to(&self, vmpl: nat) -> bool {
            self@.is_constant_to(vmpl)
        }
    }

    impl<T: ToSecSeq, const N: IndexType> VTypeCast<SecSeqByte> for Array<T, N>
    {
        open spec fn vspec_cast_to(self) -> SecSeqByte {
            self@.vspec_cast_to()
        }
    }

    // Use reveal_N to reveal the size relationship.
    impl<T: SpecSize, const N: IndexType> SpecSize for Array<T, N>
    {
        #[verifier(inline)]
        open spec fn spec_size_def() -> nat {
            (N * T::spec_size_def()) as nat
        }
    }


    impl<T: SpecSize, const N: IndexType> Array<T, N>
    {
        #[verifier(external_body)]
        pub proof fn reveal_N(n: nat)
        requires
            N == n
        ensures
            spec_size::<Array<T, N>>() ==  n * T::spec_size_def(),
            spec_size::<Array<T, N>>() ==  N * T::spec_size_def()
        {}
    }
}
