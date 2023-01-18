use super::*;

verismo! {
    /// SNP safe pointer usage
    impl<V: IsConstant + WellFormed + SpecSize> SnpPPtr<V> {
        /// Moves `v` out of the location pointed to by the pointer `self`
        /// and returns it.
        /// Requires the memory to be initialized, and leaves it uninitialized.
        ///
        /// In the ghost perspective, this updates `perm.value`
        /// from `Some(v)` to `None`,
        /// while returning the `v` as an `exec` value.
        #[inline(always)]
        #[verifier(external_body)]
        pub fn _take(&self, Tracked(perm): Tracked<&mut SnpPointsTo<V>>) -> (v: V)
            requires
                old(perm)@.ptr_not_null_wf(*self),
                old(perm)@.value.is_Some(),
            ensures
                perm@.spec_write_rel(old(perm)@, None),
                old(perm)@.spec_read_rel(v),
        {
            unsafe {
                let mut m = MaybeUninit::uninit();
                mem::swap(&mut m, &mut *(self.uptr as *mut MaybeUninit<V>));
                m.assume_init()
            }
        }

        #[inline(always)]
        #[verifier(external_body)]
        pub fn _put(&self, Tracked(perm): Tracked<&mut SnpPointsTo<V>>, in_v: V)
            requires
                old(perm)@.ptr_not_null_wf(*self),
                old(perm)@.value().is_None(),
            ensures
                perm@.spec_write_rel(old(perm)@, Some(in_v)),
        {
            unsafe {
                *(self.uptr as *mut MaybeUninit<V>) = MaybeUninit::new(in_v);
            }
        }

        /// Swaps the `in_v: V` passed in as an argument with the value in memory.
        #[inline(always)]
        #[verifier(external_body)]
        pub fn _replace(&self, Tracked(perm): Tracked<&mut SnpPointsTo<V>>, in_v: V) -> (out_v: V)
            requires
                old(perm)@.ptr_not_null_wf(*self),
                old(perm)@.is_assigned(),
            ensures
                perm@.spec_write_rel(old(perm)@, Some(in_v)),
                old(perm)@.spec_read_rel(out_v),
            opens_invariants none
        {
            unsafe {
                let mut m = MaybeUninit::new(in_v);
                mem::swap(&mut m, &mut *(self.uptr as *mut MaybeUninit<V>));
                m.assume_init()
            }
        }

        /// Given a shared borrow of the `PointsTo<V>`, obtain a shared borrow of `V`.
        // Note that `self` is just a pointer, so it doesn't need to outlive
        // the returned borrow.
        // A non-private mem should not be borrowed since its value can change anytime
        #[inline(always)]
        #[verifier(external_body)]
        pub fn _borrow<'a>(&self, Tracked(perm): Tracked<&'a SnpPointsTo<V>>) -> (v: &'a V)
            requires
                perm@.wf_not_null_at(self.id()) || perm@.is_wf_pte(self.id()),
                perm@.value.is_Some(),
                perm@.snp().is_vmpl0_private()
            ensures
                perm@.spec_read_rel(*v),
        {
            unsafe {
                (*(self.uptr as *mut MaybeUninit<V>)).assume_init_ref()
            }
        }
    }

    impl<V: IsConstant + WellFormed + SpecSize + Clone> SnpPPtr<V> {
        #[inline(always)]
        #[verifier(external_body)]
        pub fn _copy<'a>(&self, Tracked(perm): Tracked<&'a SnpPointsTo<V>>) -> (v: V)
            requires
                perm@.wf_not_null_at(self.id()) || perm@.is_wf_pte(self.id()),
                perm@.value.is_Some(),
            ensures
                perm@.spec_read_rel(v),
        {
            unsafe {
                (*(self.uptr as *mut V)).clone()
            }
        }
    }
}
