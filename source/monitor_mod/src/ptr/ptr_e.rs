use super::*;
use crate::global::IsConsole;

verus! {

impl<V: IsConstant + WellFormed + SpecSize> SnpPPtr<V> {
    #[inline(always)]
    #[verifier(external_body)]
    pub const fn from_usize(u: usize_t) -> (p: Self)
        requires
            u.wf(),
        ensures
            p.uptr === u,
            p.wf(),
    {
        SnpPPtr { uptr: u, dummy: Ghost::assume_new() }
    }

    pub const fn nullptr() -> (p: Self)
        ensures
            p.uptr == INVALID_ADDR,
            p.uptr.is_constant(),
            p.wf(),
            p.is_null(),
    {
        Self::from_usize(INVALID_ADDR)
    }

    #[inline(always)]
    pub const fn to_usize(&self) -> (u: usize_t)
        ensures
            u as int == self.id(),
            u === self.uptr,
    {
        self.uptr
    }

    #[inline(always)]
    pub fn as_u64(&self) -> (u: u64_t)
        ensures
            u as int == self.id(),
            u === self.uptr.vspec_cast_to(),
    {
        self.uptr as u64
    }

    pub fn to<V2: IsConstant + WellFormed + SpecSize>(&self) -> (ret: SnpPPtr<V2>)
        ensures
            ret.id() == self.id(),
    {
        SnpPPtr::from_usize(self.to_usize())
    }

    pub fn check_valid(&self) -> (ret: bool)
        requires
            self.is_constant(),
        ensures
            ret === self.not_null(),
    {
        self.uptr.check_valid_addr(size_of::<V>())
    }
}

} // verus!
verus! {

/// SNP safe pointer usage
impl<V: IsConstant + WellFormed + SpecSize> SnpPPtr<V> {
    #[inline(always)]
    pub fn take(&self, Tracked(perm): Tracked<&mut SnpPointsTo<V>>) -> (v: V)
        requires
            old(perm)@.ptr_not_null_wf(*self),
            old(perm)@.value.is_Some(),
        ensures
            perm@.spec_write_rel(old(perm)@, None),
            old(perm)@.ensures_read(v),
            perm@.wf(),
            v.wf(),
    {
        let v = self._take(Tracked(perm));
        proof {
            HwSnpMemAttr::proof_hvupdate_rel_propograte(
                perm@.hw_snp(),
                old(perm)@.hw_snp(),
                old(perm)@.snp(),
            );
        }
        v
    }

    #[inline(always)]
    pub fn put(&self, Tracked(perm): Tracked<&mut SnpPointsTo<V>>, in_v: V)
        requires
            old(perm)@.ptr_not_null_wf(*self),
            old(perm)@.value().is_None(),
            old(perm)@.wf_value(in_v),
            inv_snp_value(old(perm)@.snp(), in_v),
        ensures
            perm@.spec_write_rel(old(perm)@, Some(in_v)),
            perm@.snp.wf(),
            perm@.wf(),
    {
        self._put(Tracked(perm), in_v);
        proof {
            HwSnpMemAttr::proof_hvupdate_rel_propograte(
                perm@.hw_snp(),
                old(perm)@.hw_snp(),
                old(perm)@.snp(),
            );
        }
    }

    /// Swaps the `in_v: V` passed in as an argument with the value in memory.
    #[inline(always)]
    pub fn replace(&self, Tracked(perm): Tracked<&mut SnpPointsTo<V>>, in_v: V) -> (out_v: V)
        requires
            old(perm)@.ptr_not_null_wf(*self),
            old(perm)@.is_assigned(),
            old(perm)@.wf_value(in_v),
        ensures
            perm@.spec_write_rel(old(perm)@, Some(in_v)),
            old(perm)@.ensures_read(out_v),
            perm@.wf(),
    {
        let ret = self._replace(Tracked(perm), in_v);
        proof {
            HwSnpMemAttr::proof_hvupdate_rel_propograte(
                perm@.hw_snp(),
                old(perm)@.hw_snp(),
                old(perm)@.snp(),
            );
        }
        ret
    }

    #[inline(always)]
    pub fn borrow<'a>(&self, Tracked(perm): Tracked<&'a SnpPointsTo<V>>) -> (v: &'a V)
        requires
            perm@.wf_not_null_at(self.id()) || perm@.is_wf_pte(self.id()),
            perm@.value.is_Some(),
            perm@.snp().is_vmpl0_private(),
        ensures
            perm@.ensures_read(*v),
            v.wf(),
    {
        self._borrow(Tracked(perm))
    }
}

impl<F: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte> + Clone> SnpPPtr<F> {
    pub fn copy_with<T2: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>>(
        &self,
        Tracked(perm): Tracked<SnpPointsTo<T2>>,
    ) -> (ret: (F, Tracked<SnpPointsTo<T2>>))
        requires
            perm@.wf_not_null_at(perm@.id()),
            perm@.value.is_Some(),
            inside_range(self.range_id(), perm@.range_id()),
            spec_size::<T2>() > 0,
            spec_size::<F>() > 0,
            self.is_constant(),
        ensures
            perm@.snp().ensures_read(
                Some(field_at(perm@.get_value(), (self.id() - perm@.id()) as nat)),
                ret.0,
            ),
            ret.1@@ === perm@,
    {
        proof {
            reveal(field_at);
        }
        let ghost offset = self.id() - perm@.id();
        let ghost val = perm@.get_value();
        let tracked perm = perm.tracked_into_raw();
        let tracked (left, right) = perm.trusted_split(offset as nat);
        let tracked (fieldp, right) = right.trusted_split(spec_size::<F>());
        assert(fieldp@.bytes() =~~= perm@.bytes().subrange(
            offset as int,
            offset as int + spec_size::<F>(),
        ));
        let tracked fieldp = fieldp.tracked_into();
        let ret = self._copy(Tracked(&fieldp));
        let tracked ret_perm = left.trusted_join(fieldp.tracked_into_raw().trusted_join(right));
        assert(ret_perm@.bytes() =~~= perm@.bytes());
        assert(val.vspec_cast_to() === perm@.bytes());
        assert(val === perm@.bytes().vspec_cast_to());
        (ret, Tracked(ret_perm.tracked_into()))
    }
}

impl<F: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> SnpPPtr<F> {
    #[inline(always)]
    pub fn replace_with<T2: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>>(
        &self,
        in_v: F,
        Tracked(perm): Tracked<SnpPointsTo<T2>>,
    ) -> (ret: (F, Tracked<SnpPointsTo<T2>>))
        requires
            in_v.wf(),
            (!perm@.snp().is_vm_confidential() ==> in_v.is_constant()),
            (perm)@.wf_not_null_at((perm)@.id()),
            (perm)@.value.is_Some(),
            inside_range(self.range_id(), (perm)@.range_id()),
            spec_size::<T2>() > 0,
            spec_size::<F>() > 0,
            self.is_constant(),
        ensures
            ret.1@@.spec_write_field_rel((perm)@, (self.id() - ret.1@@.id()) as nat, Some(in_v)),
            ret.1@@.wf(),
    {
        proof {
            reveal(field_set);
        }
        let ghost offset = self.id() - perm@.id();
        let ghost val = perm@.get_value();
        let tracked perm = perm.tracked_into_raw();
        let ghost old_perm = perm;
        let tracked (left, right) = perm.trusted_split(offset as nat);
        let tracked (fieldp, right) = right.trusted_split(spec_size::<F>());
        assert(fieldp@.bytes() =~~= perm@.bytes().subrange(
            offset as int,
            offset as int + spec_size::<F>(),
        ));
        let tracked mut fieldp = fieldp.tracked_into();
        let ret = self.replace(Tracked(&mut fieldp), in_v);
        let tracked ret_perm = left.trusted_join(fieldp.tracked_into_raw().trusted_join(right));
        proof {
            proof_cast_from_seq_unique(fieldp@.get_value());
            assert(left@.bytes() =~~= old_perm@.bytes().take(offset as int));
            assert(right@.bytes() =~~= old_perm@.bytes().skip(
                offset as int + spec_size::<F>() as int,
            ));
            assert(ret_perm@.bytes() =~~= left@.bytes() + in_v.vspec_cast_to() + right@.bytes());
        }
        (ret, Tracked(ret_perm.tracked_into()))
    }
}

} // verus!
verus! {

impl<T: IsConstant + WellFormed + SpecSize, const N: usize_t> SnpPPtr<Array<T, N>> {
    #[inline(always)]
    pub fn index(&self, i: usize) -> (ret: SnpPPtr<T>)
        requires
            i < N,
            0 < spec_size::<T>() < 0x10000,
            i < 0x10000,
            self.wf(),
            self.not_null(),
        ensures
            ret.id() == self.id() + i * spec_size::<T>(),
            inside_range(ret.range_id(), self.range_id()),
            self.is_constant() ==> ret.is_constant(),
    {
        let unit = size_of::<T>();
        let ghost totalsize = spec_size::<Array<T, N>>();
        proof {
            assert(self.id().spec_valid_addr_with(totalsize));
            Array::<T, N>::reveal_N(N as nat);
            assert(totalsize == N * spec_size::<T>());
            assert(unit == spec_size::<T>());
            assert(i * unit <= N * unit - unit) by (nonlinear_arith)
                requires
                    0 <= i < N,
                    0 < unit,
            ;
            assert(0 <= (i * unit) < MAXU64) by (nonlinear_arith)
                requires
                    0 <= i < 0x10000,
                    0 < unit < 0x10000,
            ;
        }
        let offset: usize = i * unit;
        SnpPPtr::from_usize(self.to_usize() + offset)
    }
}

} // verus!
