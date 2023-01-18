use super::*;
use crate::*;
verus! {
    #[derive(SpecSetter, SpecGetter)]
    pub ghost struct SnpPointsToBytes {
        pub pptr: int,
        pub snp_bytes: SecSeqByte,
        pub snp: SnpMemAttr,
    }

    impl IsSnpPPtr for SnpPointsToBytes {}

    impl SnpPointsToRaw {
        pub open spec fn view(&self) -> SnpPointsToBytes;
    }

    impl SnpPointsToBytes{
        #[verifier(external_body)]
        #[verifier(broadcast_forall)]
        proof fn axiom_map_ext_equal(self, other: Self)
        ensures
            #[trigger](self =~= other) == (self.bytes() =~~= other.bytes() && self.snp() === other.snp() && self.range() === other.range())
        {}

        #[verifier(external_body)]
        #[verifier(broadcast_forall)]
        proof fn axiom_map_ext_equal_deep(self, other: Self)
        ensures
            #[trigger](self =~~= other) == (self.bytes() =~~= other.bytes() && self.snp === other.snp && self.range() === other.range())
        {}

        #[verifier(inline)]
        pub open spec fn sw_eq(self, rhs: Self) -> bool {
            &&& self.snp() === rhs.snp()
            &&& self.bytes() =~~= rhs.bytes()
            &&& self.range() === rhs.range()
        }

        pub open spec fn only_val_updated(self, rhs: Self) -> bool {
            &&& self.snp() === rhs.snp()
            &&& self.range() === rhs.range()
            &&& rhs.wf() ==> self.wf()
        }

        pub open spec fn size(&self) -> nat {
            self.snp_bytes.len()
        }

        pub open spec fn range(&self) -> (int, nat) {
            (self.pptr, self.size())
        }

        pub open spec fn is_assign_with(&self, val: SecSeqByte) -> bool {
            self.snp().is_vmpl0_private() ==> self.bytes() =~~= val
        }

        pub open spec fn wf_range(&self, range: (int, nat)) -> bool {
            &&& self.range() == range
            &&& self.wf()
        }

        pub open spec fn snp_wf_range(&self, range: (int, nat)) -> bool {
            &&& self.range() == range
            &&& self.snp.wf()
        }

        pub open spec fn wf_const_default(&self, range: (int, nat)) -> bool {
            &&& self.wf_not_null(range)
            &&& self.snp() === SwSnpMemAttr::spec_default()
            &&& self.bytes().is_constant()
        }

        pub open spec fn wf_shared(&self, range: (int, nat)) -> bool {
            &&& self.wf_not_null(range)
            &&& self.snp() === SwSnpMemAttr::shared()
            &&& self.bytes().is_constant()
        }

        pub open spec fn wf_default(&self, range: (int, nat)) -> bool {
            &&& self.wf_not_null(range)
            &&& self.snp() === SwSnpMemAttr::spec_default()
        }

        pub open spec fn wf_secret_default(&self, range: (int, nat)) -> bool {
            &&& self.wf_range(range)
            &&& self.snp() === SwSnpMemAttr::spec_default()
            &&& self.bytes().is_fullsecret()
            &&& range.0.spec_valid_addr_with(range.1)
        }

        pub open spec fn wf_not_null(&self, range: (int, nat)) -> bool {
            &&& range.0.spec_valid_addr_with(range.1)
            &&& self.wf_range(range)
        }

        pub open spec fn wf_freemem(&self, range: (int, nat)) -> bool {
            &&& self.wf_const_default(range)
        }

        pub open spec fn ptr_not_null_wf(&self, addr: int, len: nat) -> bool {
            &&& self.wf_not_null((addr, len))
        }

        pub open spec fn snp_wf_not_null_range(&self, range: (int, nat)) -> bool {
            &&& range.0.spec_valid_addr_with(range.1)
            &&& self.range() == range
            &&& self.snp.wf()
        }

        pub open spec fn ptr_validated_low(&self, addr: int, len: nat) -> bool {
            &&& self.wf_not_null((addr, len))
            &&& self.snp() === SwSnpMemAttr::spec_default()
        }

        pub open spec fn wf(&self) -> bool {
            &&& self.snp.wf()
            &&& inv_snp_value(self.snp(), self.bytes())
        }

        pub open spec fn inv_snp_value(&self) -> bool {
            inv_snp_value(self.snp(), self.bytes())
        }

        pub open spec fn bytes(&self) -> SecSeqByte
        recommends
            self.snp().is_vmpl0_private(),
        {
            self.snp_bytes
        }

        pub open spec fn spec_write_rel(self, prev: Self, bytes: SecSeqByte) -> bool {
            &&& self.snp_bytes === bytes // equal value without memattr
            &&& self.snp_bytes.is_constant() == prev.snp_bytes.is_constant()
            &&& self.range() === prev.range()
            &&& self.snp == prev.snp
            &&& self.wf()
        }

        pub open spec fn value<T: VTypeCast<SecSeqByte>>(&self) -> T {
            self.snp_bytes.vspec_cast_to()
        }

        pub open spec fn ppage(&self) -> int {
            self.snp().guestmap[self.range().0.to_page()]
        }
    }

    impl <T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> VTypeCast<SnpPointsToData<T>> for SnpPointsToBytes {
        open spec fn vspec_cast_to(self) -> SnpPointsToData<T> {
            SnpPointsToData {
                ptr: self.pptr,
                value: Some(self.snp_bytes.vspec_cast_to()),
                snp: self.snp,
            }
        }
    }

    impl SnpPointsToRaw {
        #[verifier(external_body)]
        pub proof fn tracked_empty(ptr: int, snp: SwSnpMemAttr) -> (tracked ret: SnpPointsToRaw)
        ensures
            ret@.snp() === snp,
            ret@.range() === (ptr, 0),
            ret@.wf(),
        {
            unimplemented!{}
        }
        // spec_size must be equal to byte.size(), otherwise, some axiom related to vpsec_cast_to may not hold.
        #[verifier(external_body)]
        pub proof fn trusted_into<V: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>>(tracked self) -> (tracked points_to: SnpPointsTo<V>)
        requires
            self@.wf(),
            spec_size::<V>() == self@.size(),
        ensures
            points_to@ === self@.vspec_cast_to(),
            self@ === points_to@.vspec_cast_to(),
            points_to@.wf(),
        {
            unimplemented!{}
        }

        pub proof fn tracked_into<V: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>>(tracked self) -> (tracked points_to: SnpPointsTo<V>)
        requires
            self@.wf(),
            spec_size::<V>() == self@.size(),
        ensures
            points_to@ === self@.vspec_cast_to(),
            self@ === points_to@.vspec_cast_to(),
            points_to@.wf(),
            self@.bytes().is_constant() ==> points_to@.get_value().is_constant(),
        {
            proof_into_is_constant::<SecSeqByte, V>(self@.bytes());
            proof_into_is_constant_to::<SecSeqByte, V>(self@.bytes(), 1);
            proof_into_is_constant_to::<SecSeqByte, V>(self@.bytes(), 2);
            proof_into_is_constant_to::<SecSeqByte, V>(self@.bytes(), 3);
            proof_into_is_constant_to::<SecSeqByte, V>(self@.bytes(), 4);
            self.trusted_into()
        }

        #[verifier(external_body)]
        pub proof fn trusted_split(tracked self, len1: nat) -> (tracked res: (Self, Self))
        requires
            self@.snp.wf(),
            len1 <= self@.size(),
            self@.size() > 0,
        ensures
            res.0@.snp_wf_range((self@.pptr, len1)),
            res.1@.snp_wf_range((self@.pptr + len1 as int, (self@.size() - len1) as nat)),
            self@.snp === res.0@.snp,
            self@.snp === res.1@.snp,
            res.0@.bytes() =~~= self@.bytes().take(len1 as int),
            res.1@.bytes() =~~= self@.bytes().skip(len1 as int),
        {
            unimplemented!{}
        }

        pub proof fn tracked_split(tracked self, len1: nat) -> (tracked res: (Self, Self))
        requires
            self@.snp.wf(),
            len1 <= self@.size(),
            self@.size() > 0,
        ensures
            res.0@.snp_wf_range((self@.pptr, len1)),
            res.1@.snp_wf_range((self@.pptr + len1 as int, (self@.size() - len1) as nat)),
            self@.snp === res.0@.snp,
            self@.snp === res.1@.snp,
            res.0@.bytes() =~~= self@.bytes().take(len1 as int),
            res.1@.bytes() =~~= self@.bytes().skip(len1 as int),
            (res.0@.bytes().is_constant_to(1) && res.1@.bytes().is_constant_to(1)) <==> self@.bytes().is_constant_to(1),
            (res.0@.bytes().is_constant_to(2) && res.1@.bytes().is_constant_to(2)) <==> self@.bytes().is_constant_to(2),
            (res.0@.bytes().is_constant_to(3) && res.1@.bytes().is_constant_to(3)) <==> self@.bytes().is_constant_to(3),
            (res.0@.bytes().is_constant_to(4) && res.1@.bytes().is_constant_to(4)) <==> self@.bytes().is_constant_to(4),
        {
            let tracked ret = self.trusted_split(len1);
            assert(self@.bytes() =~~= ret.0@.bytes() + ret.1@.bytes());
            proof_bytes_add_is_constant_to(ret.0@.bytes(), ret.1@.bytes(), 1);
            proof_bytes_add_is_constant_to(ret.0@.bytes(), ret.1@.bytes(), 2);
            proof_bytes_add_is_constant_to(ret.0@.bytes(), ret.1@.bytes(), 3);
            proof_bytes_add_is_constant_to(ret.0@.bytes(), ret.1@.bytes(), 4);

            ret
        }

        #[verifier(external_body)]
        pub proof fn trusted_join(tracked self, tracked other: Self) -> (tracked res: Self)
        requires
            self@.range().end() == other@.range().0,
            self@.snp() === other@.snp(),
            self@.snp.wf(),
            other@.snp.wf(),
        ensures
            res@.pptr === self@.pptr,
            res@.snp === self@.snp,
            res@.size() == self@.size() + other@.size(),
            res@.snp.wf(),
            res@.bytes() =~~= self@.bytes() + other@.bytes(),
        {
            unimplemented!{}
        }

        pub proof fn tracked_join(tracked self, tracked other: Self) -> (tracked res: Self)
        requires
            self@.range().end() == other@.range().0,
            self@.snp() === other@.snp(),
            self@.snp.wf(),
            other@.snp.wf(),
        ensures
            res@.pptr === self@.pptr,
            res@.snp === self@.snp,
            res@.size() == self@.size() + other@.size(),
            res@.snp.wf(),
            res@.bytes() =~~= self@.bytes() + other@.bytes(),
            (self@.bytes().is_constant_to(1) && other@.bytes().is_constant_to(1)) == res@.bytes().is_constant_to(1),
            (self@.bytes().is_constant_to(2) && other@.bytes().is_constant_to(2)) == res@.bytes().is_constant_to(2),
            (self@.bytes().is_constant_to(3) && other@.bytes().is_constant_to(3)) == res@.bytes().is_constant_to(3),
            (self@.bytes().is_constant_to(4) && other@.bytes().is_constant_to(4)) == res@.bytes().is_constant_to(4),

        {
            let tracked ret  = self.trusted_join(other);
            proof_bytes_add_is_constant_to(self@.bytes(), other@.bytes(), 1);
            proof_bytes_add_is_constant_to(self@.bytes(), other@.bytes(), 2);
            proof_bytes_add_is_constant_to(self@.bytes(), other@.bytes(), 3);
            proof_bytes_add_is_constant_to(self@.bytes(), other@.bytes(), 4);
            ret
        }

        #[verifier(external_body)]
        pub proof fn tracked_to_pages(tracked self) -> (tracked s: Map<int, Self>)
        requires
            self@.range().0 % PAGE_SIZE!() == 0,
            (self@.size() as int) % PAGE_SIZE!() == 0,
            self@.wf(),
        ensures
            forall |i| self@.range().0/PAGE_SIZE!() <= i < self@.range().end()/PAGE_SIZE!() ==>
                #[trigger]s.contains_key(i) &&
                s[i]@.snp() === self@.snp() &&
                s[i]@.wf_range((i.to_addr(), PAGE_SIZE as nat)) &&
                s[i]@.bytes() =~~= self@.bytes().subrange(
                    i.to_addr() - self@.range().0, i.to_addr() - self@.range().0 + PAGE_SIZE as int),
        {
            unimplemented!{}
        }

        pub open spec fn wf_seq_perms(s: Map<int, Self>, i: int) -> bool {
            &&& s[i]@.wf()
            &&& s.contains_key(i)
            &&& i > 0 ==> s[i]@.range().0 == s[i-1]@.range().end()
        }

        pub open spec fn merge_perm_ensures(s: Map<int, Self>, n: nat, res: Self) -> bool {
            &&& res@.wf()
            &&& res@.range().0 == s[0]@.range().0
            &&& res@.range().end() == s[n - 1]@.range().end()
            &&& res@.snp() === s[0]@.snp()
        }

        /*
        pub proof fn tracked_joins(tracked s: Map<int, Self>, n: nat) -> (tracked merged: Self)
        requires
            forall |i: int| 0 <= i < n ==> Self::wf_seq_perms(s, i),
            forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==> s[i]@.snp() === s[j]@.snp(),
            n >= 1,
        ensures
            Self::merge_perm_ensures(s, n, merged)
        decreases
            n
        {
            let ghost olds = s;
            let tracked mut s = s;
            assert(Self::wf_seq_perms(s, n - 1));
            if n > 1 {
                assert(Self::wf_seq_perms(s, n - 2));
                let tracked last = s.tracked_remove(n - 1);
                assert forall |i: int| 0 <= i < (n - 1)
                implies Self::wf_seq_perms(s, i) by {
                    assert(Self::wf_seq_perms(olds, i));
                    assert(olds[i] === s[i]);
                    if i > 0 {
                        assert(Self::wf_seq_perms(olds, i - 1));
                        assert(olds[i - 1] === s[i - 1]);
                    }
                }
                let tracked prev = Self::tracked_joins(s, (n - 1) as nat);
                prev.trusted_join(last)
            } else {
                assert(Self::wf_seq_perms(s, 0));
                let tracked ret = s.tracked_remove(0);
                Self::merge_perm_ensures(olds, n, ret);
                ret
            }
        }*/

        pub proof fn tracked_splits(tracked self, offsets: Seq<nat>) -> (tracked s: Map<int, Self>)
        requires
            offsets[0] == 0,
            forall |i: int| 0 <= i < offsets.len() ==> offsets[i] < self@.size(),
            forall |i, j| 0 <= i < offsets.len() && 0 <= j < offsets.len()
                ==> offsets[i] < offsets[j],
            offsets.len() > 0,
        ensures
            forall |i: int| 0 <= i < offsets.len() ==> Self::wf_seq_perms(s, i),
            forall |i: int| 0 <= i < offsets.len() ==> s[i]@.range().0 == offsets[i],
            Self::merge_perm_ensures(s, offsets.len(), self)
        decreases
            offsets.len()
        {
            if offsets.len() == 0 {
                let tracked mut ret = Map::tracked_empty();
                ret.tracked_insert(0, self);
                ret
            } else {
                let tracked (left, last) = self.trusted_split(offsets.last());
                let tracked mut ret = left.tracked_splits(offsets.take((offsets.len() - 1)));
                ret.tracked_insert(offsets.len() as int, last);
                ret
            }
        }
    }

    impl SnpMemAttrTrait for SnpPointsToBytes {
        open spec fn snp(&self) -> SwSnpMemAttr {
            self.snp.sw
                .spec_set_rmpmap(Map::empty())
                .spec_set_sysmap(Map::empty())
        }

        open spec fn hw_snp(&self) -> HwSnpMemAttr {
            self.snp.hw
        }
    }

    pub open spec fn wf_page_range(page_perms: Map<int, SnpPointsToRaw>, start_page: int, npages: nat) -> bool {
        forall |i| start_page <= i < (start_page + npages) ==>
            #[trigger]page_perms.contains_key(i) &&
            page_perms[i]@.wf_range((i.to_addr(), PAGE_SIZE as nat))
    }

}
