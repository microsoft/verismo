use super::*;

verus! {
    pub open spec fn inv_snp_value<T: IsConstant + WellFormed>(snp: SwSnpMemAttr, val: T) -> bool {
        &&& val.wf()
        &&& !snp.is_confidential_to(1) ==> val.is_constant_to(1)
        &&& !snp.is_confidential_to(2) ==> val.is_constant_to(2)
        &&& !snp.is_confidential_to(3) ==> val.is_constant_to(3)
        &&& !snp.is_confidential_to(4) ==> val.is_constant_to(4)
    }

    impl <V: IsConstant + WellFormed + SpecSize> SnpPPtr<V> {
        #[verifier(external_body)]
        #[verifier(broadcast_forall)]
        pub proof fn axiom_id_equal(&self, other: Self)
        ensures
            (self.id() == other.id()) == (*self === other)
        {}
    }

    impl<V: IsConstant + WellFormed + SpecSize> SnpMemAttrTrait for SnpPointsToData<V> {
        open spec fn snp(&self) -> SwSnpMemAttr {
            self.snp.sw
        }

        open spec fn hw_snp(&self) -> HwSnpMemAttr {
            self.snp.hw
        }
    }

    impl<V: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>>  SnpPointsToData<V> {
        pub open spec fn spec_write_field_rel<F: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>>(self, prev: Self, offset: nat, val: Option<F>) -> bool {
            &&& if let Some(v) = val {
                &&& field_set(prev.get_value(), self.get_value(), offset, v)
                &&& self.value().is_Some()
            } else {
                self.value().is_None()
            }
            &&& self.ptr == prev.ptr
            &&& self.snp() === prev.snp()
            &&& self.wf()
        }
    }

    impl <V: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> VTypeCast<SnpPointsToBytes> for SnpPointsToData<V> {
        open spec fn vspec_cast_to(self) -> SnpPointsToBytes {
            SnpPointsToBytes {
                pptr: self.ptr,
                snp_bytes: self.value().get_Some_0().vspec_cast_to(),
                snp: self.snp
            }
        }
    }

    impl <V: IsConstant + WellFormed + SpecSize> SnpPointsToData<V> {
        pub open spec fn sw_eq(self, rhs: Self) -> bool {
            &&& self.snp() === rhs.snp()
            &&& self.value() === rhs.value()
            &&& self.id() === rhs.id()
        }

        pub open spec fn only_val_updated(self, rhs: Self) -> bool {
            &&& self.snp() === rhs.snp()
            &&& self.id() === rhs.id()
            &&& self.value().is_Some()
            &&& self.wf()
        }

        pub open spec fn spec_write_rel(self, prev: Self, val: Option<V>) -> bool {
            &&& if let Some(v) = val {
                &&& self.value().get_Some_0() === v
                &&& self.value().is_Some()
            } else {
                self.value().is_None()
            }
            &&& self.ptr == prev.ptr
            &&& self.snp() === prev.snp()
            &&& self.hw_snp().hvupdate_rel(prev.hw_snp())
        }

        pub open spec fn spec_read_rel(self, val: V) -> bool {
            &&& self.value().is_Some() && self.hw_snp().is_vmpl0_private() ==> {
                self.value().get_Some_0() === val
            }
            &&& inv_snp_value(self.snp(), val)
            &&& self.snp.valid_access(self.id(), spec_size::<V>(), crate::arch::rmp::perm_s::Perm::Read)
        }
    }

    impl <V: IsConstant + WellFormed + SpecSize> IsConstant for SnpPointsToData<V> {
        open spec fn is_constant_to(&self, vmpl: nat) -> bool {
            self.value.is_Some() && self.value.get_Some_0().is_constant_to(vmpl)
        }

        open spec fn is_constant(&self) -> bool {
            self.value.is_Some() && self.value.get_Some_0().is_constant()
        }
    }

    impl<V: IsConstant + WellFormed + VTypeCast<SecSeqByte> + SpecSize> SnpPointsTo<V> {
        #[verifier(external_body)]
        pub proof fn trusted_into_raw(tracked self) -> (tracked points_to_raw: SnpPointsToRaw)
        requires
            self@.value.is_Some(),
            self@.wf(),
        ensures
            points_to_raw@ === self@.vspec_cast_to(),
            self@ === points_to_raw@.vspec_cast_to(),
            points_to_raw@.wf(),
        {
            unimplemented!{}
        }

        pub proof fn tracked_into_raw(tracked self) -> (tracked points_to_raw: SnpPointsToRaw)
        requires
            self@.value.is_Some(),
            self@.wf(),
        ensures
            points_to_raw@ === self@.vspec_cast_to(),
            self@ === points_to_raw@.vspec_cast_to(),
            points_to_raw@.wf(),
            self@.get_value().is_constant() ==> points_to_raw@.bytes().is_constant(),
            self@.get_value().is_constant_to(1) ==> points_to_raw@.bytes().is_constant_to(1),
            self@.get_value().is_constant_to(1) ==> points_to_raw@.bytes().is_constant_to(1),
            self@.get_value().is_constant_to(1) ==> points_to_raw@.bytes().is_constant_to(1),
            self@.get_value().is_constant_to(1) ==> points_to_raw@.bytes().is_constant_to(1),

        {
            proof_into_is_constant::<V, SecSeqByte>(self@.get_value());
            self.trusted_into_raw()
        }
    }
}
