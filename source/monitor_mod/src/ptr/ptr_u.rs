use super::*;

verus! {
impl<V: IsConstant + WellFormed + SpecSize> WellFormed for SnpPointsToData<V> {
    open spec fn wf(&self) -> bool {
        &&& self.snp.wf()
        &&& !self.snp().is_pte
        &&& self.value().is_Some() ==> self.wf_value(self.value().get_Some_0())
    }
}

impl<V: IsConstant + WellFormed + SpecSize> SnpPPtr<V> {
    pub open spec fn not_null(&self) -> bool {
        &&& self.id().spec_valid_addr_with(spec_size::<V>())
        &&& self.wf()
    }

    pub open spec fn is_null(&self) -> bool {
        &&& self.wf()
        &&& !self.id().spec_valid_addr_with(spec_size::<V>())
    }
}

impl<V: IsConstant + WellFormed + SpecSize> SnpPointsToData<V> {
    pub open spec fn id(&self) -> int {
        self.ptr
    }

    pub open spec fn range_id(&self) -> (int, nat) {
        (self.ptr, spec_size::<V>())
    }

    pub open spec fn pptr(&self) -> int {
        self.ptr
    }

    /// None if the value is never set or if the memory is hv shared.
    /// If snp.is_vmpl0_private() ==> value() represents the content in mem.
    /// If !snp.is_vmpl0_private() ==> value() is not usable.
    pub open spec fn value(&self) -> Option<V>
    recommends
        self.hw_snp().is_vmpl0_private(),
    {
        self.value
    }

    #[verifier(inline)]
    pub open spec fn get_value(&self) -> V {
        self.value().get_Some_0()
    }

    pub open spec fn is_assigned(&self) -> bool {
        self.snp().is_vmpl0_private() ==> self.value().is_Some()
    }

    pub open spec fn is_valid_private(&self) -> bool {
        &&& self.snp().is_vmpl0_private()
        &&& self.value().is_Some()
    }

    // hv-shared memory only holds non-secret data (guessing space = 1)
    pub open spec fn wf_value(&self, val: V) -> bool {
        &&& (!self.snp().is_vm_confidential() ==> val.is_constant())
        &&& val.wf()
    }

    pub open spec fn wf_at(&self, ptr: int) -> bool {
        &&& self.pptr() === ptr
        &&& self.wf()
    }

    pub open spec fn wf_const_default(&self, ptr: int) -> bool {
        &&& self.wf_not_null_at(ptr)
        &&& self.snp() === SwSnpMemAttr::spec_default()
        &&& self.get_value().is_constant()
        &&& self.value().is_Some()
    }

    pub open spec fn wf_shared(&self, ptr: int) -> bool {
        &&& self.wf_not_null_at(ptr)
        &&& self.snp() === SwSnpMemAttr::shared()
        &&& self.get_value().is_constant()
        &&& self.value().is_Some()
    }


    // wf_pte cannot use SnpPPtr::replace or put.
    pub open spec fn is_wf_pte(&self, ptr: int) -> bool {
        &&& self.snp.wf()
        &&& ptr.spec_valid_addr_with(spec_size::<V>())
        &&& self.pptr() === ptr
        &&& self.snp() === SwSnpMemAttr::spec_default_pte()
        &&& self.get_value().is_constant()
        &&& self.value().is_Some()
        &&& self.wf_value(self.value().get_Some_0())
    }

    pub open spec fn wf_not_null_at(&self, ptr: int) -> bool {
        &&& spec_size::<V>() > 0 ==> ptr.spec_valid_addr_with(spec_size::<V>())
        &&& self.wf_at(ptr)
    }

    #[verifier(inline)]
    pub open spec fn ptr_not_null_wf(&self, ptr: SnpPPtr<V>) -> bool {
        &&& self.wf_not_null_at(ptr.id())
    }

    pub open spec fn ptr_not_null_private_wf(&self, ptr: SnpPPtr<V>) -> bool {
        &&& self.ptr_not_null_wf(ptr)
        &&& self.is_valid_private()
    }

    pub open spec fn ensures_read(self, val: V) -> bool {
        self.snp().ensures_read(self.value(), val)
    }
}
}
