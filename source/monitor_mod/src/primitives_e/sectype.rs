use super::*;

verus! {

pub type NoAdditional = ();

impl_secure_type! {NoAdditional, pub type}

crate::macro_const! {
    #[macro_export]

    pub const MAX_LEAK: u64 = 1u64;
}

impl<T> WellFormed for SpecSecType<T, NoAdditional> {
    #[verifier(inline)]
    open spec fn wf(&self) -> bool {
        self.wf_value()
    }
}

impl<T> WellFormed for SecType<T, NoAdditional> {
    #[verifier(inline)]
    open spec fn wf(&self) -> bool {
        self.wf_value()
    }
}

pub trait ToSecSeq {
    spec fn sec_bytes(self) -> SecSeqByte where Self: core::marker::Sized;
}

pub trait FromSecSeq<T> {
    spec fn from_sec_bytes(self) -> T where T: core::marker::Sized, Self: core::marker::Sized;
}

impl<T: VTypeCast<SecSeqByte>> ToSecSeq for T {
    #[verifier(inline)]
    open spec fn sec_bytes(self) -> SecSeqByte {
        VTypeCast::<SecSeqByte>::vspec_cast_to(self)
    }
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_size_from_cast_secbytes_def<T: SpecSize + VTypeCast<SecSeqByte>>(val: T)
    ensures
        T::spec_size_def() == VTypeCast::<SecSeqByte>::vspec_cast_to(val).len(),
{
}

impl<T: ToSecSeq> FromSecSeq<T> for SecSeqByte {
    open spec fn from_sec_bytes(self) -> T {
        choose|v: T| v.sec_bytes() =~~= self
    }
}

impl<T: VTypeCast<SecSeqByte>> VTypeCast<T> for SecSeqByte {
    open spec fn vspec_cast_to(self) -> T {
        self.from_sec_bytes()
    }
}

#[verifier(external_body)]
pub proof fn proof_sectype_cast_eq<T1: VTypeCast<T2>, T2: VTypeCast<T1>, M>(v: SecType<T1, M>)
    requires
        forall|basev: T1|
            VTypeCast::<T1>::vspec_cast_to(VTypeCast::<T2>::vspec_cast_to(basev)) === basev,
    ensures
        VTypeCast::<SecType<T1, M>>::vspec_cast_to(VTypeCast::<SecType<T2, M>>::vspec_cast_to(v))
            === v,
{
}

impl<T> VTypeCast<SecSeqByte> for Option<T> {
    open spec fn vspec_cast_to(self) -> SecSeqByte;
}

impl<T> VTypeCast<SecSeqByte> for Tracked<T> {
    open spec fn vspec_cast_to(self) -> SecSeqByte {
        Seq::empty()
    }
}

} // verus!
