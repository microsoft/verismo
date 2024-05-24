use hacl_sys::*;

use super::*;

verismo! {
#[verifier(external_body)]
pub fn trusted_cal_sha512<V: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>>(input: &V, dst: &mut SHA512Type)
requires
    input.wf(),
ensures
    *dst === spec_cal_sha512(input.vspec_cast_to()),
    (*dst).wf(),
    forall |vmpl:nat| 1 <= vmpl <= 4 ==> input.is_constant_to(vmpl) == dst.is_constant_to(vmpl)
{
    unsafe {
        Hacl_SHA3_sha3_512(
            size_of::<V>() as u32,
            input as *const _ as _,
            dst as *mut _ as _,
        )
    }
}
}
