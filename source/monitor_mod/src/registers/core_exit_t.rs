use super::*;
use crate::ptr::*;

verus! {

pub open spec fn is_none_or_sharedmem(memperm: Option<SnpPointsToRaw>) -> bool {
    &&& memperm.is_Some() ==> (memperm.get_Some_0()@.snp().is_hv_shared()
        || memperm.get_Some_0()@.size() == 0)
    &&& memperm.is_Some() ==> memperm.get_Some_0()@.wf()
}

pub open spec fn hvupdate_none_or_sharedmem(
    memperm: Option<SnpPointsToRaw>,
    prevmemperm: Option<SnpPointsToRaw>,
) -> bool {
    &&& prevmemperm.is_Some() == memperm.is_Some()
    &&& prevmemperm.is_Some() ==> memperm.get_Some_0()@.spec_write_rel(
        prevmemperm.get_Some_0()@,
        memperm.get_Some_0()@.snp_bytes,
    )
}

} // verus!
verus! {

/// Only shared memory or non-mem is passed.
#[inline(always)]
#[verifier(external_body)]
pub fn vmgexit(
    Tracked(ghcbperm): Tracked<&mut RegisterPerm>,
    Tracked(coreperm): Tracked<&mut CoreIdPerm>,
    Tracked(memperm): Tracked<&mut Option<SnpPointsToRaw>>,
)
    requires
        old(ghcbperm).is_ghcb(),
        is_none_or_sharedmem(*old(memperm)),
    ensures
        coreperm@.spec_vmgexit(
            ghcbperm.view::<u64_s>(),
            *memperm,
            old(coreperm)@,
            old(ghcbperm)@,
            *old(memperm),
        ),
        (ghcbperm).view::<u64_s>().spec_write_value(old(ghcbperm)@, old(ghcbperm)@.value()),
        hvupdate_none_or_sharedmem(*memperm, *old(memperm)),
        ghcbperm.view::<u64_s>().spec_write_value(
            old(ghcbperm).view::<u64_s>(),
            ghcbperm.view::<u64_s>().value,
        ),
{
    unsafe {
        asm!(
            "rep vmmcall",
            options(nostack, preserves_flags),
        );
    }
}

} // verus!
