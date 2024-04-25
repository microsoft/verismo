use core::arch::asm;

use super::*;
use crate::registers::{CoreIdPerm, SnpCore};

verus! {

// PVALIDATE and RMPADJUST related
/// 0
pub const RMP_4K: u64 = 0;

/// 1
pub const RMP_2M: u64 = 1;

pub const RMP_READ: u8 = 1;

pub const RMP_WRITE: u8 = 2;

pub const RMP_USER_EXE: u8 = 4;

pub const RMP_KERN_EXE: u8 = 8;

pub const RMP_NO_WRITE: u8 = RMP_READ | RMP_USER_EXE | RMP_KERN_EXE;

pub const RMP_RWX: u8 = RMP_NO_WRITE | RMP_WRITE;

} // verus!
verus! {

// After validation, SPA may change and thus, software-tracked value will not be retained anymore.
// The actual value could be any value including secret values.
#[verifier(external_body)]
pub fn pvalidate(
    vaddr: u64,
    psize: u64,
    validate: u64,
    rflags: &mut u64,
    Tracked(mycore): Tracked<&SnpCore>,
    Tracked(perm): Tracked<&mut SnpPointsToRaw>,
) -> (ret: u64)
    requires
        old(perm)@.snp().requires_pvalidate(vaddr as int, psize as int, validate as int),
        mycore.coreid@.vmpl == 0,
        mycore.inv(),
    ensures
        old(perm)@.snp.pvalidate_ret(
            perm@.snp,
            ret,
            *rflags,
            vaddr as int,
            psize as int,
            validate as int,
        ),
        old(perm)@.range() === perm@.range(),
        old(perm)@.bytes().wf() ==> perm@.bytes().wf(),
{
    let flags: u64;
    let rc: u64;
    unsafe {
        asm!(
                ".byte 0xF2, 0x0F, 0x01, 0xFF",
                "pushf; pop {out}\n\t",
                out = out(reg) flags,
                lateout("eax") rc,
                in("eax") vaddr,
                in("ecx") psize,
                in("edx") validate,
            );
    }
    *rflags = flags;
    rc
}

// If the rmpadjust is for vmsa page, newcore perm is required.
// After rmpadjust, the current context my lose the ownership of the page.
//  * If creating vmsa page, the memory perm will be taken into the function if the vmsa is for a different cpu.
#[verifier(external_body)]
pub fn rmpadjust(
    vaddr: u64,
    psize: u64,
    attr: RmpAttr,
    Tracked(mycore): Tracked<&SnpCore>,
    Tracked(newcore): Tracked<Option<CoreIdPerm>>,
    Tracked(perm): Tracked<&mut SnpPointsToRaw>,
) -> (ret: u64)
    requires
        old(perm)@.snp().requires_rmpadjust(vaddr as int, psize as int, attr@, newcore, old(perm)@),
        mycore.coreid@.vmpl == 0,
        attr.spec_vmpl() > mycore.coreid@.vmpl,
    ensures
        old(perm)@.snp.rmpadjust_ret(perm@.snp, ret, vaddr as int, psize as int, attr@),
        old(perm)@.range() === perm@.range(),
        old(perm)@.snp_bytes === perm@.snp_bytes,
{
    let ret: u64;
    unsafe {
        asm!(".byte 0xf3,0x0f,0x01,0xfe",
                in("rax") vaddr, in("rcx") psize, in("rdx") attr.value,
                lateout("rax") ret,
                options(nostack));
    }
    ret
}

} // verus!
