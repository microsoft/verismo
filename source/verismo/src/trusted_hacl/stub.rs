use crate::addr_e::VAddr;
use crate::ptr::*;
use crate::registers::SnpCore;
use crate::snp::ghcb::*;
use crate::tspec::*;

verus! {

#[no_mangle]
pub extern "C" fn __stack_chk_fail(Tracked(core): Tracked<&mut SnpCore>)
    requires
        old(core).inv(),
    ensures
        false,
{
    vc_terminate(SM_EVERCRYPT_ERR(1), Tracked(core))
}

#[no_mangle]
pub extern "C" fn printf() {
}

#[no_mangle]
pub extern "C" fn __fprintf_chk() {
}

#[no_mangle]
pub extern "C" fn stderr() {
}

#[no_mangle]
pub extern "C" fn exit(Tracked(core): Tracked<&mut SnpCore>)
    requires
        old(core).inv(),
    ensures
        false,
{
    vc_terminate(SM_EVERCRYPT_ERR(2), Tracked(core))
}

#[no_mangle]
pub extern "C" fn __memcpy_chk(
    dst_addr: usize,
    src_addr: usize,
    len: usize,
    dst_len: usize,
    Tracked(dst_perm0): Tracked<&mut Map<int, SnpPointsToRaw>>,
    Tracked(src_perm): Tracked<&SnpPointsToRaw>,
) -> (ret: usize)
    requires
        src_perm@.ptr_not_null_wf(src_addr as int, len as nat),
        old(dst_perm0).contains_key(0),
        old(dst_perm0)[0]@.ptr_not_null_wf(dst_addr as int, dst_len as nat),
        len > 0,
        dst_len > 0,
        src_addr != 0,
        dst_addr != 0,
    ensures
        dst_perm0.contains_key(0),
        dst_perm0[0]@.range() === old(dst_perm0)[0]@.range(),
        dst_perm0[0]@.snp() === old(dst_perm0)[0]@.snp(),
        dst_perm0[0]@.wf(),
        ret == dst_addr ==> dst_perm0[0]@.bytes() =~~= (src_perm@.bytes() + old(
            dst_perm0,
        )[0]@.bytes().skip(len as int)),
        (ret == 0) ==> (*dst_perm0) =~~= (*old(dst_perm0)),
{
    if dst_len < len {
        return 0;
    } else {
        let tracked (mut dst_perm, right_perm) = dst_perm0.tracked_remove(0).trusted_split(
            len as nat,
        );
        mem_copy(src_addr, dst_addr, len, Tracked(src_perm), Tracked(&mut dst_perm));
        proof {
            dst_perm0.tracked_insert(0, dst_perm.trusted_join(right_perm));
        }
        return dst_addr;
    }
}

#[no_mangle]
pub extern "C" fn __printf_chk() {
}

#[no_mangle]
pub extern "C" fn malloc(size: usize, Tracked(core): Tracked<&mut SnpCore>)
    requires
        old(core).inv(),
    ensures
        false,
{
    vc_terminate(SM_EVERCRYPT_ERR(3), Tracked(core));
}

#[no_mangle]
pub extern "C" fn calloc(size: usize, Tracked(core): Tracked<&mut SnpCore>)
    requires
        old(core).inv(),
    ensures
        false,
{
    vc_terminate(SM_EVERCRYPT_ERR(4), Tracked(core))
}

#[no_mangle]
pub extern "C" fn free(addr: usize, Tracked(core): Tracked<&mut SnpCore>)
    requires
        old(core).inv(),
    ensures
        false,
{
    vc_terminate(SM_EVERCRYPT_ERR(5), Tracked(core))
}

} // verus!
