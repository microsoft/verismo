use super::*;

verus! {

pub open spec fn spec_set_zeros(old_perm: SnpPointsToBytes, perm: SnpPointsToBytes) -> bool {
    &&& perm.range() === old_perm.range()
    &&& perm.snp() === old_perm.snp()
    &&& perm.wf()
    &&& perm.is_assign_with(Seq::new(perm.range().1, |i| u8_s::spec_constant(0)@))
    &&& perm.bytes().is_constant()
}

pub open spec fn spec_mem_copy(
    bytes: SecSeqByte,
    dst_perm: SnpPointsToBytes,
    old_dst_perm: SnpPointsToBytes,
) -> bool {
    &&& dst_perm.range() === old_dst_perm.range()
    &&& dst_perm.snp() === old_dst_perm.snp()
    &&& dst_perm.wf()
    &&& bytes.len() == dst_perm.range().1 ==> dst_perm.bytes() =~~= bytes
    &&& bytes.len() < dst_perm.range().1 ==> dst_perm.bytes() =~~= bytes
        + old_dst_perm.bytes().skip(bytes.len() as int)
    &&& bytes.len() > dst_perm.range().1 ==> dst_perm.bytes() =~~= bytes.take(
        dst_perm.range().1 as int,
    )
}

pub open spec fn spec_mem_copy_onepage_start(i: int, dst_addr: int, size: nat) -> int {
    let start = i.to_addr() - dst_addr;
    if start < size {
        start
    } else {
        size as int
    }
}

pub open spec fn spec_mem_copy_onepage_end(i: int, dst_addr: int, size: nat) -> int {
    let start = i.to_addr() - dst_addr;
    let end = if (i + 1).to_addr() - dst_addr > size {
        size as int
    } else {
        (i + 1).to_addr() - dst_addr
    };
    end
}

pub open spec fn spec_mem_copy_page(
    i: int,
    dst_addr: int,
    size: nat,
    bytes: SecSeqByte,
    dst_perm: SnpPointsToBytes,
    old_dst_perm: SnpPointsToBytes,
) -> bool {
    let start = spec_mem_copy_onepage_start(i, dst_addr, size);
    let end = spec_mem_copy_onepage_end(i, dst_addr, size);
    spec_mem_copy(bytes.subrange(start, end), dst_perm, old_dst_perm)
}

/// mem_set_zeros will leave the data as non-secret.
#[inline(always)]
#[verifier(external_body)]
pub fn mem_set_zeros(addr: usize, size: usize, Tracked(perm): Tracked<&mut SnpPointsToRaw>)
    requires
        old(perm)@.snp_wf_range((addr as int, size as nat)),
    ensures
        spec_set_zeros(old(perm)@, perm@),
{
    unsafe {
        core::intrinsics::volatile_set_memory(addr as *mut u8, 0, size);
    }
}

#[inline(always)]
#[verifier(external_body)]
pub fn mem_set_zeros2(
    addr: usize,
    size: usize,
    Tracked(perms): Tracked<&mut Map<int, SnpPointsToRaw>>,
)
    requires
        forall|i|
            (addr as int).to_page() <= i < ((addr + size) as int).to_page() ==> #[trigger] old(
                perms,
            ).contains_key(i) && old(perms)[i]@.snp_wf_range(
                ((i as int).to_addr(), PAGE_SIZE as nat),
            ),
    ensures
        perms.dom() =~~= old(perms).dom(),
        forall|i|
            (addr as int).to_page() <= i < ((addr + size) as int).to_page() ==> spec_set_zeros(
                old(perms)[i]@,
                perms[i]@,
            ),
{
    unsafe {
        core::intrinsics::volatile_set_memory(addr as *mut u8, 0, size);
    }
}

#[inline(always)]
#[verifier(external_body)]
pub fn mem_copy(
    src_addr: usize,
    dst_addr: usize,
    size: usize,
    Tracked(src_perm): Tracked<&SnpPointsToRaw>,
    Tracked(dst_perm): Tracked<&mut SnpPointsToRaw>,
)
    requires
        src_perm@.wf_not_null((src_addr as int, size as nat)),
        old(dst_perm)@.wf_not_null((dst_addr as int, size as nat)),
    ensures
        spec_mem_copy(src_perm@.bytes(), dst_perm@, old(dst_perm)@),
{
    unsafe {
        core::ptr::copy(src_addr as *mut u8, dst_addr as *mut u8, size);
    }
}

#[inline(always)]
#[verifier(external_body)]
pub fn mem_copy_to_pages(
    src_addr: usize,
    dst_addr: usize,
    size: usize,
    Tracked(src_perm): Tracked<&SnpPointsToRaw>,
    Tracked(dst_perm): Tracked<&mut Map<int, SnpPointsToRaw>>,
)
    requires
        forall|i|
            (dst_addr as int).to_page() <= i < ((dst_addr + size) as int).to_page() ==> old(
                dst_perm,
            ).contains_key(i),
        forall|i|
            old(dst_perm).contains_key(i) ==> old(dst_perm)[i]@.wf_not_null(
                ((i as int).to_addr(), PAGE_SIZE as nat),
            ),
        src_perm@.wf_not_null((src_addr as int, size as nat)),
        (dst_addr as int) % (PAGE_SIZE as int) == 0,
    ensures
        dst_perm.dom() =~~= old(dst_perm).dom(),
        forall|i: int| #[trigger]
            dst_perm.contains_key(i) ==> spec_mem_copy_page(
                i,
                dst_addr as int,
                size as nat,
                src_perm@.bytes(),
                dst_perm[i]@,
                old(dst_perm)[i]@,
            ),
{
    unsafe {
        core::ptr::copy(src_addr as *mut u8, dst_addr as *mut u8, size);
    }
}

} // verus!
