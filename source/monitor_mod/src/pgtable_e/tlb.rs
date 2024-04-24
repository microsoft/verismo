use core::arch::asm;

use crate::addr_e::*;
use crate::arch::addr_s::*;
use crate::ptr::*;
use crate::tspec::*;
use crate::tspec_e::*;
use crate::*;

verus! {

pub open spec fn ensure_invlpg(prev_mem_perm: SnpPointsToRaw, mem_perm: SnpPointsToRaw) -> bool {
    let snp = mem_perm@.snp();
    let prev_snp = prev_mem_perm@.snp();
    &&& snp === prev_snp.spec_set_pte(snp.pte)
    &&& snp.pte =~~= seq![prev_snp.pte.last()]
    &&& snp.pte() === prev_snp.pte.last()
    &&& mem_perm@.bytes() === prev_mem_perm@.bytes()
    &&& mem_perm@.range() === prev_mem_perm@.range()
}

/// Invalidate TLB for a given address using the `invlpg` instruction.
/// The PTE will be updated to apply the recent pte change.
#[inline]
#[verifier(external_body)]
pub fn invlpg(vaddr: u64, Tracked(mem_perm): Tracked<&mut SnpPointsToRaw>)
    requires
        (vaddr as int).spec_valid_addr_with(PAGE_SIZE as nat),
        (vaddr as int) % (PAGE_SIZE as int) == 0,
    ensures
        ensure_invlpg(*old(mem_perm), *mem_perm),
{
    unsafe {
        asm!("invlpg [{}]", in(reg) vaddr, options(nostack, preserves_flags));
    }
}

} // verus!
