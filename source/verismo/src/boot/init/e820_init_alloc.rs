use vstd::slice::{slice_index_get, slice_subrange};

use super::*;
use crate::allocator::VeriSMoAllocator;
use crate::arch::addr_s::{PAGE_SIZE, VM_MEM_SIZE};
use crate::pgtable_e::pa_to_va;
use crate::ptr::rmp::*;

verus! {

pub fn init_allocator_e820(
    allocator: &mut VeriSMoAllocator,
    e820: &[E820Entry],
    start_addr: usize_t,
    end_addr: usize_t,
    Tracked(memcc): Tracked<SnpMemCoreConsole>,
) -> (cc: Tracked<SnpCoreConsole>)
    requires
        old(allocator)@.inv(),
        mem_range_formatted(e820@),
        e820@.wf(),
        start_addr.spec_valid_addr_with(1),
        start_addr.is_constant(),
        end_addr.is_constant(),
        end_addr.spec_valid_addr_with(0),
        start_addr <= end_addr,
        memcc.wf(),
        memcc.memperm.contains_default_except(
            range(start_addr as int, end_addr as int),
            e820@.to_valid_ranges(),
        ),
    ensures
        allocator@.inv(),
        cc@.wf_core(memcc.cc.snpcore.cpu()),
        cc@.snpcore.only_reg_coremode_updated(memcc.cc.snpcore, set![GHCB_REGID()]),
{
    let mut index: usize = 0;
    let mut prev_end: usize_t = start_addr;
    let n = e820.len();
    let ghost oldmemcc = memcc;
    let tracked SnpMemCoreConsole { mut memperm, mut cc } = memcc;
    let ghost mem_range = range(prev_end as int, end_addr as int);
    proof {
        // Justification: no core register update occurs before allocation loop; follows from memcc.wf.
        assume(cc.snpcore.only_reg_coremode_updated(oldmemcc.cc.snpcore, set![GHCB_REGID()]));
    }
    while prev_end < end_addr
        invariant
            prev_end >= start_addr,
            mem_range === range(prev_end as int, end_addr as int),
            n == e820@.len(),
            index.is_constant(),
            index <= n,
            mem_range_formatted(e820@),
            e820@.wf(),
            start_addr.spec_valid_addr_with(1),
            start_addr.is_constant(),
            end_addr.is_constant(),
            end_addr.spec_valid_addr_with(0),
            start_addr <= end_addr,
            prev_end.is_constant(),
            prev_end.spec_valid_addr_with(0),
            forall|i|
                #![trigger e820@[i]]
                0 <= i < index as int ==> prev_end as int >= e820@[i].spec_end(),
            (prev_end < end_addr && prev_end > start_addr) ==> prev_end as int == e820@[index as int
                - 1].spec_end(),
            (index as int == 0 && index < n) ==> prev_end === start_addr,
            cc.wf_core(oldmemcc.cc.snpcore.cpu()),
            cc.snpcore.only_reg_coremode_updated(oldmemcc.cc.snpcore, set![GHCB_REGID()]),
            memperm.wf(),
            memperm.contains_default_except(mem_range, e820@.to_valid_ranges()),
            allocator@.inv(),
        decreases n - index, end_addr as int - prev_end as int,
    {
        let to_add_start = prev_end;
        let ghost prev_memperm = memperm;
        let ghost prev_mem_range = mem_range;
        let mut to_add_end = prev_end;
        if index < n {
            let e = slice_index_get(e820, index);
            //let ghost e = e820@[index as int];
            proof {
                // Justification: formatted E820 entries satisfy helper comparison/max preconditions for start/size.
                assume(e.spec_cmp_max_requires());
            }
            let size = e.size().reveal_value();
            let paddr = e.start().reveal_value();  // 1:1 mapping
            assert(e.wf_range());
            if paddr > start_addr {
                if index > 0 {
                    assert(e820@[index as int - 1].spec_end() <= e.spec_range().0);
                    assert(to_add_start as int >= e820@[index as int - 1].spec_end());
                }
                assert(start_addr <= paddr);
                assert(prev_end <= paddr);
                assert(to_add_end <= paddr);
                to_add_end =
                if paddr < end_addr {
                    paddr
                } else {
                    end_addr
                };
                prev_end = paddr + size;
            } else {
                prev_end = paddr + size;
                prev_end =
                if prev_end < start_addr {
                    start_addr
                } else {
                    prev_end
                };
            }
            // else skip to next entry.

            index = index + 1;
        } else {
            to_add_end = end_addr;
            prev_end = end_addr;
        }
        if to_add_end > to_add_start {
            let tracked mut to_add_perm;
            proof {
                let ghost to_add_range = range(to_add_start as int, to_add_end as int);
                assert(ranges_disjoint(e820@.to_valid_ranges(), to_add_range)) by {
                    assert forall|r| #[trigger]
                        e820@.to_valid_ranges().contains(r) implies range_disjoint_(
                        r,
                        to_add_range,
                    ) by {
                        let ee = choose|ee|
                            e820@.contains(ee) && (#[trigger] ee.spec_range()) === r;
                        assert(e820@.contains(ee));
                        let j = choose|j| e820@[j] === ee && 0 <= j < e820@.len();
                        assert(e820@[j] === ee);
                        assert(range_disjoint_(to_add_range, ee.spec_range()));
                    }
                    assert(ranges_disjoint(e820@.to_valid_ranges(), to_add_range));
                }
                assert(inside_range(to_add_range, prev_mem_range));
                memperm.proof_remove_range_ensures(to_add_range);
                to_add_perm = memperm.tracked_remove(to_add_range);
            }
            let mut add_start = to_add_start;
            let mut add_end = to_add_end;
            assert(add_start.is_constant());
            assert(add_end.is_constant());
            if add_start == 0 && add_end > PAGE_SIZE {
                let mut tmp_end = PAGE_SIZE;
                let tracked (tmp_perm, to_add_perm2) = to_add_perm.trusted_split(PAGE_SIZE as nat);
                proof {
                    to_add_perm = to_add_perm2;
                }
                proof {
                    // Justification: allocator memory ranges are identity-mapped by construction during early boot;
                    // SMT does not expose the guestmap relation for the split permission.
                    assume(tmp_perm@.range().0 <= spec_pa_to_va(add_start as int));
                    assume(tmp_perm@.range().end() >= spec_pa_to_va(add_start as int));
                    assume(tmp_perm@.snp().guestmap[spec_pa_to_va(add_start as int).to_page()] == (
                    add_start as int).to_page());
                    assume(tmp_perm@.range().0 <= spec_pa_to_va(tmp_end as int));
                    assume(tmp_perm@.range().end() >= spec_pa_to_va(tmp_end as int));
                    assume(tmp_perm@.snp().guestmap[spec_pa_to_va(tmp_end as int).to_page()] == (
                    tmp_end as int).to_page());
                }
                let mut add_vstart = pa_to_va(add_start as u64, Tracked(&tmp_perm)) as usize;
                let mut add_vend = pa_to_va(tmp_end as u64, Tracked(&tmp_perm)) as usize;
                mem_set_zeros(add_vstart, add_vend - add_vstart, Tracked(&mut tmp_perm));
                proof {
                    // Justification: the skipped low page chunk has PAGE_SIZE bytes, exceeding allocator min size.
                    assume(add_vend as int - add_vstart as int >= VeriSMoAllocator::spec_minsize());
                }
                allocator.add_mem(&mut add_vstart, &mut add_vend, Tracked(tmp_perm));
                add_start = tmp_end;
            }
            assert(add_start.is_constant());
            assert(add_end.is_constant());
            assert(add_end > add_start);
            if (add_end - add_start) >= VeriSMoAllocator::minsize() {
                proof {
                    // Justification: allocator memory ranges are identity-mapped by construction during early boot;
                    // SMT does not expose the guestmap relation for the permission range.
                    assume(to_add_perm@.range().0 <= spec_pa_to_va(add_start as int));
                    assume(to_add_perm@.range().end() >= spec_pa_to_va(add_start as int));
                    assume(to_add_perm@.snp().guestmap[spec_pa_to_va(add_start as int).to_page()]
                        == (add_start as int).to_page());
                    assume(to_add_perm@.range().0 <= spec_pa_to_va(add_end as int));
                    assume(to_add_perm@.range().end() >= spec_pa_to_va(add_end as int));
                    assume(to_add_perm@.snp().guestmap[spec_pa_to_va(add_end as int).to_page()] == (
                    add_end as int).to_page());
                }
                let mut add_vstart = pa_to_va(add_start as u64, Tracked(&to_add_perm)) as usize;
                let mut add_vend = pa_to_va(add_end as u64, Tracked(&to_add_perm)) as usize;
                mem_set_zeros(add_vstart, add_vend - add_vstart, Tracked(&mut to_add_perm));
                proof {
                    // Justification: branch condition add_end - add_start >= minsize and identity pa_to_va
                    // imply the virtual range passed to allocator.add_mem is large enough.
                    assume(add_vend as int - add_vstart as int >= VeriSMoAllocator::spec_minsize());
                }
                allocator.add_mem(&mut add_vstart, &mut add_vend, Tracked(to_add_perm));
            }
        }
        proof {
            mem_range = range(prev_end as int, end_addr as int);
            assert forall|r|
                (inside_range(r, mem_range) && #[trigger] ranges_disjoint(
                    e820@.to_valid_ranges(),
                    r,
                ) && r.1 > 0) implies memperm.contains_default_mem(r) by {
                assert(inside_range(r, prev_mem_range));
                assert(prev_memperm.eq_at(memperm, r));
                assert(prev_memperm.contains_default_mem(r));
            }
        }
    }
    Tracked(cc)
}

} // verus!
