use vstd::slice::{slice_index_get, slice_subrange};

use super::mshv_alloc::InitAllocFn;
use super::*;
use crate::allocator::VeriSMoAllocator;
use crate::arch::addr_s::VM_MEM_SIZE;
use crate::boot::init::e820_init::*;
use crate::lock::LockPermRaw;
use crate::vbox::{MutFnTrait, VBox};

verismo_simple! {
    pub open spec fn init_vm_mem_requires(
        e820: &[E820Entry],
        static_start: usize, static_end: usize,
        memcc: SnpMemCoreConsole,
        unused_preval_memperm: RawMemPerms
    ) -> bool {
        &&& e820@.is_constant()
        &&& mem_range_formatted(e820@)
        &&& memcc.wf()
        &&& static_start.spec_valid_addr_with(1)
        &&& static_end.spec_valid_addr_with(0)
        &&& static_start.is_constant()
        &&& static_end.is_constant()
        &&& static_start < static_end
        &&& unused_preval_memperm.wf()
        &&& forall |r| e820@.to_aligned_ranges().contains(r) ==>
            unused_preval_memperm.contains_default_except(r, e820@.to_valid_ranges())
        &&& memcc.memperm.contains_init_except((0, VM_MEM_SIZE as nat), e820@.to_aligned_ranges())
    }
}

verus! {

pub fn process_vm_mem(
    hv_mem_slice: &[HyperVMemMapEntry],
    e820: &[E820Entry],
    static_start: usize,
    static_end: usize,
    Tracked(memcc): Tracked<SnpMemCoreConsole>,
    Tracked(unused_preval_memperm): Tracked<RawMemPerms>,
    Tracked(alloc_perm): Tracked<SnpPointsTo<VeriSMoAllocator>>,
    Tracked(alloc_lock): Tracked<&mut LockPermRaw>,
) -> (newcc: Tracked<SnpCoreConsole>)
    requires
        is_alloc_perm(alloc_perm@),
        old(alloc_lock)@.is_clean_lock_for(spec_ALLOCATOR().ptr_range(), memcc.cc.snpcore.cpu()),
        init_vm_mem_requires(e820, static_start, static_end, memcc, unused_preval_memperm),
        hv_mem_slice@.is_constant(),
        mem_range_formatted(hv_mem_slice@),
        hv_mem_slice@.len() > 0,
    ensures
        newcc@.wf_core(memcc.cc.snpcore.cpu()),
        newcc@.snpcore.only_reg_coremode_updated(memcc.cc.snpcore, set![GHCB_REGID()]),
        spec_ALLOCATOR().lock_default_mem_requires(newcc@.snpcore.cpu(), alloc_lock@),
        is_permof_ALLOCATOR(alloc_lock@),
{
    let ghost verismo_range = range(static_start as int, static_end as int);
    let tracked mut memcc = memcc;
    let entry = slice_index_get(hv_mem_slice, 0);
    let tracked SnpMemCoreConsole { memperm, mut cc } = memcc;
    SlicePrinter { s: hv_mem_slice }.debug(Tracked(&mut cc));
    proof {
        memcc = SnpMemCoreConsole { memperm, cc };
        assert(cc.wf());
        assert(memperm.wf());
    }
    // initial 1:1 mapping
    if entry.start().to_addr().reveal_value() > static_start || entry.end().to_addr().reveal_value()
        < static_end {
        // verismo code and static vars are not covered by the first range?
        vc_terminate(SM_TERM_INVALID_PARAM, Tracked(&mut memcc.cc.snpcore));
    }
    let Tracked(memcc) = validate_vm_mem(hv_mem_slice, e820, Tracked(memcc));
    let alloc_ref = ALLOCATOR();
    let alloc_ptr = alloc_ref.ptr();
    let mut allocator: VBox<VeriSMoAllocator> = VBox::from_raw(
        alloc_ptr.to_usize(),
        Tracked(alloc_perm),
    );
    proof {
        let tracked SnpMemCoreConsole { mut memperm, cc } = memcc;
        let ghost prev_memperm = memperm;
        memperm.tracked_union(unused_preval_memperm);
        assert forall|i: int| 0 <= i < hv_mem_slice@.len() implies memperm.contains_default_except(
            (#[trigger] hv_mem_slice@[i]).range(),
            e820@.to_valid_ranges(),
        ) by {
            RawMemPerms::lemma_union_propograte_except(
                prev_memperm,
                unused_preval_memperm,
                hv_mem_slice@[i].range(),
                SwSnpMemAttr::spec_default(),
                e820@.to_aligned_ranges(),
                e820@.to_valid_ranges(),
            );
        }
        let static_range = range(static_start as int, static_end as int);
        let first_range = hv_mem_slice@[0].range();
        assert(inside_range(static_range, first_range));
        let prev_memperm = memperm;
        memperm.proof_remove_range_ensures(verismo_range);
        memperm.tracked_split(verismo_range);
        assert forall|i: int| 0 <= i < hv_mem_slice@.len() implies memperm.contains_default_except(
            hv_mem_slice@[i].range(),
            e820@.to_valid_ranges().insert(verismo_range),
        ) by {
            let excepted = e820@.to_valid_ranges().insert(verismo_range);
            assert forall|r|
                inside_range(r, hv_mem_slice@[i].range()) && ranges_disjoint(excepted, r) && r.1
                    != 0 implies memperm.contains_range(r) && memperm.contains_default_mem(r) by {
                assert(excepted.contains(verismo_range));
                assert(range_disjoint_(verismo_range, r));
                assert(memperm.eq_at(prev_memperm, r));
                assert(ranges_disjoint(e820@.to_valid_ranges(), r)) by {
                    assert forall|rr| e820@.to_valid_ranges().contains(rr) implies range_disjoint_(
                        rr,
                        r,
                    ) by {
                        assert(excepted.contains(rr));
                    }
                }
                assert(prev_memperm.contains_default_except(
                    hv_mem_slice@[i].range(),
                    e820@.to_valid_ranges(),
                ));
                assert(prev_memperm.contains_range(r));
            }
        }
        memcc = SnpMemCoreConsole { memperm, cc };
    }
    let Tracked(cc) = allocator.box_update(
        (InitAllocFn, hv_mem_slice, e820, static_start, static_end, Tracked(memcc)),
    );
    let (_, Tracked(alloc_perm)) = allocator.into_raw();
    proof {
        assert(allocator@@.inv());
        alloc_lock.tracked_bind_new(VeriSMoAllocator::invfn(), alloc_perm);
        assert(alloc_lock@.invfn.inv(allocator@));
        assert(alloc_lock@.cpu == cc.snpcore.cpu());
        assert(alloc_lock@.is_unlocked(
            cc.snpcore.cpu(),
            spec_ALLOCATOR().lockid(),
            spec_ALLOCATOR().ptr_range(),
        ));
        assert(spec_ALLOCATOR().lock_requires(cc.snpcore.cpu(), alloc_lock@));
    }
    Tracked(cc)
}

} // verus!
verismo_simple! {
    fn validate_vm_mem(hv_mem_tb: &[HyperVMemMapEntry], e820: &[E820Entry], Tracked(memcc): Tracked<SnpMemCoreConsole>) -> (newmemcc: Tracked<SnpMemCoreConsole>)
    requires
        e820@.is_constant(),
        mem_range_formatted(e820@),
        memcc.wf(),
        memcc.memperm.contains_init_except((0, VM_MEM_SIZE as nat), e820@.to_aligned_ranges()),
        hv_mem_tb@.is_constant(),
        mem_range_formatted(hv_mem_tb@),
    ensures
        newmemcc@.wf(),
        newmemcc@.cc.snpcore.cpu() == memcc.cc.snpcore.cpu(),
        newmemcc@.cc.snpcore.only_reg_coremode_updated(
            memcc.cc.snpcore,
            set![GHCB_REGID()]),
        forall |i: int| 0 <= i < hv_mem_tb@.len() ==>
            newmemcc@.memperm.contains_default_except((#[trigger]hv_mem_tb@[i]).range(), e820@.to_aligned_ranges()),
    {
        let mut idx: usize = 0;
        let mut prev_end: usize = 0;
        let tracked mut memcc = memcc;
        let ghost oldmemcc = memcc;
        let ghost cpu = memcc.cc.snpcore.cpu();
        let len = usize_s::constant(hv_mem_tb.len());
        let ghost pre_validated = e820@.to_aligned_ranges();
        while idx < len
        invariant
            idx <= len,
            idx.is_constant(),
            len.is_constant(),
            e820@.is_constant(),
            pre_validated === e820@.to_aligned_ranges(),
            mem_range_formatted(e820@),
            len == hv_mem_tb@.len(),
            hv_mem_tb@.is_constant(),
            mem_range_formatted(hv_mem_tb@),
            prev_end.spec_valid_addr_with(0),
            prev_end.is_constant(),
            idx == 0 ==> prev_end as int == 0,
            idx > 0 ==> prev_end as int == hv_mem_tb@[idx as int - 1].range().end(),
            (memcc).wf_core(cpu),
            memcc.cc.snpcore.only_reg_coremode_updated(
                oldmemcc.cc.snpcore,
                set![GHCB_REGID()]),
            forall |i: int| 0 <= i < idx as int ==>
                memcc.memperm.contains_default_except(
                    (#[trigger]hv_mem_tb@[i]).range(), pre_validated),
            forall |i: int| 0 <= i < idx as int ==>
                prev_end as int >= (#[trigger]hv_mem_tb@[i]).range().end(),
            memcc.memperm.contains_init_except(range(prev_end as int, VM_MEM_SIZE!()), pre_validated),
        {
            let entry = slice_index_get(hv_mem_tb, idx as usize_t);
            let start_gpn = entry.starting_gpn as usize;
            let npages = entry.numpages as usize;
            let tracked SnpMemCoreConsole{mut memperm, mut cc} = memcc;
            let tracked mut cc: SnpCoreConsole = cc;
            let ghost prev_memperm = memperm;
            proof {
                assert(npages != 0);
                assert(cc.wf());
                assert(memperm.wf());
            }
            if !start_gpn.check_valid_pn(npages) ||
                prev_end > start_gpn.to_addr()
            {
                // HV reported overlapped memory
                vc_terminate(SM_TERM_INVALID_PARAM, Tracked(&mut cc.snpcore));
            }

            let end_gpn = start_gpn.add(npages);
            let start = start_gpn.to_addr();
            let end = end_gpn.to_addr();
            let ghost used_range = range(start as int, end as int);
            let ghost remain_init_range = range(start as int, VM_MEM_SIZE!());
            proof {reveal_strlit("range: ");}
            (new_strlit("range: "), (start as u64, end as u64)).debug(Tracked(&mut cc));
            proof {
                assert(used_range === hv_mem_tb@[idx as int].range());
                memperm.lemma_with_except_sub(remain_init_range, range(prev_end as int, VM_MEM_SIZE!()), SwSnpMemAttr::init(), pre_validated);
                //memcc.memperm.lemma_invalided_range_sub(
                //    e820@.to_set(), range(prev_end, VM_MEM_SIZE as int), range(start, VM_MEM_SIZE as int));
                assert(cc.wf());
                assert(memperm.wf());
                memcc = SnpMemCoreConsole{memperm, cc};
            }
            let Tracked(newmemcc) = validate_e820(e820, start.reveal_value(), end.reveal_value(), Tracked(memcc));
            prev_end = end;
            idx = idx + 1;
            proof {
                memcc = newmemcc;
                assert forall |i: int| 0 <= i < (idx as int)
                implies
                    memcc.memperm.contains_default_except(
                        (#[trigger]hv_mem_tb@[i]).range(), pre_validated)
                by {
                    if i < (idx as int - 1) {
                        assert(prev_memperm.contains_default_except(hv_mem_tb@[i].range(), pre_validated));
                        assert(range_disjoint_(hv_mem_tb@[i].range(), used_range));
                    }
                }
            }
        }
        Tracked(memcc)
    }
}
