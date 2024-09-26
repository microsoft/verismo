use vstd::slice::slice_index_get;

use super::*;
use crate::allocator::VeriSMoAllocator;
use crate::boot::init::e820_init_alloc::init_allocator_e820;

verus! {

pub open spec fn init_allocator_requires(
    allocator: VeriSMoAllocator,
    hv_mem_tb: &[HyperVMemMapEntry],
    e820: &[E820Entry],
    static_start: usize_t,
    static_end: usize_t,
    memcc: SnpMemCoreConsole,
) -> bool {
    &&& allocator.is_constant()
    &&& allocator@.inv()
    &&& static_start.is_constant()
    &&& static_end.is_constant()
    &&& static_end.spec_valid_addr_with(0)
    &&& static_start.spec_valid_addr_with(1)
    &&& static_start < static_end
    &&& mem_range_formatted(hv_mem_tb@)
    &&& mem_range_formatted(e820@)
    &&& e820@.wf()
    &&& hv_mem_tb@.wf()
    &&& memcc.wf()
    &&& forall|i: int|
        0 <= i < hv_mem_tb@.len() ==> memcc.memperm.contains_default_except(
            (#[trigger] hv_mem_tb@[i]).range(),
            e820@.to_valid_ranges().insert(range(static_start as int, static_end as int)),
        )
}

fn init_allocator(
    allocator: &mut VeriSMoAllocator,
    hv_mem_tb: &[HyperVMemMapEntry],
    e820: &[E820Entry],
    static_start: usize_t,
    static_end: usize_t,
    Tracked(memcc): Tracked<SnpMemCoreConsole>,
) -> (newcc: Tracked<SnpCoreConsole>)
    requires
        init_allocator_requires(*old(allocator), hv_mem_tb, e820, static_start, static_end, memcc),
    ensures
        newcc@.wf_core(memcc.cc.snpcore.cpu()),
        allocator@.inv(),
        newcc@.snpcore.only_reg_coremode_updated(memcc.cc.snpcore, set![GHCB_REGID()]),
{
    let ghost oldmemcc = memcc;
    let tracked SnpMemCoreConsole { mut memperm, cc } = memcc;
    let ghost coreid = cc.snpcore.cpu();
    let ghost verismo_static = range(static_start as int, static_end as int);
    let ghost except_ranges = e820@.to_valid_ranges().insert(verismo_static);
    let ghost oldmem = memperm;
    let static_start = static_start;
    let static_end = static_end;
    let mut idx: usize = 0;
    let mut prev_end: usize = 0;
    let len = hv_mem_tb.len();
    if len == 0 {
        new_strlit("bad hv_mem len\n").leak_debug();
        vc_terminate(SM_TERM_INVALID_PARAM, Tracked(&mut cc.snpcore));
    }
    let tracked mut memcc = SnpMemCoreConsole { memperm, cc };
    proof {
        assert forall|i: int|
            (idx as int) <= i < (len as int) implies memcc.memperm.contains_default_except(
            hv_mem_tb@[i].range(),
            except_ranges,
        ) by {
            assert(oldmem.contains_default_except(hv_mem_tb@[i].range(), except_ranges));
        }
    }
    while idx < len
        invariant
            idx <= len,
            static_end.spec_valid_addr_with(0),
            static_start.spec_valid_addr_with(1),
            static_start < static_end,
            len == hv_mem_tb@.len(),
            verismo_static === range(static_start as int, static_end as int),
            except_ranges === e820@.to_valid_ranges().insert(verismo_static),
            mem_range_formatted(hv_mem_tb@),
            mem_range_formatted(e820@),
            e820@.wf(),
            hv_mem_tb@.wf(),
            prev_end.spec_valid_addr_with(0),
            (allocator)@.inv(),
            idx == 0 ==> prev_end as int == 0,
            idx > 0 ==> prev_end as int == hv_mem_tb@[idx as int - 1].range().end(),
            memcc.wf_core(coreid),
            memcc.cc.snpcore.only_reg_coremode_updated(oldmemcc.cc.snpcore, set![GHCB_REGID()]),
            forall|i: int|
                (idx as int) <= i < (len as int) ==> memcc.memperm.contains_default_except(
                    (#[trigger] hv_mem_tb@[i]).range(),
                    except_ranges,
                ),
            forall|i: int|
                0 <= i < idx as int ==> prev_end as int >= (#[trigger] hv_mem_tb@[i]).range().end(),
            prev_end as int <= verismo_static.0 || prev_end as int >= verismo_static.end(),
    {
        let entry = slice_index_get(hv_mem_tb, idx as usize_t);
        let start_gpn = entry.start().reveal_value();
        let npages = entry.size().reveal_value();
        let tracked SnpMemCoreConsole { mut memperm, cc } = memcc;
        let ghost prev_memperm = memperm;
        proof {
            assert(npages != 0);
            assert(entry.wf_range());
        }
        if !start_gpn.check_valid_pn(npages) || prev_end > start_gpn.to_addr() {
            // HV reported overlapped memory
            new_strlit("zero or invalid or overlapped start pg").leak_debug();
            vc_terminate(SM_TERM_INVALID_PARAM, Tracked(&mut cc.snpcore));
        }
        let end_gpn = start_gpn + npages;
        let start = start_gpn.to_addr();
        let end = end_gpn.to_addr();
        let ghost g_current_range = range(start as int, end as int);
        let static_range = (static_start, static_end - static_start);
        let current_range = (start, end - start);
        let inside = static_range.check_inside(&current_range);
        let disjoint = static_range.check_disjoint(&current_range);
        if !disjoint && !inside {
            // the static mem is not fully covered in one range.
            new_strlit("the static mem is not fully covered in one range.\n").leak_debug();
            vc_terminate(SM_TERM_INVALID_PARAM, Tracked(&mut cc.snpcore));
        }
        let tracked mut cc = cc;
        if inside {
            proof {
                assert(inside_range(verismo_static, g_current_range));
                assert(start@ <= static_start@);
                assert(end@ >= static_end@);
                if static_end@ < end@ {
                    lemma_contains_except_remove(
                        memperm,
                        range(static_end as int, end as int),
                        g_current_range,
                        except_ranges,
                        verismo_static,
                    );
                }
                if start@ < static_start@ {
                    lemma_contains_except_remove(
                        memperm,
                        range(start as int, static_start as int),
                        g_current_range,
                        except_ranges,
                        verismo_static,
                    );
                }
            }
            let ghost mut remain_range = g_current_range;
            if start < static_start {
                proof {
                    assert(verismo_static.end() == static_end as int);
                    assert(end as int >= verismo_static.end());
                    let used_range = range(start as int, static_start as int);
                    assert(memperm.contains_default_except(used_range, except_ranges)) by {
                        memperm.lemma_with_except_sub(
                            used_range,
                            g_current_range,
                            SwSnpMemAttr::spec_default(),
                            except_ranges,
                        );
                    }
                    remain_range = range(static_start as int, end as int);
                    assert(memperm.contains_default_except(remain_range, except_ranges)) by {
                        memperm.lemma_with_except_sub(
                            remain_range,
                            g_current_range,
                            SwSnpMemAttr::spec_default(),
                            except_ranges,
                        );
                    }
                    memperm.proof_remove_range_ensures(used_range);
                    memperm.proof_remove_range_ensures_except(used_range);
                    let tracked hv_memperm = memperm.tracked_split(used_range);
                    assert(hv_memperm.contains_default_except(used_range, except_ranges));
                    assert(inside_range(used_range, g_current_range) && range_disjoint_(
                        verismo_static,
                        used_range,
                    ));
                    assert(hv_memperm.contains_default_except(used_range, except_ranges)) by {
                        assert forall|r|
                            inside_range(r, used_range) && ranges_disjoint(except_ranges, r) && r.1
                                != 0 implies #[trigger] hv_memperm.contains_range(r)
                            && hv_memperm[r].snp() === SwSnpMemAttr::spec_default() by {
                            assert(ranges_disjoint(except_ranges, r)) by {
                                assert(range_disjoint_(verismo_static, used_range));
                            }
                            assert(hv_memperm.contains_range(r));
                        }
                    }
                    assert(hv_memperm.wf());
                    memcc = SnpMemCoreConsole { memperm: hv_memperm, cc };
                }
                let Tracked(tmpcc) = init_allocator_e820(
                    allocator,
                    e820,
                    start,
                    static_start,
                    Tracked(memcc),
                );
                proof {
                    cc = tmpcc;
                }
            }
            if static_end < end {
                proof {
                    let used_range = range(static_end as int, end as int);
                    assert(memperm.contains_default_except(used_range, except_ranges)) by {
                        memperm.lemma_with_except_sub(
                            used_range,
                            remain_range,
                            SwSnpMemAttr::spec_default(),
                            except_ranges,
                        );
                    }
                    let memperm0 = memperm;
                    memperm.proof_remove_range_ensures(used_range);
                    memperm.proof_remove_range_ensures_except(used_range);
                    let tracked mut hv_memperm = memperm.tracked_split(used_range);
                    assert(hv_memperm.contains_default_except(used_range, except_ranges));
                    memcc = SnpMemCoreConsole { memperm: hv_memperm, cc };
                    assert(inside_range(used_range, g_current_range) && range_disjoint_(
                        verismo_static,
                        used_range,
                    ));
                    assert(hv_memperm.contains_default_except(used_range, e820@.to_valid_ranges()))
                        by {
                        assert forall|r|
                            (inside_range(r, used_range) && r.1 != 0 && ranges_disjoint(
                                e820@.to_valid_ranges(),
                                r,
                            )) implies (hv_memperm.contains_range(r) && hv_memperm[r].snp()
                            === SwSnpMemAttr::spec_default()) by {
                            assert(ranges_disjoint(except_ranges, r)) by {
                                assert(range_disjoint_(verismo_static, used_range));
                            }
                            assert(hv_memperm.contains_default_except(used_range, except_ranges));
                            assert(hv_memperm.contains_range(r));
                        }
                    }
                }
                let Tracked(tmpcc) = init_allocator_e820(
                    allocator,
                    e820,
                    static_end,
                    end,
                    Tracked(memcc),
                );
                proof {
                    cc = tmpcc;
                }
            }
        } else {
            proof {
                assert(range_disjoint_(verismo_static, g_current_range));
                let used_range = g_current_range;
                memperm.proof_remove_range_ensures(used_range);
                memperm.proof_remove_range_ensures_except(used_range);
                assert(memperm.contains_default_except(used_range, except_ranges));
                //lemma_contains_except_remove(memperm, used_range, g_current_range, except_ranges, verismo_static);
                let tracked mut hv_memperm = memperm.tracked_split(used_range);
                assert(hv_memperm.contains_default_except(used_range, except_ranges));
                assert(inside_range(used_range, g_current_range) && range_disjoint_(
                    verismo_static,
                    used_range,
                ));
                assert(hv_memperm.contains_default_except(used_range, e820@.to_valid_ranges())) by {
                    assert forall|r|
                        inside_range(r, used_range) && r.1 != 0 && ranges_disjoint(
                            e820@.to_valid_ranges(),
                            r,
                        ) implies hv_memperm.contains_range(r) && hv_memperm[r].snp()
                        === SwSnpMemAttr::spec_default() by {
                        assert(ranges_disjoint(except_ranges, r)) by {
                            assert(range_disjoint_(verismo_static, used_range));
                        }
                        assert(hv_memperm.contains_range(r));
                    }
                }
                memcc = SnpMemCoreConsole { memperm: hv_memperm, cc };
            }
            let Tracked(tmpcc) = init_allocator_e820(allocator, e820, start, end, Tracked(memcc));
            proof {
                cc = tmpcc;
            }
        }
        prev_end = end;
        idx = idx + 1;
        proof {
            memcc = SnpMemCoreConsole { memperm, cc };
            assert forall|i: int|
                (idx as int) <= i < (len as int) implies memcc.memperm.contains_default_except(
                hv_mem_tb@[i].range(),
                except_ranges,
            ) by {
                assert(prev_memperm.contains_default_except(hv_mem_tb@[i].range(), except_ranges));
                mem_range_formatted_is_disjoint(hv_mem_tb@);
                assert(range_disjoint_(hv_mem_tb@[i].range(), g_current_range));
                prev_memperm.proof_remove_range_ensures(g_current_range);
            }
        }
    }
    Tracked(memcc.cc)
}

} // verus!
verus! {

pub struct InitAllocFn;

pub type InitAllocParams<'a, 'b> = (
    InitAllocFn,
    &'a [HyperVMemMapEntry],
    &'b [E820Entry],
    usize,
    usize,
    Tracked<SnpMemCoreConsole>,
);

use crate::vbox::MutFnTrait;

impl<'a, 'b, 'c> MutFnTrait<
    'c,
    InitAllocParams<'a, 'b>,
    Tracked<SnpCoreConsole>,
> for VeriSMoAllocator {
    open spec fn spec_update_requires(&self, params: InitAllocParams<'a, 'b>) -> bool {
        init_allocator_requires(*self, params.1, params.2, params.3, params.4, params.5@)
    }

    open spec fn spec_update(
        &self,
        prev: &Self,
        params: InitAllocParams<'a, 'b>,
        ret: Tracked<SnpCoreConsole>,
    ) -> bool {
        &&& ret@.wf_core(params.5@.cc.snpcore.cpu())
        &&& self@.inv()
        &&& ret@.snpcore.only_reg_coremode_updated(params.5@.cc.snpcore, set![GHCB_REGID()])
    }

    fn box_update(&'c mut self, params: InitAllocParams<'a, 'b>) -> (ret: Tracked<SnpCoreConsole>) {
        init_allocator(self, params.1, params.2, params.3, params.4, params.5)
    }
}

} // verus!
