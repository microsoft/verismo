use vstd::slice::slice_index_get;

use super::*;
use crate::arch::addr_s::VM_MEM_SIZE;
use crate::ptr::rmp::*;

verus! {

proof fn lemma_validate_e820_single(
    prev_memperm: RawMemPerms,
    memperm: RawMemPerms,
    pre_validated: Set<(int, nat)>,
    prev_validated_range: (int, nat),
    end_addr: int,
    toval_range: (int, nat),
    validated_range: (int, nat),
    entry_r: (int, nat),
)
    requires
        prev_memperm.contains_default_except(prev_validated_range, pre_validated),
        prev_memperm.contains_init_except(
            range(prev_validated_range.end(), VM_MEM_SIZE as int),
            pre_validated,
        ),
        prev_memperm.contains_init_except(
            range(end_addr as int, VM_MEM_SIZE as int),
            pre_validated,
        ),
        forall|r| range_disjoint_(r, toval_range) ==> memperm.eq_at(prev_memperm, r),
        (toval_range.1 > 0) ==> memperm.contains_default_mem(toval_range),
        ranges_disjoint(pre_validated, toval_range),
        (toval_range.1 > 0) ==> (toval_range.0 == prev_validated_range.end()),
        validated_range.0 == prev_validated_range.0,
        pre_validated.contains(entry_r),
        prev_validated_range.end() < entry_r.0 ==> toval_range.1 != 0,
        validated_range.end() == if entry_r.0 < end_addr as int {
            spec_max(prev_validated_range.0, entry_r.end())
        } else {
            end_addr
        },
        validated_range.end() >= prev_validated_range.end(),
        toval_range.end() <= end_addr,
        (toval_range.1 > 0) ==> toval_range.end() == spec_min(
            end_addr,
            spec_max(entry_r.0, prev_validated_range.0),
        ),
        prev_validated_range.end() <= end_addr,
    ensures
        memperm.contains_default_except(validated_range, pre_validated),
        memperm.contains_init_except(
            range(validated_range.end(), VM_MEM_SIZE as int),
            pre_validated,
        ),
        memperm.contains_init_except(range(end_addr as int, VM_MEM_SIZE as int), pre_validated),
        forall|r| range_disjoint_(r, toval_range) ==> memperm.eq_at(prev_memperm, r),
{
    let end_init_range = range(end_addr as int, VM_MEM_SIZE as int);
    assert forall|r: (int, nat)|
        r.1 != 0 && inside_range(r, validated_range) && ranges_disjoint(
            pre_validated,
            r,
        ) implies memperm.contains_range(r) && memperm.contains_default_mem(r) by {
        let snp = SwSnpMemAttr::spec_default();
        assert(memperm.contains_default_except(prev_validated_range, pre_validated));
        assert(memperm.contains_default_except(toval_range, pre_validated)) by {
            memperm.proof_contains_range_to_except(toval_range, pre_validated);
        }
        assert(memperm.contains_default_except(entry_r, pre_validated)) by {
            memperm.lemma_empty_contains_except(entry_r, snp, pre_validated)
        }
        let leftr = if toval_range.1 != 0 {
            let leftr = memperm.lemma_with_except_union(
                prev_validated_range,
                toval_range,
                snp,
                pre_validated,
            );
            leftr
        } else {
            prev_validated_range
        };
        let fullr = if leftr.0 <= entry_r.0 && leftr.end() >= entry_r.0 && leftr.end()
            <= entry_r.end() {
            memperm.lemma_with_except_union(leftr, entry_r, snp, pre_validated)
        } else {
            leftr
        };
        assert(inside_range(r, fullr));
        memperm.lemma_with_except_sub(r, fullr, snp, pre_validated);
        assert(memperm.contains_default_except(fullr, pre_validated));
        assert(memperm.contains_range(r));
        assert(memperm.contains_default_mem(r));
    }
    let prev_init_range = range(prev_validated_range.end(), VM_MEM_SIZE as int);
    let next_init_range = range(validated_range.end(), VM_MEM_SIZE as int);
    assert(memperm.contains_init_except(next_init_range, pre_validated)) by {
        if next_init_range.1 != 0 {
            assert(inside_range(next_init_range, prev_init_range));
        }
        prev_memperm.lemma_with_except_sub(
            next_init_range,
            prev_init_range,
            SwSnpMemAttr::init(),
            pre_validated,
        );
        assert forall|r: (int, nat)|
            r.1 != 0 && inside_range(r, next_init_range) && ranges_disjoint(
                pre_validated,
                r,
            ) implies memperm.contains_range(r) && memperm.contains_init_mem(r) by {
            assert(range_disjoint_(r, toval_range));
            assert(prev_memperm.contains_init_mem(r));
        }
    }
    assert forall|r: (int, nat)|
        r.1 != 0 && inside_range(r, end_init_range) && ranges_disjoint(
            pre_validated,
            r,
        ) implies #[trigger] memperm.contains_range(r) && memperm.contains_init_mem(r) by {
        assert(prev_memperm.contains_init_mem(r));
    }
}

spec fn validate_e820_loop_inv(
    e820: Seq<E820Entry>,
    n: usize,
    start_addr: usize,
    end_addr: usize,
    pre_validated: Set<(int, nat)>,
) -> bool {
    &&& n == e820.len()
    &&& pre_validated === e820.to_aligned_ranges()
    &&& e820.is_constant()
    &&& start_addr < end_addr <= VM_MEM_SIZE
    &&& end_addr as int % PAGE_SIZE!() == 0
    &&& start_addr as int % PAGE_SIZE!() == 0
    &&& mem_range_formatted(e820)
}

proof fn lemma_validated_range_disjoint_e820(
    e820: Seq<E820Entry>,
    i: int,
    start_addr: int,
    end_addr: int,
    toval_range: (int, nat),
)
    requires
        0 <= i < e820.len(),
        toval_range === validate_e820_iter_val_range(e820, i, start_addr, end_addr),
        mem_range_formatted(e820),
    ensures
        ranges_disjoint(e820.to_aligned_ranges(), toval_range),
{
    let pre_validated = e820.to_aligned_ranges();
    assert forall|r| #[trigger] pre_validated.contains(r) implies range_disjoint_(
        toval_range,
        r,
    ) by {
        let k = choose|k: int| e820[k].spec_aligned_range() === r && 0 <= k && k < e820.len();
        assert(e820[k].spec_aligned_range() === r);
        assert(pre_validated.contains(r));
    }
}

spec fn validate_e820_iter_val_start(e820: Seq<E820Entry>, i: int, start: int, end: int) -> int {
    if i <= 0 {
        start
    } else {
        if e820[i - 1].spec_aligned_range().0 < end {
            spec_max(start, e820[i - 1].spec_aligned_range().end())
        } else {
            end
        }
    }
}

spec fn validate_e820_iter_val_end(e820: Seq<E820Entry>, i: int, end: int) -> int {
    spec_min(e820[i].spec_aligned_range().0, end)
}

spec fn validate_e820_iter_val_range(e820: Seq<E820Entry>, i: int, start: int, end: int) -> (
    int,
    nat,
) {
    range(
        validate_e820_iter_val_start(e820, i, start, end),
        validate_e820_iter_val_end(e820, i, end),
    )
}

pub fn validate_e820(
    e820: &[E820Entry],
    start_addr: usize_t,
    end_addr: usize_t,
    Tracked(memcc): Tracked<SnpMemCoreConsole>,
) -> (newmemcc: Tracked<SnpMemCoreConsole>)
    requires
        e820@.is_constant(),
        mem_range_formatted(e820@),
        start_addr < end_addr <= VM_MEM_SIZE,
        start_addr as int % PAGE_SIZE!() == 0,
        end_addr as int % PAGE_SIZE!() == 0,
        memcc.wf(),
        memcc.memperm.contains_init_except(
            range(start_addr as int, VM_MEM_SIZE as int),
            e820@.to_aligned_ranges(),
        ),
    ensures
        newmemcc@.wf_core(memcc.cc.snpcore.cpu()),
        newmemcc@.cc.snpcore.only_reg_coremode_updated(memcc.cc.snpcore, set![GHCB_REGID()]),
        forall|r|
            range_disjoint_(r, range(start_addr as int, end_addr as int))
                ==> newmemcc@.memperm.eq_at(memcc.memperm, r),
        newmemcc@.memperm.contains_default_except(
            range(start_addr as int, end_addr as int),
            e820@.to_aligned_ranges(),
        ),
        newmemcc@.memperm.contains_init_except(
            range(end_addr as int, VM_MEM_SIZE as int),
            e820@.to_aligned_ranges(),
        ),
{
    let ghost pre_validated = e820@.to_aligned_ranges();
    let ghost oldmemcc = memcc;
    let ghost cpu = oldmemcc.cc.snpcore.cpu();
    let tracked SnpMemCoreConsole { mut memperm, mut cc } = memcc;
    let n = e820.len();
    let mut val_end = start_addr;
    let mut index = 0usize;
    proof {
        memperm.lemma_with_except_sub(
            range(end_addr as int, VM_MEM_SIZE as int),
            range(start_addr as int, VM_MEM_SIZE as int),
            SwSnpMemAttr::init(),
            pre_validated,
        );
        memperm.lemma_empty_contains_except(
            range(start_addr as int, val_end as int),
            SwSnpMemAttr::spec_default(),
            pre_validated,
        );
    }
    while val_end < end_addr && index < n
        invariant
            index <= e820@.len(),
            n == e820@.len(),
            validate_e820_loop_inv(e820@, n, start_addr, end_addr, pre_validated),
            memperm.wf(),
            cc.wf_core(cpu),
            cc.snpcore.only_reg_coremode_updated(oldmemcc.cc.snpcore, set![GHCB_REGID()]),
            memperm.contains_default_except(
                range(start_addr as int, val_end as int),
                pre_validated,
            ),
            memperm.contains_init_except(range(val_end as int, VM_MEM_SIZE as int), pre_validated),
            memperm.contains_init_except(range(end_addr as int, VM_MEM_SIZE as int), pre_validated),
            forall|r|
                range_disjoint_(r, range(start_addr as int, end_addr as int)) ==> memperm.eq_at(
                    oldmemcc.memperm,
                    r,
                ),
            val_end as int % PAGE_SIZE!() == 0,
            val_end >= start_addr,
            val_end == validate_e820_iter_val_start(
                e820@,
                index as int,
                start_addr as int,
                end_addr as int,
            ),
    {
        let ghost prev_end: int = val_end as int;
        let ghost prev_memperm = memperm;
        let ghost gstart = start_addr as int;
        let ghost prev_init_range = range(prev_end, VM_MEM_SIZE as int);
        let ghost prev_validated_range = range(gstart, prev_end);
        let mut next_start = val_end;
        let val_start = val_end;
        let entry = *slice_index_get(e820, index);
        let ghost entry_r = entry.spec_aligned_range();
        proof {
            assert(inside_ranges(entry_r, pre_validated) && pre_validated.contains(entry_r)) by {
                e820@.lemma_align_ranges_reveal();
                assert(pre_validated.contains(entry_r));
            }
            assert(entry.wf_range());
        }
        let cur_addr = entry.aligned_start().reveal_value();
        let cur_end = page_align_up(entry.end().reveal_value());
        assert(cur_end == entry_r.end());
        if cur_addr < end_addr {
            next_start =
            if cur_end > start_addr {
                cur_end
            } else {
                start_addr
            };
            val_end = cur_addr;
        } else {
            next_start = end_addr;
            val_end = end_addr;
        }
        assert(next_start as int == if entry_r.0 < end_addr as int {
            spec_max(start_addr as int, entry_r.end())
        } else {
            end_addr as int
        });
        let ghost toval_range = range(val_start as int, val_end as int);
        proof {
            assert(ranges_disjoint(pre_validated, toval_range)) by {
                lemma_validated_range_disjoint_e820(
                    e820@,
                    index as int,
                    start_addr as int,
                    end_addr as int,
                    toval_range,
                );
            }
        }
        proof {
            if toval_range.1 > 0 {
                assert(toval_range.0 == prev_end);
                memperm.lemma_with_except_sub(
                    toval_range,
                    prev_init_range,
                    SwSnpMemAttr::init(),
                    pre_validated,
                );
                assert(memperm.contains_init_except(toval_range, pre_validated));
                assert(memperm.contains_init_mem(toval_range)) by {
                    assert(ranges_disjoint(pre_validated, toval_range));
                    assert(inside_range(toval_range, toval_range));
                    assert(memperm.contains_range(toval_range));
                }
                memperm.proof_remove_range_ensures(toval_range);
            }
        }
        if val_end > val_start {
            let tracked pperm = memperm.tracked_remove(toval_range);
            let Tracked(pperm) = pvalmem(
                val_start as u64,
                val_end as u64,
                true,
                Tracked(pperm),
                Tracked(&mut cc.snpcore),
            );
            proof {
                assert(memperm.contains_default_except(prev_validated_range, pre_validated));
                memperm.tracked_insert(toval_range, pperm);
                assert(memperm.contains_default_mem(toval_range));
                memperm.proof_remove_range_ensures(toval_range);
                assert(range_disjoint_(toval_range, prev_validated_range));
                assert(memperm.contains_default_except(toval_range, pre_validated)) by {
                    memperm.proof_contains_range_to_except(toval_range, pre_validated);
                }
                assert(memperm.contains_default_except(prev_validated_range, pre_validated));
            }
        }
        proof {
            let validated_range = range(gstart, next_start as int);
            if toval_range.1 != 0 {
                assert(memperm.contains_default_mem(toval_range));
            }
            lemma_validate_e820_single(
                prev_memperm,
                memperm,
                pre_validated,
                prev_validated_range,
                end_addr as int,
                toval_range,
                validated_range,
                entry_r,
            );
            //assert(validate_e820_loop_inv(e820@, n, start_addr, end_addr, pre_validated));
        }
        index = index + 1;
        val_end = next_start;
        proof {
            assert(val_end as int % PAGE_SIZE!() == 0 && val_end >= start_addr && index == 0
                ==> val_end == start_addr && index > 0 ==> val_end == spec_max(
                start_addr as int,
                e820@[index as int - 1].spec_aligned_range().end(),
            ));
        }
    }
    let ghost validated_range = range(start_addr as int, end_addr as int);
    let ghost prev_memperm = memperm;
    let ghost end_init_range = range(end_addr as int, VM_MEM_SIZE!());
    if val_end < end_addr {
        let ghost toval_range = range(val_end as int, end_addr as int);
        let ghost prev_validated_range = range(start_addr as int, val_end as int);
        proof {
            memperm.proof_remove_range_ensures(toval_range);
        }
        let tracked pperm = memperm.tracked_remove(toval_range);
        let Tracked(pperm) = pvalmem(
            val_end as u64,
            end_addr as u64,
            true,
            Tracked(pperm),
            Tracked(&mut cc.snpcore),
        );
        proof {
            assert(memperm.contains_default_except(prev_validated_range, pre_validated));
            memperm.tracked_insert(toval_range, pperm);
            assert(memperm.contains_default_mem(toval_range));
            memperm.proof_remove_range_ensures(toval_range);
            assert(range_disjoint_(toval_range, prev_validated_range));
            assert(memperm.contains_default_except(toval_range, pre_validated)) by {
                memperm.proof_contains_range_to_except(toval_range, pre_validated);
            }
            assert(memperm.contains_default_except(validated_range, pre_validated)) by {
                memperm.lemma_with_except_union(
                    prev_validated_range,
                    toval_range,
                    SwSnpMemAttr::spec_default(),
                    pre_validated,
                );
            }
        }
    } else {
        proof {
            memperm.lemma_with_except_sub(
                validated_range,
                range(start_addr as int, val_end as int),
                SwSnpMemAttr::spec_default(),
                pre_validated,
            );
        }
    }
    proof {
        assert forall|r: (int, nat)|
            r.1 != 0 && inside_range(r, end_init_range) && ranges_disjoint(
                pre_validated,
                r,
            ) implies #[trigger] memperm.contains_range(r) && memperm.contains_init_mem(r) by {
            assert(prev_memperm.contains_init_mem(r));
        }
    }
    Tracked(SnpMemCoreConsole { memperm, cc })
}

} // verus!
