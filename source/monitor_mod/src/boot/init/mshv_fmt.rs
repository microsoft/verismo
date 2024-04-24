use vstd::slice::slice_subrange;

use super::*;
use crate::arch::addr_s::VM_MEM_SIZE;
use crate::boot::init::e820_init::*;

#[verifier::publish]
pub const ZERO: usize = 0;
verus! {

pub closed spec fn get_hv_mem_count_ensures(arr: Seq<HyperVMemMapEntry>, ret: nat) -> bool {
    &&& ret <= arr.len()
    &&& forall|i: int| 0 <= i < (ret as int) ==> arr[i].numpages@.val != 0
    &&& ret < arr.len() ==> arr[ret as int].numpages@.val == 0
}

pub fn get_hv_mem_count(arr: &HyperVMemMapTable) -> (ret: usize_t)
    requires
        arr.is_constant(),
    ensures
        ret <= arr@.len(),
        ret.is_constant(),
        forall|i: int| 0 <= i < (ret as int) ==> arr@[i].numpages@.val != 0,
        ret < arr@.len() ==> arr@[ret as int].numpages@.val == 0,
        get_hv_mem_count_ensures(arr@, ret as nat),
{
    let mut ret = 0usize;
    let len = arr.len();
    while ret < len
        invariant
            ret <= arr@.len(),
            len == arr@.len(),
            ret.is_constant(),
            len.is_constant(),
            arr.is_constant(),
            forall|i: int| 0 <= i < (ret as int) ==> arr@[i].numpages@.val != 0,
        ensures
            ret < arr@.len() ==> arr@[ret as int].numpages@.val == 0,
            ret <= arr@.len(),
            ret.is_constant(),
            forall|i: int| 0 <= i < (ret as int) ==> arr@[i].numpages@.val != 0,
    {
        if arr.index(ret).numpages.reveal_value() == 0 {
            break ;
        }
        ret = ret + 1usize;
    }
    ret
}

pub closed spec fn fmt_hvparam_ensures(
    prev_hvparam: HvParamTable,
    hvparam: HvParamTable,
    n: nat,
    ret: &[HyperVMemMapEntry],
) -> bool {
    let prev_memtab = prev_hvparam.mem_table@;
    let mem_table = ret@;
    &&& hvparam === prev_hvparam.spec_set_mem_table(hvparam.mem_table)
    &&& format_range_ensures(ret@, prev_hvparam.mem_table@.take(n as int), n)
    &&& ret@.is_constant()
    &&& ret@ === hvparam.mem_table@.take(ret@.len() as int)
    &&& ret@.len() <= n <= hvparam.mem_table@.len()
}

pub fn fmt_hvparam<'a>(hv_param: &'a mut HvParamTable, n: usize_t) -> (ret: Option<
    &'a [HyperVMemMapEntry],
>)
    requires
        old(hv_param).is_constant(),
        n <= old(hv_param).mem_table@.len(),
        n.is_constant(),
        forall|i: int| 0 <= i < (n as int) ==> old(hv_param).mem_table@[i].numpages@.val != 0,
        n < old(hv_param).mem_table@.len() ==> old(hv_param).mem_table@[n as int].numpages@.val
            == 0,
    ensures
        ret.is_Some() ==> fmt_hvparam_ensures(
            *old(hv_param),
            *hv_param,
            n as nat,
            ret.get_Some_0(),
        ),
{
    let ghost hvslice = hv_param.mem_table@.subrange(0, n as int);
    proof {
        let seq = hv_param.mem_table@;
        assert(hv_param.mem_table@.is_constant());
        assert forall|i| 0 <= i < (n as int) implies (
        #[trigger] seq[i]).spec_real_range().0.is_constant()
            && seq[i].spec_real_range().1.is_constant() by {
            assert(seq[i].is_constant());
            proof_into_is_constant::<_, usize_s>(seq[i].starting_gpn);
            proof_into_is_constant::<_, usize_s>(seq[i].numpages);
        }
    }
    let ghost prev_memtb = hv_param.mem_table@.take(n as int);
    let (visited, validn) = hv_param.mem_table.format_range(n);
    proof {
        assert(validn <= hv_param.mem_table@.len());
        let memtb = hv_param.mem_table@.take(validn as int);
        assert(format_range_ensures(memtb, prev_memtb, visited as nat));
        assert(forall|i| 0 <= i < memtb.len() ==> is_format_entry(#[trigger] memtb[i], prev_memtb));
        assert(memtb.is_constant()) by {
            assert forall|i| 0 <= i < memtb.len() implies memtb[i].is_constant() by {
                let entry = memtb[i];
                if i < validn as int {
                    assert(is_format_entry(entry, prev_memtb));
                    let j = choose|j|
                        entry === prev_memtb[j].spec_set_range(entry.spec_real_range()) && 0 <= j
                            && j < prev_memtb.len();
                    assert(entry === prev_memtb[j].spec_set_range(entry.spec_real_range()));
                    assert(entry.spec_real_range().0.is_constant());
                    assert(entry.spec_real_range().1.is_constant());
                    proof_into_is_constant::<_, u64_s>(entry.spec_real_range().0);
                    proof_into_is_constant::<_, u64_s>(entry.spec_real_range().1);
                    assert(prev_memtb[j].is_constant());
                    assert(entry.starting_gpn.is_constant());
                    assert(entry.numpages.is_constant());
                    assert(entry.is_constant());
                } else {
                    assert(prev_memtb.contains(entry));
                    let j = choose|j| entry === prev_memtb[j] && 0 <= j < prev_memtb.len();
                    assert(prev_memtb[j].is_constant());
                    assert(entry === prev_memtb[j]);
                    assert(entry.is_constant());
                }
            }
        }
    }
    if visited != n || validn == 0 {
        // HV reported memory is malformatted or is empty.
        return None
    }
    let ghost sorted_hvslice = hv_param.mem_table@.subrange(0, n as int);
    let hv_mem_slice = hv_param.mem_table.as_slice();
    let hv_mem_slice = slice_subrange(hv_mem_slice, 0, validn);
    Some(hv_mem_slice)
}

pub struct FmtHvParamCall;

pub type FmtHvParamOut<'a> = (&'a [HyperVMemMapEntry]);

use crate::vbox::MutFnWithCSTrait;

impl<'a> MutFnWithCSTrait<'a, SnpCoreConsole, FmtHvParamCall, FmtHvParamOut<'a>> for HvParamTable {
    open spec fn spec_update_cs_requires(
        &self,
        params: FmtHvParamCall,
        cs: SnpCoreConsole,
    ) -> bool {
        &&& cs.wf()
        &&& self.is_constant()
    }

    open spec fn spec_update_cs(
        &self,
        prev: &Self,
        params: FmtHvParamCall,
        oldcs: SnpCoreConsole,
        ret: FmtHvParamOut<'a>,
        cs: SnpCoreConsole,
    ) -> bool {
        &&& cs.wf_core(oldcs.snpcore.cpu())
        &&& cs.snpcore === oldcs.snpcore
        &&& ret@.len() > 0
        &&& mem_range_formatted(ret@)
        &&& ret@.is_constant()
        &&& exists|n: nat| #[trigger]
            get_hv_mem_count_ensures(prev.mem_table@, n) && #[trigger] fmt_hvparam_ensures(
                *prev,
                *self,
                n,
                ret,
            )
    }

    fn box_update_cs(
        &'a mut self,
        params: FmtHvParamCall,
        Tracked(cs): Tracked<&mut SnpCoreConsole>,
    ) -> (ret: FmtHvParamOut<'a>) {
        let n = get_hv_mem_count(&self.mem_table);
        let hv_mem_slice = fmt_hvparam(self, n);
        if hv_mem_slice.is_none() {
            early_vc_terminate_debug(SM_TERM_INVALID_PARAM, Tracked(cs));
        }
        let hv_mem_slice = hv_mem_slice.unwrap();
        if (hv_mem_slice.len() as usize) == 0 {
            early_vc_terminate_debug(SM_TERM_INVALID_PARAM, Tracked(cs));
        }
        hv_mem_slice
    }
}

} // verus!
