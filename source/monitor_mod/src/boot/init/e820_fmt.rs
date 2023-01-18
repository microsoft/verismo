use vstd::slice::{slice_index_get, slice_subrange};

use super::*;
use crate::arch::addr_s::{GVA, VM_MEM_SIZE};
use crate::ptr::rmp::*;

verismo_simple! {
    pub open spec fn e820_lt() -> spec_fn(E820Entry, E820Entry) -> bool {
        |v1: E820Entry, v2: E820Entry| v1.addr < v2.addr
    }
}

verus! {
    pub fn e820_format<const N: usize_t>(e820tb: &mut Array<E820Entry, N>, e820_entries: usize_t) -> (ret: Option<&[E820Entry]>)
    requires
        old(e820tb).is_constant(),
        e820_entries.is_constant(),
        e820_entries < old(e820tb)@.len(),
    ensures
        ret.is_Some() ==> e820tb.is_constant(),
        ret.is_Some() ==> (ret.get_Some_0()@.is_constant() && ret.get_Some_0()@.len() <= (e820_entries as nat)),
        ret.is_Some() ==> ret.get_Some_0()@ === e820tb@.take(ret.get_Some_0()@.len() as int),
        ret.is_Some() ==> format_range_ensures(ret.get_Some_0()@, old(e820tb)@.take(e820_entries as int), e820_entries as nat),
    {
        let ghost prev_e820tb = e820tb@;
        proof {
            assert(prev_e820tb.is_constant());
            assert forall |i| 0 <= i < (e820_entries as int)
            implies
                (#[trigger]prev_e820tb[i]).spec_real_range().0.is_constant() && prev_e820tb[i].spec_real_range().1.is_constant()
            by{
                proof_into_is_constant::<_, usize_s>(prev_e820tb[i].addr);
                proof_into_is_constant::<_, usize_s>(prev_e820tb[i].size);
            }
        }
        let ghost prev_e820 = e820tb@.take(e820_entries as int);
        let (visited, e820_len) = e820tb.format_range(e820_entries);

        if visited < e820_entries {
            // wrong format
            ((new_strlit("visited < e820_entries"), visited), e820_entries).leak_debug();
            return Option::None;
        }
        let e820 = e820tb.as_slice();
        let e820 = slice_subrange(e820, 0, e820_len);
        proof {
            let e820 = e820@;
            assert(e820.is_constant()) by{
                assert(prev_e820.is_constant());
                assert(format_range_ensures(e820, prev_e820, visited as nat));
                assert  forall |i| 0 <= i < (e820_len as int)
                implies is_format_entry(e820[i], prev_e820) by{
                };
                assert forall |i| 0 <= i < e820.len()
                implies
                    e820[i].is_constant()
                by{
                    let entry = e820[i];
                    assert(is_format_entry(entry, prev_e820));
                    proof_into_is_constant::<_, u64_s>(entry.spec_real_range().0);
                    proof_into_is_constant::<_, u64_s>(entry.spec_real_range().1);
                    let j = choose |j| entry === prev_e820[j].spec_set_range(entry.spec_real_range())
                                        && (0 <= j) && j < prev_e820.len();
                    assert(prev_e820[j].is_constant());
                    assert(entry.is_constant());
                }
            }
            assert(e820tb.is_constant()) by {
                assert forall |i| 0 <= i < e820tb@.len()
                implies
                    e820tb@[i].is_constant()
                by {
                    assert(prev_e820tb[i].is_constant());
                    if i >= e820.len() {
                        assert(prev_e820tb.contains(e820tb@[i]));
                        let j = choose |j| prev_e820tb[j] === e820tb@[i] && 0 <= j <prev_e820tb.len();
                        assert(e820tb@[i] === prev_e820tb[j]);
                        assert(prev_e820tb[j].is_constant());
                    } else {
                        assert(e820tb@[i] === e820[i]);
                    }
                }
            }
        }
        Option::Some(e820)
    }
}
