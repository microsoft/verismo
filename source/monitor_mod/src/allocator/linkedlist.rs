use core::mem::size_of;

use super::*;
use crate::addr_e::AddrTrait;
use crate::debug::VPrintAtLevel;
use crate::linkedlist::{LinkedList, Node, SpecListItem};
use crate::ptr::*;

verus! {
pub const MIN_VERISMO_PADDR: usize = 0x10_000;
}

verismo_simple! {
    pub struct LinkedListAllocator {
        perms: Tracked<Map<nat, SnpPointsToRaw>>,
        // Use the last bytes of each mem range to store nodes
        // each entry stores the end addr and the next entry
        free_list: LinkedList<usize_t>,
    }

    pub ghost struct SpecLinkedListAllocator {
        pub perms: Map<nat, SnpPointsToRaw>,
        // Use the last bytes of each mem range to store nodes
        pub free_list: LinkedList<usize_t>,
    }
}

verus! {
    impl SpecLinkedListAllocator {
        pub closed spec fn start(&self, i: nat) -> int {
            let SpecListItem {ptr: node_ptr, snp: node_snp, val} = self.free_list@[i as int];
            val as int
        }

        pub closed spec fn wf_perm(&self, i: nat) -> bool
        {
            let freelist = self.free_list@;
            let SpecListItem {ptr: node_ptr, snp: node_snp, val} = freelist[i as int];
            let node_size = spec_size::<Node<usize_t>>();
            let start = val as int;
            let end = node_ptr.id() + node_size;
            let perm = self.perms[i]@;
            &&& self.perms.contains_key(i)
            &&& (val as int) == perm.range().0
            &&& perm.size() + node_size + start == end
            &&& perm.wf_freemem((node_ptr.id() - perm.size(), perm.size()))
            &&& perm.snp() === SwSnpMemAttr::spec_default()
            &&& node_snp === SwSnpMemAttr::spec_default()
            &&& node_ptr.not_null()
            &&& val.is_constant()
        }

        pub closed spec fn len(&self) -> nat {
            self.free_list@.len()
        }

        pub closed spec fn wf(&self) -> bool {
            &&& forall |i: nat| i < self.len() ==> #[trigger] self.wf_perm(i)
        }

        pub closed spec fn inv(&self) -> bool {
            &&& self.free_list.inv()
            &&& self.wf()
        }

        proof fn lemma_use_perms_map_as_seq(&self)
        requires
            self.wf()
        ensures
            forall |k: nat| k < self.len() ==> #[trigger]self.perms.contains_key(k)
        {
            assert forall |k: nat| k < self.len()
            implies #[trigger] self.perms.contains_key(k)
            by {
                assert(self.wf_perm(k));
            }
        }
    }
}
verus! {
impl LinkedListAllocator {
    proof fn lemma_use_perms_map_as_seq(&self)
    requires
        self@.wf()
    ensures
        forall |k: nat| k < self@.len() ==> #[trigger]self.perms@.contains_key(k)
    {
        self@.lemma_use_perms_map_as_seq();
        assert forall |k: nat| k < self@.len()
        implies #[trigger] self.perms@.contains_key(k)
        by {
            assert(self@.perms.contains_key(k));
        }
    }

    pub open spec fn invfn() -> spec_fn(Self) -> bool {
        |v: LinkedListAllocator| v@.inv()
    }

    pub closed spec fn view(&self) -> SpecLinkedListAllocator {
        SpecLinkedListAllocator {
            perms: self.perms@,
            free_list: self.free_list,
        }
    }

    pub open spec fn spec_minsize() -> nat {
        spec_size::<Node<usize_t>>()
    }
}
}

verus! {
impl LinkedListAllocator {
    #[inline]
    pub fn minsize() -> (ret: usize)
    ensures
        ret == Self::spec_minsize(),
        ret.is_constant(),
    {
        size_of::<Node<usize_t>>()
    }

    pub const fn new() -> (ret: Self)
        ensures
            ret@.len() == 0,
            ret@.inv(),
        {
            LinkedListAllocator {
                free_list: LinkedList::new(),
                perms: Tracked(Map::tracked_empty()),
            }
        }

        pub fn find_prev_of_addr(&self, addr: usize_t) -> (ret: (SnpPPtr<Node<usize_t>>, Ghost<int>))
        requires
            self@.inv(),
            addr.is_constant(),
        ensures
            self@.free_list.contains_ptr_at(ret.0, ret.1@),
            forall |i| ret.1@ <= i < self@.len() ==> self@.free_list@[i].val < addr
        {
            let mut node_ptr = self.free_list.head_ptr();
            let mut prev_ptr = SnpPPtr::nullptr();
            let ghost mut idx: int = self@.len() as int;
            while node_ptr.check_valid()
            invariant
                addr.is_constant(),
                self@.inv(),
                self.free_list.is_constant(),
                node_ptr.is_constant(),
                prev_ptr.is_constant(),
                0 <= idx <= self@.len(),
                (idx == 0) == (node_ptr.is_null()),
                self@.free_list.contains_ptr_at(prev_ptr, idx),
                idx > 0 ==> self@.free_list.contains_ptr_at(node_ptr, idx - 1),
                forall |i: int| idx <= i < self@.len() ==> self.free_list@[i].val < addr
            ensures
                prev_ptr.is_constant(),
                0 <= idx <= self@.len(),
                forall |i| idx <= i < self@.len() ==> self.free_list@[i].val < addr,
                self@.free_list.contains_ptr_at(prev_ptr, idx),
            {
                let ghost i = idx - 1;
                let node = self.free_list.node_at(node_ptr.clone(), Ghost(i));
                let start = node.val;
                assert(self@.wf_perm(i as nat));
                if start >= addr {
                    break;
                }
                prev_ptr = node_ptr;
                node_ptr = node.next_ptr();
                proof {idx = idx - 1;}
            }
            (prev_ptr, Ghost(idx))
        }
        // TODO(ziqiao): search and insert to keep the list sorted.
        pub fn add_mem(&mut self, start: &mut usize, end: &mut usize, Tracked(perm): Tracked<SnpPointsToRaw>)
        requires
            (*old(start)).spec_valid_addr_with(1),
            (*old(end)).spec_valid_addr_with(0),
            old(start).is_constant(),
            old(end).is_constant(),
            (*old(start)) < (*old(end)),
            old(self)@.inv(),
            perm@.wf_freemem(((*old(start) as int), (*old(end) - *old(start)) as nat)),
            *old(end) - *old(start) >= Self::spec_minsize(),
            perm@.snp() === SwSnpMemAttr::spec_default(),
        ensures
            self@.inv(),
            *start === *old(start),
            *end === *old(end),
        {
            let start = *start;
            let end = *end;
            let ghost old_self = *self;
            let ghost size = (end - start) as nat;
            let add_ptr = SnpPPtr::from_usize(end - size_of::<Node<usize_t>>());
            let node = Node{next: 0, val: start};
            let tracked (free_perm, add_perm) = perm.trusted_split((size - Self::spec_minsize()) as nat);
            let tracked mut add_perm = add_perm.trusted_into();
            add_ptr.replace(Tracked(&mut add_perm), node);
            let (prev, Ghost(idx)) = self.find_prev_of_addr(start);
            proof {
                self.lemma_use_perms_map_as_seq();
                assert(self.perms@ === self@.perms);
            }
            let ghost n = self@.len();
            self.free_list.insert(prev, add_ptr, Ghost(idx), Tracked(add_perm));
            proof {
                tracked_seq_insert(self.perms.borrow_mut(), idx as nat, free_perm, n);
                assert(self@.wf_perm(idx as nat));
                assert forall |i: nat| i < self@.len()
                implies #[trigger] self@.wf_perm(i) by{
                    if i < idx {
                        assert(old_self@.wf_perm(i));
                        assert(self.free_list@[i as int] === old_self.free_list@[i as int]);
                        assert(self.perms@[i] === old_self.perms@[i]);
                        assert(self@.wf_perm(i));
                    }
                    if i > idx {
                        assert(old_self@.wf_perm((i - 1) as nat));
                        assert(self.free_list@[i as int] === old_self.free_list@[i - 1]);
                        assert(self.perms@[i] === old_self.perms@[(i - 1) as nat]);
                        assert(self@.wf_perm(i));
                    }
                }
            }
        }

        pub fn remove_range_from(&mut self, node_ptr: SnpPPtr<Node<usize_t>>,
            start: usize_t, new_start: usize_t, Ghost(i): Ghost<int>) -> (perm: Tracked<SnpPointsToRaw>)
        requires
            node_ptr.is_constant(),
            start.is_constant(),
            new_start.is_constant(),
            0 <= i < old(self)@.len(),
            old(self)@.free_list@[i].ptr.id() == node_ptr.id(),
            node_ptr.not_null(),
            old(self)@.inv(),
            start == old(self)@.start(i as nat),
            (start as int) < (new_start as int) <= old(self)@.free_list@[i].ptr.id(),
        ensures
            self@.inv(),
            self@.free_list@ =~~= old(self)@.free_list@.update(i, SpecListItem {ptr: node_ptr, snp: old(self)@.free_list@[i].snp, val: new_start}),
            perm@@.wf_freemem(perm@@.range()),
            perm@@.range() === range(start as int, new_start as int),
        {
            let ghost oldself = self@;
            let tracked mut perm;
            assert(oldself.wf_perm(i as nat));
            proof {
                assert forall |k: nat| k < self@.len()
                implies #[trigger] self@.perms.contains_key(k)
                by {
                    assert(self@.wf_perm(k));
                }
            }
            self.free_list.update_node_at(Ghost(i), node_ptr, new_start);
            proof {
                perm = self.perms.borrow_mut().tracked_remove(i as nat);
                let ghost real_size = (new_start - start) as nat;
                assert(real_size <= perm@.size());
                let tracked (used, free_perm) = perm.trusted_split(real_size);
                self.perms.borrow_mut().tracked_insert(i as nat, free_perm);
                perm = used;
                assert(self@.wf_perm(i as nat)) by {
                    assert(self@.free_list@[i as int].val === new_start);
                    assert(self@.perms[i as nat] === free_perm);
                }
                assert forall |k: nat| k < self@.len()
                    implies self@.wf_perm(k)
                by{
                    assert(oldself.wf_perm(k));
                    if i != k {
                        assert(self@.free_list@[k as int] === oldself.free_list@[k as int]);
                        assert(self@.perms[k as nat] === oldself.perms[k as nat]);
                    }
                }
            }
            assert(self@.inv());
            Tracked(perm)
        }

        pub fn remove_mem(&mut self, prev_ptr: SnpPPtr<Node<usize_t>>, Ghost(i): Ghost<int>) -> (perm: Tracked<SnpPointsToRaw>)
        requires
            0 <= i < old(self)@.len(),
            prev_ptr.is_constant(),
            i != (old(self)@.len() - 1) ==> old(self)@.free_list@[i + 1].ptr.id() == prev_ptr.id(),
            i == (old(self)@.len() - 1) <==> prev_ptr.is_null(),
            old(self)@.inv(),
            old(self)@.free_list@[i].ptr.not_null(),
        ensures
            self@.inv(),
            self@.free_list@ =~~= old(self)@.free_list@.remove(i),
            perm@@.wf_freemem(perm@@.range()),
            perm@@.range() === range(old(self)@.free_list@[i].val as int, old(self)@.free_list@[i].ptr.id() + spec_size::<Node<usize_t>>()),
        {
            let ghost oldself = self@;
            assert(oldself.wf_perm(i as nat));
            proof {
                self.lemma_use_perms_map_as_seq();
                /*assert forall |k: nat| k < self@.len()
                implies #[trigger] self@.perms.contains_key(k)
                by {
                    assert(self@.wf_perm(k));
                }*/
            }
            let Tracked(nodep) = self.free_list.remove(prev_ptr, Ghost(i));
            let tracked mut perm;
            proof {
                perm = map_lib::tracked_seq_remove(self.perms.borrow_mut(), i as nat, self@.len() + 1);
                let tracked nodep = nodep.trusted_into_raw();
                perm = perm.trusted_join(nodep);
                assert forall |k: nat| k < self@.len()
                    implies self@.wf_perm(k)
                by{
                    assert(oldself.wf_perm(k));
                    assert(oldself.wf_perm((k + 1) as nat));
                    if k < i {
                        assert(self@.free_list@[k as int] === oldself.free_list@[k as int]);
                        assert(self@.perms[k as nat] === oldself.perms[k as nat]);
                    } else {
                        assert(self@.free_list@[k as int] === oldself.free_list@[k as int + 1]);
                        assert(self@.perms[k] === oldself.perms[k + 1]);
                        assert(self@.wf_perm(k));
                    }
                }
            }
            Tracked(perm)
        }

        pub fn _alloc_inner(&mut self, size: &mut usize_t, align: usize_t) -> (ret: Option<(usize, Tracked<SnpPointsToRaw>)>)
            requires
                spec_bit64_is_pow_of_2(align as int),
                *old(size) as int > 0,
                old(self)@.inv(),
                *old(size) >= Self::spec_minsize(),
                old(size).is_constant(),
                align.is_constant(),
            ensures
                self@.inv(),
                size.is_constant(),
                ret.is_Some() ==> (MAXU64 - align as int) > (ret.get_Some_0().0 as int),
                ret.is_Some() ==> valid_free_ptr(*size, ret.get_Some_0()),
                ret.is_Some() ==> *old(size) <= *size,
                ret.is_Some() ==> ret.get_Some_0().is_constant(),
                ret.is_Some() ==> inside_range(
                    (spec_align_up(ret.get_Some_0().0 as int, align as int), *old(size) as nat),
                    (ret.get_Some_0().0 as int, *size as nat)),
        {
            let mut node_ptr = self.free_list.head_ptr();
            let mut prev_ptr = SnpPPtr::<Node<usize>>::nullptr();
            let tracked mut ret_perm: Option<SnpPointsToRaw> = Option::None;
            let mut ret: Option<usize> = Option::None;
            let ghost mut idx: int = 0;
            let expect_size = *size;
            while node_ptr.check_valid()
            invariant_except_break
                self@.inv(),
                self.free_list.is_constant(),
                node_ptr.is_constant(),
                align.is_constant(),
                spec_bit64_is_pow_of_2(align as int),
                expect_size > 0,
                expect_size === (*size),
                expect_size.is_constant(),
                prev_ptr.is_constant(),
                0 <= idx <= self@.len(),
                (idx == self@.len()) == (node_ptr.is_null()),
                (idx == 0) == (prev_ptr.is_null()),
                idx != 0 ==> prev_ptr.id() == self.free_list@[self.free_list.reverse_index(idx - 1)].ptr.id(),
                idx < self@.len() ==> node_ptr.id() == self.free_list@[self.free_list.reverse_index(idx)].ptr.id(),
                ret.is_Some() == ret_perm.is_Some(),
                !ret.is_Some(),
            ensures
                self@.inv(),
                self.free_list.is_constant(),
                ret.is_Some() ==>
                    ret_perm.get_Some_0()@.wf_freemem( (ret.get_Some_0() as int, *size as nat)),
                ret.is_Some() ==> inside_range(
                        (spec_align_up(ret.get_Some_0() as int, align as int), expect_size as nat),
                        ret_perm.get_Some_0()@.range()),
                (!node_ptr.not_null()) ==> ret.is_None(),
                ret.is_Some() == ret_perm.is_Some(),
                ret.is_Some() ==> ret.get_Some_0().is_constant(),
                size.is_constant(),
                ret.is_Some() ==> (MAXU64) - align as int > ret.get_Some_0() as int,
            {
                let ghost i = self.free_list.reverse_index(idx);
                let ghost prev_i = self.free_list.reverse_index(idx - 1);
                let ghost oldself = self@;
                assert(idx < self@.len());
                let node = self.free_list.node_at(node_ptr.clone(), Ghost(i));
                proof {
                    if idx == self@.len() - 1 {
                        assert(!node.next.spec_valid_addr_with(spec_size::<Node<usize_t>>()));
                    } else {
                        assert(node.next.spec_valid_addr_with(spec_size::<Node<usize_t>>()));
                    }
                    assert(self@.wf_perm(i as nat));
                    if prev_ptr.not_null() {
                        assert(self@.wf_perm(prev_i as nat));
                    }
                    assert(node_ptr.not_null());
                }
                let minsize = size_of::<Node<usize>>();
                assert(minsize == spec_size::<Node<usize_t>>());
                let start = node.val;
                let end = node_ptr.to_usize() + minsize;
                if (MAXU64 as usize) - align > start {
                    let aligned_start: usize = align_up_by(start as u64, align as u64) as usize;
                    if start >= MIN_VERISMO_PADDR && end > aligned_start && end - aligned_start > expect_size {
                        let mut new_start = aligned_start + expect_size;
                        let tracked mut perm;
                        if end - new_start < minsize {
                            new_start = end;
                            let Tracked(p) = self.remove_mem(prev_ptr, Ghost(i));
                            proof {perm = p;}
                        } else {
                            let Tracked(p) = self.remove_range_from(node_ptr, start, new_start, Ghost(i));
                            proof {perm = p;}
                        }
                        assert(self.free_list.inv());
                        assert(self@.wf());
                        *size = new_start - start;
                        proof {ret_perm = Some(perm)};
                        ret = Some(start);
                        break;
                    }
                }
                prev_ptr = node_ptr;
                node_ptr = node.next_ptr();
                proof {
                    idx = idx + 1;
                    assert(!ret.is_Some());
                }
            }
            if ret.is_some() {
                Some((ret.unwrap(), Tracked(ret_perm.tracked_unwrap())))
            } else {
                None
            }
        }

        pub fn alloc_inner(&mut self, size: usize_t, align: usize_t) -> (ret: Option<(usize, Tracked<SnpPointsToRaw>)>)
        requires
            spec_bit64_is_pow_of_2(align as int),
            (size) as int > 0,
            old(self)@.inv(),
            (size) >= Self::spec_minsize(),
            (size).is_constant(),
            align.is_constant(),
        ensures
            self@.inv(),
            self.wf(),
            ret.is_Some() ==> alloc_valid_ptr(size, ret.get_Some_0()),
            ret.is_Some() ==> ret.get_Some_0().is_constant(),
            ret.is_Some() ==>
                (spec_align_up(ret.get_Some_0().0 as int, align as int), size as nat) ===
                (ret.get_Some_0().0 as int, size as nat),
        {
            let mut real_size = size;
            let ghost old_size = size as nat;
            if let Some((addr, perm)) = self._alloc_inner(&mut real_size, align) {
                let ghost prev_addr = addr;
                let addr: usize_t = align_up_by(addr as u64, align as u64) as usize;
                let Tracked(mut ret_perm) = perm;
                proof {
                    if addr > prev_addr {
                        ret_perm = ret_perm.trusted_split((addr as int - prev_addr as int) as nat).1;
                    }
                    if ret_perm@.size() > old_size {
                        ret_perm = ret_perm.trusted_split(old_size as nat).0;
                    } else {
                        assert(old_size == ret_perm@.size());
                    }
                }
                assert(ret_perm@.wf_freemem((addr as int, size as nat)));
                mem_set_zeros(addr, size, Tracked(&mut ret_perm));
                assert(ret_perm@.wf_freemem((addr as int, size as nat)));
                assert(ret_perm@.wf_const_default((addr as int, size as nat)));
                Some((addr, Tracked(ret_perm)))
            } else {
                None
            }
        }

        // No dealloc
        pub fn dealloc_inner(&mut self, addr: usize_t, size: usize_t, Tracked(perm): Tracked<SnpPointsToRaw>)
        requires
            perm@.wf_default((addr as int, size as nat)),
            size > 0,
            size.is_constant(),
            addr.is_constant(),
            size >= Self::spec_minsize(),
            old(self)@.inv(),
        ensures
            self@.inv(),
            self.wf(),
        {
            let mut start = addr;
            let mut end = addr + size;
            let tracked mut perm = perm;
            mem_set_zeros(addr, size, Tracked(&mut perm));
            self.add_mem(&mut start, &mut end, Tracked(perm));
        }
    }
}

verus! {
impl LinkedListAllocator {
        pub fn remove_one_range(&mut self) -> (ret: Option<((usize, usize), Tracked<SnpPointsToRaw>)>)
        requires
            old(self)@.inv(),
        ensures
            self@.inv(),
            self.wf(),
            ret.is_None() ==> (*self) =~~= (*old(self)),
            ret.is_Some() == (old(self)@.len() > 0),
            ret.is_Some() ==>
                self@.len() <= (old(self)@.len() - 1),
            ret.is_Some() ==>
                ret.get_Some_0().1@@.wf_const_default((ret.get_Some_0().0.0 as int, ret.get_Some_0().0.1 as nat)),
        {
            let mut prev_ptr = SnpPPtr::<Node<usize_t>>::nullptr();
            let mut node_ptr = self.free_list.head_ptr();
            if !node_ptr.check_valid() {
                return None;
            }
            let ghost head_i = self.free_list.reverse_index(0);
            let node = self.free_list.node_at(node_ptr.clone(), Ghost(head_i));
            assert(self@.wf_perm(head_i as nat));
            let mut start = node.val;
            let node_addr = node_ptr.to_usize();
            let end: usize_t = size_of::<Node<usize_t>>() + node_addr;
            let size = end - start;
            //let zero_start = if start < MIN_VERISMO_PADDR {MIN_VERISMO_PADDR} else {start};
           // let zero_size = if end > zero_start {end - zero_start} else {0};
            let Tracked(mut p) = self.remove_mem(prev_ptr, Ghost(head_i));
            Some(((start, size), Tracked(p)))
        }
    }
}
