use core::ptr;

use verismo_macro::*;

use crate::addr_e::*;
use crate::arch::addr_s::*;
use crate::ptr::*;
use crate::tspec_e::*;
use crate::*;

verismo_simple! {
    #[repr(C, align(1))]
    #[derive(VDefault)]
    pub struct Node<T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> {
        pub next: usize_t,
        pub val: T,
    }

    pub tracked struct VSnpPointsToNode<T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> {
        pub next: SnpPointsTo<usize_t>,
        pub val: SnpPointsTo<T>,
    }

    pub ghost struct SpecListItem<T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> {
        pub ptr: SnpPPtr<Node<T>>,
        pub snp: SwSnpMemAttr,
        pub val: T,
    }

    // Cannot directly prove that the linked list is not a circle.
    // Cannot directly prove self.spec_index_of(nodeptr) is unique.
    // However, those properties are implicitly indicated
    // by the fact that each memory token has unique id.
    //
    // Such limitation requires the users to provide a ghost index for node access/
    pub struct LinkedList<T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> {
        // a reversed list of ptrs
        pub ptrs: Ghost<Seq<SpecListItem<T>>>,
        pub perms: Tracked<Map<nat, SnpPointsTo<Node<T>>>>,
        pub head: usize_t,
    }
}

verus! {

impl<T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> SnpPPtr<Node<T>> {
    pub fn set_next(&self, next: usize_t, Tracked(perm): Tracked<SnpPointsTo<Node<T>>>) -> (newperm:
        Tracked<SnpPointsTo<Node<T>>>)
        requires
            (perm)@.ptr_not_null_wf(*self),
            perm@.value().is_Some(),
            next.wf(),
            next.is_constant(),
        ensures
            newperm@@.ptr_not_null_wf(*self),
            newperm@@.value().get_Some_0().next === next,
            newperm@@.value().get_Some_0().val === (perm)@.value().get_Some_0().val,
            newperm@@.snp() === perm@.snp(),
            newperm@@.value().is_Some(),
    {
        let tracked mut mp = perm;
        let tracked mut mp1;
        let tracked mut mp2;
        let ghost old_perm = perm;
        proof {
            let value = mp@.value();
            let tracked tmp = mp.trusted_into_raw();
            assert(tmp@.bytes() === value.get_Some_0().vspec_cast_to());
            let tracked (rmp1, rmp2) = tmp.trusted_split(spec_size::<usize>());
            assert(rmp1@.snp() === rmp2@.snp());
            mp1 = rmp1.trusted_into();
            mp2 = rmp2;
            let bytes1 = old_perm@.value().get_Some_0().next.sec_bytes();
            let bytes2 = old_perm@.value().get_Some_0().val.sec_bytes();
            let bytes3 = old_perm@.value().get_Some_0().sec_bytes();
            assert(bytes3.subrange(bytes1.len() as int, bytes3.len() as int) =~~= bytes2);
            assert(mp2@.bytes() === bytes2);
            assert(mp1@.snp() === mp2@.snp());
            assert(mp1@.value().is_Some());
            assert(mp1@.value().get_Some_0() === value.get_Some_0().next) by {
                let v1 = mp1@.value().get_Some_0();
                let v2 = value.get_Some_0();
                assert(v1 === v1.sec_bytes().vspec_cast_to());
                assert(v2.next === v2.next.sec_bytes().vspec_cast_to());
                assert(v1.sec_bytes() =~~= v2.next.sec_bytes());
            }
        }
        self.to::<usize_t>().replace(Tracked(&mut mp1), next);
        proof {
            let value = mp1@.value();
            mp = mp1.trusted_into_raw().trusted_join(mp2).trusted_into();
            let v2 = mp@.value().get_Some_0();
            let v1 = value.get_Some_0();
            assert(v1.sec_bytes() =~~= (v2.sec_bytes().subrange(0, spec_size::<usize>() as int)));
            //Node::<T>::trusted_to_stream(v2);
            assert(v2.sec_bytes().take(spec_size::<usize>() as int) =~~= (v2.next.sec_bytes()));
            proof_cast_from_seq_unique(v2);
            proof_cast_from_seq_unique(v1);
            assert(mp2@.bytes() =~~= old_perm@.value().get_Some_0().val.sec_bytes());
            assert(v2.sec_bytes().skip(spec_size::<usize>() as int) =~~= v2.val.sec_bytes());
            assert(mp2@.bytes() =~~= v2.sec_bytes().skip(spec_size::<usize>() as int));
            proof_cast_from_seq_unique(mp@.value().get_Some_0().val);
            proof_cast_from_seq_unique(old_perm@.value().get_Some_0().val);
            assert(mp@.value().get_Some_0().next === value.get_Some_0());
        }
        Tracked(mp)
    }
}

impl<T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> Node<T> {
    pub fn next_ptr(&self) -> (ret: SnpPPtr<Node<T>>)
        requires
            self.wf(),
        ensures
            ret.uptr === self.next,
            ret.wf(),
    {
        SnpPPtr::from_usize(self.next)
    }
}

impl<T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> LinkedList<T> {
    spec fn wf_perm_val(&self, i: nat) -> bool
        recommends
            i < self.ptrs@.len(),
    {
        let val = self.perms@[i]@.value().get_Some_0();
        //&&& self.head.is_constant() == val.is_constant()
        &&& self.head.is_constant() == val.next.is_constant()
        &&& self.perms@[i].view().value().is_Some()
        &&& (i > 0 ==> self.perms@[i].view().value().get_Some_0().next as int == self.ptrs@[i
            - 1 as int].ptr.id())
        &&& (i == 0) == (!self.perms@[i].view().value().get_Some_0().next.spec_valid_addr_with(
            spec_size::<Node<T>>(),
        ))
    }

    spec fn wf_perm(&self, i: nat) -> bool
        recommends
            i < self.ptrs@.len(),
    {
        let spec_item = self.ptrs@[i as int];
        let point_to = self.perms@[i]@;
        &&& self.perms@.dom().contains(i)
        &&& point_to.ptr_not_null_wf(spec_item.ptr)
        &&& point_to.snp() === spec_item.snp
        &&& point_to.value().get_Some_0().val === spec_item.val
        &&& self.perms@[i]@.is_valid_private()
        &&& self.wf_perm_val(i)
    }

    spec fn wf_perms(&self) -> bool {
        forall|i: nat| i < self.ptrs@.len() ==> self.wf_perm(i)
    }

    spec fn wf_head(&self) -> bool {
        &&& if self.ptrs@.len() == 0 {
            !self.head.spec_valid_addr_with(spec_size::<Node<T>>())
        } else {
            &&& self.head == self.ptrs@.last().ptr.id()
            &&& self.head.spec_valid_addr_with(spec_size::<Node<T>>())
        }
        &&& self.head.is_constant()
    }

    pub open spec fn inv(&self) -> bool {
        self.inv_hidden() && self.is_constant()
    }

    pub closed spec fn inv_hidden(&self) -> bool {
        self.wf_perms() && self.wf_head() && self.wf()
    }

    pub closed spec fn view(&self) -> Seq<SpecListItem<T>> {
        self.ptrs@
    }

    pub open spec fn contains_ptr_at(&self, ptr: SnpPPtr<Node<T>>, idx: int) -> bool {
        &&& ptr.not_null() ==> (0 <= idx < self@.len() && self@[idx].ptr.id() == ptr.id())
        &&& ptr.is_null() <==> idx == self@.len()
        &&& ptr.is_constant()
    }

    /// Create a new LinkedList
    pub const fn new() -> (ret: LinkedList<T>)
        ensures
            ret.inv(),
            ret@ =~~= Seq::empty(),
            ret.is_constant(),
    {
        LinkedList {
            ptrs: Ghost(Seq::empty()),
            perms: Tracked(Map::tracked_empty()),
            head: INVALID_ADDR,
        }
    }
}

} // verus!
verus! {

impl<T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> LinkedList<T> {
    /// Return `true` if the list is empty
    pub fn is_empty(&self) -> (ret: bool)
        requires
            self.inv(),
        ensures
            ret == (self@.len() == 0),
    {
        !self.head.check_valid_addr(size_of::<Node<T>>())
    }
}

} // verus!
verus! {

impl<T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> SpecDefault for LinkedList<T> {
    spec fn spec_default() -> Self;
}

} // verus!
verus! {

impl<T> LinkedList<T> where T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte> {
    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_default()
        ensures
            (#[trigger] Self::spec_default()).is_constant(),
            Self::spec_default()@.len() == 0,
    {
    }

    /// Push `ptr` to the front of the list
    pub fn push(&mut self, ptr: SnpPPtr<Node<T>>, Tracked(perm): Tracked<SnpPointsTo<Node<T>>>)
        requires
            old(self).spec_valid_item(ptr, perm),
            (*old(self)).inv(),
            ptr.is_constant(),
            perm@.value().get_Some_0().next.is_constant(),
            perm@.value().is_Some(),
        ensures
            (*self).inv(),
            self@ === old(self)@.push(
                SpecListItem { ptr, snp: perm@.snp(), val: perm@.value().get_Some_0().val },
            ),
    {
        self.insert(SnpPPtr::nullptr(), ptr, Ghost(self@.len() as int), Tracked(perm));
    }

    pub open spec fn spec_valid_item(
        &self,
        ptr: SnpPPtr<Node<T>>,
        perm: SnpPointsTo<Node<T>>,
    ) -> bool {
        let next = perm@.value().get_Some_0().next;
        &&& perm@.ptr_not_null_private_wf(
            ptr,
        )
        //&&& next.spec_valid_addr_with(spec_size::<Node<T>>())

    }

    pub open spec fn spec_pop(
        new: Self,
        olds: Self,
        ret: Option<(SnpPPtr<Node<T>>, Tracked<SnpPointsTo<Node<T>>>)>,
    ) -> bool {
        let len = olds@.len();
        &&& if let Some(ptr) = ret {
            &&& len > 0
            &&& new@ === olds@.drop_last()
            &&& olds@.last().ptr.id() === ptr.0.id()
            &&& olds@.last().snp === ptr.1@@.snp()
            &&& olds@.last().val === ptr.1@@.value().get_Some_0().val
            &&& new.spec_valid_item(ptr.0, ptr.1@)
        } else {
            &&& len == 0
            &&& olds === new
        }
    }

    pub open spec fn spec_pop2(
        new: Self,
        olds: Self,
        ret: Option<(SnpPPtr<Node<T>>, Tracked<SnpPointsTo<Node<T>>>)>,
    ) -> bool {
        let len = olds@.len();
        &&& if let Some(ptr) = ret {
            &&& len > 0
            &&& new@ === olds@.drop_last()
            &&& olds@.last().ptr.id() === ptr.0.id()
            &&& olds@.last().snp === ptr.1@@.snp()
            &&& olds@.last().val
                === ptr.1@@.value().get_Some_0().val
            //&&& new.spec_valid_item(ptr.0, ptr.1@)

        } else {
            &&& len == 0
            &&& olds === new
        }
    }

    pub closed spec fn spec_node(&self, i: nat) -> Node<T> {
        self.perms@[i]@.value().get_Some_0()
    }

    #[verifier(inline)]
    pub open spec fn spec_index_of(&self, nodeptr: SnpPPtr::<Node<T>>) -> int {
        self._spec_index_of(nodeptr.id())
    }

    pub open spec fn _spec_index_of(&self, id: int) -> int {
        if self@.len() > 0 && self.head == id {
            (self@.len() - 1)
        } else {
            choose|i: int| id == self@[i].ptr.id() && 0 <= i < self@.len()
        }
    }

    pub open spec fn _spec_has_index_of(&self, nodeptr: int) -> bool {
        &&& self@.len() > 0
        &&& exists|i| nodeptr == self@[i].ptr.id() && 0 <= i < self@.len()
    }

    pub open spec fn spec_has_index_of(&self, nodeptr: SnpPPtr::<Node<T>>) -> bool {
        self._spec_has_index_of(nodeptr.id())
    }

    pub fn head_ptr(&self) -> (ret: SnpPPtr<Node<T>>)
        requires
            self.inv(),
        ensures
            ret.uptr === self.head,
            ret.is_constant(),
            self@.len() > 0 ==> self@.last().ptr.id() == ret.id(),
            self@.len() > 0 ==> ret.not_null(),
            (self@.len() == 0) == (ret.is_null()),
    {
        SnpPPtr::from_usize(self.head)
    }

    pub open spec fn reverse_index(&self, i: int) -> int {
        self@.len() - i - 1
    }

    pub fn pop(&mut self) -> (ret: Option<(SnpPPtr<Node<T>>, Tracked<SnpPointsTo<Node<T>>>)>)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            Self::spec_pop2(*self, *old(self), ret),
            Self::spec_pop(*self, *old(self), ret),
    {
        if self.is_empty() {
            return None
        } else {
            let ghost i = (self.ptrs@.len() - 1) as nat;
            proof {
                assert(self.ptrs@.len() != 0);
                assert(self.wf_perm(i));
                assert(self.wf_head());
                if i > 0 {
                    assert(self.wf_perm((i - 1) as nat));
                }
                assert(self.ptrs@.last().ptr.id() == self.perms@[i]@.pptr());
                assert(self.head == old(self).ptrs@.last().ptr.id());
            }
            // Advance head pointer
            let tracked first_perm = self.perms.borrow_mut().tracked_remove(i);
            let headptr = SnpPPtr::<Node<T>>::from_usize(self.head);
            proof {
                assert(self.head == first_perm@.pptr());
                assert(headptr.id() == first_perm@.pptr());
            }
            let ret = self.head;
            self.head = headptr.borrow(Tracked(&first_perm)).next;
            proof {
                assert(ret == old(self).ptrs@.last().ptr.id());
                self.ptrs@ = self.ptrs@.drop_last();
                assert(self.wf_perms()) by {
                    assert forall|i: nat| 0 <= i < self.ptrs@.len() implies self.wf_perm(i) by {
                        assert(i < old(self).ptrs@.len());
                        assert(old(self).wf_perm(i));
                    }
                }
                assert(self.wf_head()) by {
                    if self.ptrs@.len() == 0 {
                    } else {
                        assert(self.head == self.ptrs@.last().ptr.id());
                    }
                }
            }
            let ret = Some((SnpPPtr::from_usize(ret), Tracked(first_perm)));
            proof {
                assert(self.ptrs@ === old(self).ptrs@.drop_last());
                assert(ret.get_Some_0().0.id() == ret.get_Some_0().1@@.pptr());
                assert(ret.get_Some_0().1@ === old(self).perms@[(old(self).ptrs@.len()
                    - 1) as nat]);
            }
            // Strange: Need to call wf and is_constant explicitly to ensure tracked is true.
            assert(ret.get_Some_0().1.wf());
            assert(ret.get_Some_0().1.is_constant());
            ret
        }
    }

    pub fn remove_iter<F: FnOnce(SnpPPtr<Node<T>>) -> bool + core::marker::Copy>(
        &mut self,
        cond_fn: F,
        max_len: usize,
    ) -> (ret: (Self, Ghost<Seq<int>>, Ghost<Seq<int>>))
        requires
            old(self).inv(),
            forall|var: SnpPPtr<Node<T>>| var.is_constant() ==> cond_fn.requires((var,)),
        ensures
            self.inv(),
            ret.0@.len() <= max_len as nat,
            ret.0@.len() < max_len as nat ==> forall|k: int|
                0 <= k < self@.len() ==> cond_fn.ensures((self@[k].ptr,), false),
            forall|k: int| 0 <= k < ret.0@.len() ==> cond_fn.ensures((ret.0@[k].ptr,), true),
            is_subseq_via_index(ret.0@, old(self)@, ret.1@),
            is_subseq_via_index(self@, old(self)@, ret.2@),
            (ret.0@.len() == 0) ==> old(self) === self,
            ret.0@.len() == 1 ==> self@ =~~= old(self)@.remove(ret.1@[0]),
            ret.0.inv(),
    {
        let mut prev_ptr: SnpPPtr<Node<T>> = SnpPPtr::nullptr();
        let mut cur_ptr: SnpPPtr<Node<T>> = SnpPPtr::from_usize(self.head);
        let ghost mut d: int = 0;
        let mut ret = Self::new();
        let ghost mut keep_idx = Seq::new(self@.len(), |i: int| i);
        let ghost mut removed_idx = Seq::empty();
        let mut removed: usize = 0;
        if self.is_empty() {
            return (ret, Ghost(removed_idx), Ghost(keep_idx));
        }
        proof {
            proof_empty_is_subs(old(self)@);
            assert(removed.is_constant());
            assert(max_len.is_constant());
        }
        //&& removed < max_len
        while cur_ptr.check_valid() && removed < max_len
            invariant
                self.inv(),
                ret.inv(),
                forall|var: SnpPPtr<Node<T>>| var.is_constant() ==> cond_fn.requires((var,)),
                old(self).is_constant(),
                self.is_constant(),
                removed.is_constant(),
                max_len.is_constant(),
                cur_ptr.is_constant(),
                prev_ptr.is_constant(),
                ret.is_constant(),
                if d < self@.len() {
                    cur_ptr.id() == self@[self@.len() - d - 1].ptr.id()
                } else {
                    cur_ptr.is_null()
                },
                d > 0 ==> prev_ptr.id() == self@[self@.len() - d].ptr.id(),
                d == 0 ==> prev_ptr.is_null(),
                removed <= max_len,
                removed == ret@.len(),
                old(self)@.len() != 0,
                removed as nat + self@.len() == old(self)@.len(),
                0 <= d <= self@.len(),
                (d == self@.len()) == (cur_ptr.is_null()),
                keep_idx.len() + removed_idx.len() == old(self)@.len(),
                removed_idx.len() == removed as nat,
                forall|k: int|
                    self@.len() - d <= k < self@.len() ==> cond_fn.ensures((self@[k].ptr,), false),
                forall|k: int| 0 <= k < ret@.len() ==> cond_fn.ensures((ret@[k].ptr,), true),
                is_subseq_via_index(self@, old(self)@, keep_idx),
                is_subseq_via_index(ret@, old(self)@, removed_idx),
                ret@.len() == 0 ==> (old(self) === self && keep_idx === Seq::new(
                    self@.len(),
                    |i: int| i,
                ) && removed_idx === Seq::empty()),
                ret@.len() == 1 ==> self@ =~~= old(self)@.remove(removed_idx[0]),
        {
            let ghost prev_self = *self;
            let ghost prev_ret = ret;
            let ghost i = self@.len() - d - 1;
            proof {
                self.wf_perm(0);
                assert(self.wf_head());
                assert(0 <= i < self@.len());
                assert(self.wf_perm(i as nat));
                if i + 1 < self@.len() {
                    assert(self.wf_perm((i + 1) as nat));
                }
                if i > 0 {
                    assert(self.wf_perm((i - 1) as nat));
                }
                assert(self.perms@ =~~= self.perms@.remove(i as nat).insert(
                    i as nat,
                    self.perms@[i as nat],
                ));
            }
            assert(self.wf_perm(i as nat));
            assert(self@[i].ptr.id() === cur_ptr.id());
            let tracked cur_perm = self.perms.borrow_mut().tracked_remove(i as nat);
            let next = cur_ptr.borrow(Tracked(&cur_perm)).next;
            proof {
                self.perms.borrow_mut().tracked_insert(i as nat, cur_perm);
                assert(self@[i].ptr.id() === cur_ptr.id());
                assert(self@ =~~= prev_self@);
            }
            let cptr = cur_ptr.clone();
            assert(cptr === cur_ptr);
            assert(cond_fn.requires((cptr,)));
            if cond_fn(cptr) {
                assert(self.head != INVALID_ADDR);
                let prevptr = prev_ptr.clone();
                assert(prevptr === prev_ptr);
                if let Option::Some((cur_ptr, cur_perm)) = self._remove(
                    prevptr,
                    cur_ptr,
                    Ghost(i),
                ) {
                    let ghost (mut keep, mut removeditems) = (prev_self@, ret@);
                    let ghost cur_ptr_perm = SpecListItem {
                        ptr: cur_ptr,
                        snp: cur_perm@@.snp(),
                        val: cur_perm@@.value().get_Some_0().val,
                    };
                    proof {
                        assert(self@ =~~= prev_self@.remove(i));
                        if removed == 0 {
                            assert(keep_idx[i] == i);
                        }
                        proof_remove_keep(
                            old(self)@,
                            keep,
                            removeditems,
                            &mut keep_idx,
                            &mut removed_idx,
                            i,
                        );
                        if removed_idx.len() == 1 {
                            assert(removed_idx[removed_idx.len() - 1] == i);
                        }
                    }
                    assert(cur_ptr.id() === old(self)@[removed_idx.last()].ptr.id());
                    assert(cur_ptr === old(self)@[removed_idx.last()].ptr) by {
                        cur_ptr.axiom_id_equal(old(self)@[removed_idx.last()].ptr);
                    }
                    ret.push(cur_ptr, cur_perm);
                    removed = removed + 1;
                    proof {
                        d = d - 1;
                    }
                } else {
                    assert(false);
                }
            } else {
                prev_ptr = SnpPPtr::from_usize(cur_ptr.to_usize());
                proof {
                    assert(self@[i].ptr.id() === cur_ptr.id());
                    self@[i].ptr.axiom_id_equal(cur_ptr);
                    assert(cur_ptr === self@[i].ptr);
                    assert(cond_fn.ensures((cur_ptr,), false));
                }
            }
            cur_ptr = SnpPPtr::from_usize(next);
            proof {
                d = d + 1;
                let ghost i = self@.len() - d - 1;
                assert forall|k: int| i < k < self@.len() implies cond_fn.ensures(
                    (self@[k].ptr,),
                    false,
                ) by {
                    if self@.len() != prev_self@.len() {
                        assert(prev_self@.len() == self@.len() + 1);
                        assert(i + 1 < k + 1 < prev_self@.len());
                        assert(prev_self@[k + 1] === self@[k]);
                        assert(cond_fn.ensures((prev_self@[k + 1].ptr,), false));
                    }
                }
                assert forall|k: int| 0 <= k < ret@.len() implies cond_fn.ensures(
                    (ret@[k].ptr,),
                    true,
                ) by {
                    if ret@.len() != prev_ret@.len() {
                        assert(prev_ret@.len() == ret@.len() - 1);
                        if (0 <= k < prev_ret@.len()) {
                            assert(prev_ret@[k] === ret@[k]);
                            assert(cond_fn.ensures((prev_ret@[k].ptr,), true));
                        }
                    }
                }
            }
        }
        (ret, Ghost(removed_idx), Ghost(keep_idx))
    }

    fn _remove(
        &mut self,
        prev: SnpPPtr<Node<T>>,
        cur: SnpPPtr<Node<T>>,
        Ghost(i): Ghost<int>,
    ) -> (ret: Option<(SnpPPtr<Node<T>>, Tracked<SnpPointsTo<Node<T>>>)>)
        requires
            1 <= i + 1 <= old(self)@.len(),
            old(self).perms@[i as nat]@.ptr_not_null_private_wf(cur),
            i + 1 < old(self)@.len() ==> old(self).perms@[(i + 1) as nat]@.ptr_not_null_private_wf(
                prev,
            ),
            i + 1 == old(self)@.len() ==> prev.is_null(),
            old(self).inv(),
        ensures
            self.inv(),
            ret.is_Some() ==> self@ =~~= old(self)@.remove(i),
            (old(self)@.len() > 0) ==> self@.len() + 1 == old(self)@.len(),
            (old(self)@.len() == 0) ==> ret.is_None(),
            (old(self)@.len() > 0) ==> ret === Some((cur, ret.get_Some_0().1))
                && ret.get_Some_0().1@ === old(self).perms@[i as nat] && old(self).spec_valid_item(
                cur,
                ret.get_Some_0().1@,
            ),
    {
        if self.is_empty() {
            return None;
        }
        assert(self@.len() >= 1);
        let ghost old_self = *self;
        proof {
            assert(self.inv());
            assert(self.wf_perm(i as nat));
            if prev.not_null() {
                assert(self.wf_perm((i + 1) as nat));
            }
            if (i != 0) {
                assert(self.wf_perm((i - 1) as nat));
            }
        }
        let tracked cur_perm = self.perms.borrow_mut().tracked_remove(i as nat);
        let cur_node = cur.borrow(Tracked(&cur_perm));
        if prev.check_valid() {
            let tracked mut prev_perm = self.perms.borrow_mut().tracked_remove((i + 1) as nat);
            proof {
                assert(prev_perm@.snp() === old_self.perms@[(i + 1) as nat]@.snp());
            }
            let mut prev_node = prev.take(Tracked(&mut prev_perm));
            prev_node.next = cur_node.next;
            prev.put(Tracked(&mut prev_perm), prev_node);
            assert(prev_perm@.snp() === old_self.perms@[(i + 1) as nat]@.snp());
            proof {
                if !cur_node.next.spec_valid_addr_with(spec_size::<Node<T>>()) {
                    assert(i == 0);
                }
                self.perms.borrow_mut().tracked_insert((i + 1) as nat, prev_perm);
            }
        } else {
            self.head = cur_node.next;
        }
        proof {
            self.ptrs@ = self.ptrs@.remove(i);
            assert(self.ptrs@.len() + 1 == old_self.ptrs@.len());
            let convert = |j: nat|
                if j < i {
                    j
                } else {
                    (j + 1) as nat
                };
            let key_map = Map::<nat, nat>::new(
                |j: nat| 0 <= j < self.ptrs@.len(),
                |j: nat| convert(j),
            );
            assert forall|j: nat| key_map.dom().contains(j) implies self.perms@.dom().contains(
                convert(j),
            ) by {
                assert(old(self).wf_perm(convert(j)));
            }
            self.perms.borrow_mut().tracked_map_keys_in_place(key_map);
            assert forall|j: nat| j < self.ptrs@.len() implies self.wf_perm(j) by {
                if j < i {
                    assert(old_self.wf_perm(j));
                } else {
                    assert(old_self.wf_perm(j + 1));
                    assert(self.ptrs@[j as int] === old_self.ptrs@[(j + 1) as int]);
                    assert(self.perms@[i as nat]@.value().get_Some_0().next
                        == old_self.perms@[i as nat]@.value().get_Some_0().next);
                    assert(self.perms@[i as nat]@.pptr() === old_self.perms@[i as nat + 1]@.pptr());
                    assert(self.perms@[i as nat]@.snp() === old_self.perms@[i as nat + 1]@.snp());
                    if j != i {
                        assert(self.perms@[j] === old_self.perms@[j + 1]);
                    }
                }
            }
            assert(self.wf_perms());
            assert(self.wf_head());
            assert(self.wf());
        }
        Some((cur, Tracked(cur_perm)))
    }
}

} // verus!
verismo_simple! {
impl<T> LinkedList<T>
where
    T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>,
{
        // prev: prev node ptr
        // idx: current node index (n - index)
        pub fn remove(&mut self, prev: SnpPPtr<Node<T>>, Ghost(idx): Ghost<int>) -> (ret: Tracked<SnpPointsTo<Node<T>>>)
        requires
            old(self).inv(),
            old(self)@.len() > 0,
            0 <= idx < old(self)@.len(),
            prev.not_null() ==> old(self)@[idx].ptr.not_null(),
            old(self).contains_ptr_at(prev, idx + 1)
        ensures
            self.inv(),
            self@ =~~= old(self)@.remove(
                idx
            ),
            self@.len() == old(self)@.len() - 1,
            ret@@.ptr_not_null_wf(old(self)@[idx].ptr),
            ret@@.value().is_Some(),
            ret@@.snp() === old(self)@[idx].snp,
        {
            let ghost i = idx;
            let ghost old_self = *self;
            proof {
                if prev.not_null() {
                    assert(self.wf_perm((i + 1) as nat));
                }
                assert(self.wf_perm(i as nat));
                if (i != 0) {
                    assert(self.wf_perm((i - 1) as nat));
                }
            }
            let prev_is_null = !prev.check_valid();
            let cur = if prev_is_null {
                self.head_ptr()
            } else {
                self.node_at(prev.clone(), Ghost(i + 1)).next_ptr()
            };
            let next = self.node_at(cur.clone(), Ghost(i)).next;
            if prev_is_null {
                self.head = next;
            } else {
                let tracked mut prev_perm = self.perms.borrow_mut().tracked_remove((i + 1) as nat);
                proof {
                    assert(prev_perm@.snp() === old_self.perms@[(i + 1) as nat]@.snp());
                }
                let Tracked(prev_perm) = prev.set_next(next, Tracked(prev_perm));
                proof{
                    self.perms.borrow_mut().tracked_insert((i + 1) as nat, prev_perm);
                 }
            }
            let tracked cur_perm = self.perms.borrow_mut().tracked_remove(i as nat);
            proof {
                self.ptrs@ = self.ptrs@.remove(i);
                assert(self.ptrs@.len() + 1 == old_self.ptrs@.len());

                let convert = |j: nat| if j < i {j} else {(j+1) as nat};
                let key_map = Map::<nat, nat>::new(
                    |j: nat| 0 <= j < self.ptrs@.len(),
                    |j: nat| convert(j)
                );
                assert forall |j: nat|
                    key_map.dom().contains(j)
                implies
                    self.perms@.dom().contains(convert(j))
                by {
                    assert(old(self).wf_perm(convert(j)));
                }
                let prev_perms = self.perms;
                self.perms.borrow_mut().tracked_map_keys_in_place(
                    key_map
                );

                if prev.not_null() {
                    assert(self.perms@[i as nat] === prev_perms@[(i + 1) as nat]);
                    assert(self.perms@[i as nat]@.value().get_Some_0().next == old_self.perms@[i as nat]@.value().get_Some_0().next);
                    assert(self.perms@[i as nat]@.pptr() === old_self.perms@[i as nat + 1]@.pptr());
                    assert(self.perms@[i as nat]@.snp() === old_self.perms@[i as nat+ 1]@.snp());
                }

                assert forall |j: nat| j < self.ptrs@.len()
                implies self.wf_perm(j)
                by {
                    if j < i {
                        assert(old_self.wf_perm(j));
                    } else {
                        assert(old_self.wf_perm(j + 1));
                        assert(self.ptrs@[j as int] === old_self.ptrs@[(j + 1) as int]);
                        if j != i {
                            assert(self.perms@[j] === old_self.perms@[j + 1]);
                        }
                    }
                }
                assert(self.wf_perms());
                assert(self.wf_head());
                assert(self.wf());
            }
            Tracked(cur_perm)
        }

        pub fn insert(&mut self, prev_ptr: SnpPPtr<Node<T>>,
            ptr: SnpPPtr::<Node<T>>, Ghost(idx): Ghost<int>,
            Tracked(perm): Tracked<SnpPointsTo<Node<T>>>)
        requires
            old(self).spec_valid_item(ptr, perm),
            (*old(self)).inv(),
            ptr.is_constant(),
            perm@.value().get_Some_0().next.is_constant() == old(self).head.is_constant(),
            ptr.uptr.is_constant() == old(self).head.is_constant(),
            perm@.value().is_Some(),
            old(self).contains_ptr_at(prev_ptr, idx),
        ensures
            (prev_ptr.not_null()) ==> (self@ =~~= old(self)@.insert(
            idx,
            SpecListItem{ptr: ptr, snp: perm@.snp(), val: perm@.value().get_Some_0().val})),
            prev_ptr.is_null() ==> self@ =~~= old(self)@.push(
                SpecListItem{ptr: ptr, snp: perm@.snp(), val: perm@.value().get_Some_0().val}),
            self@.len() == old(self)@.len() + 1,
            self.inv(),
        {
            let ghost i = idx as nat;
            let prev_is_null = !prev_ptr.check_valid();
            proof {
                if prev_ptr.not_null() {
                    assert(self.wf_perm(i));
                }
                if i > 0 {
                    assert(self.wf_perm((i - 1) as nat));
                }
            }
            let ghost old_perm = perm;
            let ghost old_self = *self;
            let ghost oldlen = self.ptrs@.len();
            let next = if prev_is_null {
                self.head
            } else {
                self.node_at(prev_ptr.clone(), Ghost(i as int)).next
            };
            let Tracked(perm) = ptr.set_next(next, Tracked(perm));
            if prev_is_null {
                self.head = ptr.to_usize();
            } else {
                let tracked prev_perm = self.perms.borrow_mut().tracked_remove(i);
                let Tracked(prev_perm) = prev_ptr.set_next(ptr.to_usize(), Tracked(prev_perm));
                proof {
                    self.perms.borrow_mut().tracked_insert(i as nat, prev_perm);
                }
            };
            proof {
                self.perms.borrow_mut().tracked_insert(self.ptrs@.len(), perm);
                assert(self@ =~~= old_self@);
                let ghost tmp_perms = self.perms;
                self.ptrs@ = self.ptrs@.insert(i as int,
                    SpecListItem{ptr: ptr, snp: old_perm@.snp(), val: old_perm@.value().get_Some_0().val});
                let convert = |j: nat|
                    if j < i {j} else if j == i {(self.ptrs@.len() - 1) as nat} else {(j-1) as nat};

                let key_map = Map::<nat, nat>::new(
                    |j: nat| 0 <= j < self.ptrs@.len(),
                    |j: nat| convert(j)
                );
                assert forall |j: nat|
                    key_map.dom().contains(j)
                implies
                    self.perms@.dom().contains(convert(j))
                by {
                    if j != i {
                        assert(old(self).wf_perm(convert(j)));
                    }
                }
                self.perms.borrow_mut().tracked_map_keys_in_place(
                    key_map
                );

                assert(self.perms@[i] === perm);
                if i > 0 {
                    assert(self.perms@[i].view().value().get_Some_0().next as int == self.ptrs@[i-1 as int].ptr.id());
                }
                assert(self.wf_perm(i));

                assert forall |j: nat| j < self.ptrs@.len()
                implies self.wf_perm(j)
                by {
                    if j < i {
                        assert(old_self.wf_perm(j));
                    } else if j == i {
                        assert(self.wf_perm(i));
                    } else {
                        assert(old_self.wf_perm((j - 1) as nat));
                        assert(self.ptrs@[j as int] === old_self.ptrs@[(j - 1) as int]);
                        assert(self.perms@[j as nat]@.snp() === old_self.perms@[(j - 1) as nat]@.snp());
                        assert(self.perms@[j as nat]@.pptr() === old_self.perms@[(j - 1) as nat]@.pptr());
                        assert(prev_ptr.not_null());
                        if j != i + 1 {
                            assert(self.perms@[j] === old_self.perms@[(j - 1) as nat]);
                            assert(self.wf_perm(j));
                        } else {
                            assert(self.perms@[j] === tmp_perms@[i]);
                            assert(self.perms@[i] === tmp_perms@[(self@.len() - 1) as nat]);
                            assert(self.wf_perm(j));
                        }
                    }
                }
                assert(self.wf_perms());
                assert(self.wf_head());
                assert(self.wf());
            }
        }
    }
}

verismo_simple! {
    impl<T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> Default for LinkedList<T> {
        fn default() -> (ret: Self)
        ensures
            ret.inv(),
            ret@.len() == 0,
            ret.is_constant(),
        {
            LinkedList::new()
        }
    }
}

verismo_simple! {
impl<T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> LinkedList<T> {
    pub fn head_node(&self) -> (ret: &Node<T>)
    requires
        self.inv(),
        self@.len() > 0 ,
    ensures
        ret.val === self@[self@.len() - 1].val,
        ret.next.spec_valid_addr_with(spec_size::<Node<T>>()) ==>
            ret.next == self@[self@.len() - 2].ptr.id(),
        ret.wf(),
    {
        let nodeptr = SnpPPtr::<Node<T>>::from_usize(self.head);
        let ghost i = self@.len() - 1;
        proof {
            assert(nodeptr.id() == self@[i].ptr.id());
            assert(self.wf_perm(i as nat))
        }
        self.node_at(nodeptr, Ghost(i))
    }

    pub fn node_at(&self, nodeptr: SnpPPtr::<Node<T>>, Ghost(i): Ghost<int>) -> (ret: &Node<T>)
    requires
        self.inv(),
        nodeptr.not_null(),
        nodeptr.is_constant(),
        0 <= i < self@.len(),
        self@[i].ptr.id() == nodeptr.id(),
    ensures
        ret.next.is_constant(),
        ret === &self.spec_node(i as nat),
        i > 0 ==> (
            ret.next == self@[i - 1].ptr.id()),
        i == 0 ==> !ret.next.spec_valid_addr_with(spec_size::<Node<T>>()),
        (i > 0) == (ret.next.spec_valid_addr_with(spec_size::<Node<T>>())),
        ret.val === self@[i].val,
        ret.wf(),
    {
        //let ghost i = self.spec_index_of(*nodeptr);
        proof {
            //assert(0 <= i < self@.len());
            //assert(self@[i].ptr.id() == nodeptr.id());
            assert(self.wf_perm(i as nat));
            //assert(self.perms@[i as nat]@.ptr_not_null_wf(self@[i].ptr));
            if i > 0 {
                assert(self.wf_perm((i - 1) as nat));
            }
        }
        let tracked node_perm = self.perms.borrow().tracked_borrow(i as nat);
        nodeptr.borrow(Tracked(node_perm))
    }

    pub fn update_node_at(&mut self, Ghost(i): Ghost<int>, nodeptr: SnpPPtr::<Node<T>>, v: T)
    requires
        old(self).inv(),
        0 <= i < old(self)@.len() && old(self)@[i].ptr.id() == nodeptr.id(),
        nodeptr.not_null(),
        nodeptr.is_constant(),
        v.wf(),
    ensures
        self@ =~~= old(self)@.update(i, SpecListItem{ptr: old(self)@[i].ptr,  snp: old(self)@[i].snp, val: v}),
        self.inv(),
    {
        let ghost prev = *self;
        let ghost i = i as nat;
        //let ghost i = self.spec_index_of(*nodeptr) as nat;
        proof {
            assert(self.wf_perm(i));
        }
        let node = self.node_at(nodeptr.clone(), Ghost(i as int));
        let next = node.next;
        let tracked mut perm = self.perms.borrow_mut().tracked_remove(i);
        nodeptr.replace(Tracked(&mut perm), Node{val: v, next});
        proof {
            self.ptrs@ = self@.update(i as int, SpecListItem{ptr: self@[i as int].ptr,  snp: self@[i as int].snp, val: v});
            self.perms.borrow_mut().tracked_insert(i, perm);
            assert forall |k: nat|
                0 <= k < self@.len() && k != i
            implies
                self@[k as int] === prev@[k as int]
            by{
                assert(prev.wf_perm(k));
                assert(self.perms@[k] === prev.perms@[k]);
            }
            assert forall |k: nat|
                0 <= k < self@.len()
            implies
                self.wf_perm(k)
            by {
                if k < self@.len() - 1 {
                    assert(prev.wf_perm((k + 1) as nat));
                }
                assert(prev.wf_perm(k));
                if k != i {
                    assert(self.wf_perm(k));
                } else {
                    if i > 0 {
                        assert(self@[i - 1] === prev@[i - 1]);
                        assert(self@[i - 1].ptr.id() === prev@[i - 1].ptr.id());
                        assert(self@[i - 1].snp === prev@[i - 1].snp);
                    }
                    assert(self.perms@[i] === perm);
                    assert(self.perms@[i]@.value().get_Some_0().val === v);
                    assert(self.perms@[i]@.value().get_Some_0().next === prev.perms@[i]@.value().get_Some_0().next);
                    assert(self.wf_perm(i));
                }
            }
        }
    }
}
}
