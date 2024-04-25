use core::mem::size_of;

use super::*;
use crate::addr_e::AddrTrait;
use crate::arch::addr_s::GVA;
use crate::linkedlist::{LinkedList, Node, SpecListItem};
use crate::ptr::*;

crate::macro_const! {
    #[macro_export]
    pub const MIN_ADDR_ALIGN: usize = 8usize;
    #[macro_export]
    pub const ORDER: usize = 32usize;
    pub const ORDER_USIZE: usize = ORDER!() as usize;
    //ORDER as usize;
}

verismo_simple! {
pub struct BuddyAllocator {
    perms: Tracked<Map<(nat, nat), SnpPointsToRaw>>,
    // Use the last bytes of each mem range to store nodes
    free_lists: Array<LinkedList<()>, ORDER_USIZE>,
}

pub ghost struct SpecBuddyAllocator{
    pub perms: Map<(nat, nat), SnpPointsToRaw>,
    // Use the last bytes of each mem range to store nodes
    pub free_lists: Seq<LinkedList<()>>,
}
}

verus! {

impl BuddyAllocator {
    pub closed spec fn view(&self) -> SpecBuddyAllocator {
        SpecBuddyAllocator { perms: self.perms@, free_lists: self.free_lists@ }
    }
}

impl SpecBuddyAllocator {
    pub open spec fn valid_bucket(bucket: nat) -> bool {
        &&& bucket < ORDER!()
        &&& spec_bit64(spec_cast_integer::<_, u64>(bucket)) >= MIN_ADDR_ALIGN!()
    }

    pub open spec fn wf_bucket(&self, bucket: nat) -> bool {
        //&&& self.free_lists[bucket as int].is_Some()
        &&& self.free_lists[bucket as int].inv()
        &&& self.free_lists[bucket as int].is_constant()
    }

    pub open spec fn wf_perm(&self, bucket: nat, i: nat) -> bool {
        if (bucket < self.free_lists.len() && i < self.free_lists[bucket as int]@.len()) {
            let SpecListItem { ptr: node_ptr, snp: node_snp, val } =
                self.free_lists[bucket as int]@[i as int];
            let perm = self.perms[(bucket, i)]@;
            let size: nat = spec_bit64(bucket as u64) as nat;
            &&& self.perms.contains_key((bucket, i))
            &&& perm.wf_freemem((node_ptr.id() + MIN_ADDR_ALIGN!(), perm.size()))
            &&& node_snp === SwSnpMemAttr::spec_default()
            &&& node_ptr.not_null()
            &&& node_ptr.uptr.spec_valid_addr_with(size)
            &&& perm.size() + MIN_ADDR_ALIGN!() == size
        } else {
            !self.perms.contains_key((bucket, i))
        }
    }

    pub open spec fn wf_before_validate_write(&self) -> bool {
        &&& self.free_lists.len() == ORDER
        &&& forall|b: nat| b < self.free_lists.len() ==> self.wf_bucket(b)
        &&& forall|b: nat, i: nat| #[trigger] self.wf_perm(b, i)
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.wf_before_validate_write()
    }

    pub open spec fn spec_pop_or_push_element(&self, old_self: Self, bucket: nat) -> bool {
        let list = self.free_lists[bucket as int];
        let old_list = old_self.free_lists[bucket as int];
        &&& list@ =~~= old_list@.drop_last()
        &&& old_list@ =~~= list@.push(old_list@.last())
        &&& self.free_lists =~~= old_self.free_lists.update(bucket as int, list)
        &&& self.perms =~~= old_self.perms.remove((bucket, list@.len()))
    }

    pub open spec fn spec_add_one_to_bucket(
        &self,
        old_self: &Self,
        bucket: nat,
        nodeptr: SnpPPtr<Node<()>>,
        node_perm: SnpPointsTo<Node<()>>,
        free_perm: SnpPointsToRaw,
    ) -> bool {
        let size = spec_bit64(bucket as u64) as nat;
        &&& self.wf_bucket(bucket as nat)
        &&& old_self.wf_bucket(bucket as nat)
        &&& Self::valid_bucket(bucket)
        &&& old_self.free_lists.len() == ORDER
        &&& self.free_lists.len() == ORDER
        &&& node_perm@.ptr_not_null_wf(nodeptr)
        &&& node_perm@.snp() === SwSnpMemAttr::spec_default()
        &&& nodeptr.uptr.spec_valid_addr_with(size)
        &&& free_perm@.size() + MIN_ADDR_ALIGN!() == size
        &&& free_perm@.wf_freemem((nodeptr.id() + MIN_ADDR_ALIGN!(), free_perm@.size()))
        &&& free_perm@.snp() === SwSnpMemAttr::spec_default()
    }

    pub open spec fn spec_add_one_to_bucket2(
        &self,
        old_self: &Self,
        bucket: nat,
        nodeptr: SnpPPtr<Node<()>>,
        node_perm: SnpPointsTo<Node<()>>,
        free_perm: SnpPointsToRaw,
    ) -> bool {
        let list = old_self.free_lists[bucket as int];
        let oldlen = list@.len();
        let newlist = self.free_lists[bucket as int];
        &&& self.perms =~~= old_self.perms.insert((bucket, oldlen), free_perm)
        &&& self.perms.remove((bucket, oldlen)) =~~= old_self.perms
        &&& self.free_lists =~~= old_self.free_lists.update(
            bucket as int,
            self.free_lists[bucket as int],
        )
        &&& newlist@ =~~= list@.push(
            SpecListItem {
                ptr: nodeptr,
                snp: node_perm@.snp(),
                val: node_perm@.value().get_Some_0().val,
            },
        )
    }

    pub proof fn proof_add_one_to_bucket(
        &self,
        old_self: &Self,
        bucket: nat,
        nodeptr: SnpPPtr<Node<()>>,
        node_perm: SnpPointsTo<Node<()>>,
        free_perm: SnpPointsToRaw,
    )
        requires
            self.spec_add_one_to_bucket(old_self, bucket, nodeptr, node_perm, free_perm),
            self.spec_add_one_to_bucket2(old_self, bucket, nodeptr, node_perm, free_perm),
        ensures
            old_self.inv() == self.inv(),
    {
        let list = old_self.free_lists[bucket as int];
        let oldlen = list@.len();
        if old_self.inv() {
            assert(self.inv()) by {
                //assert((*self).sec_label() === SecLevel::Low) by {
                //reveal_with_fuel(Array::<LinkedList<()>, ORDER_USIZE>::sec_label_from_array, 32);
                //}
                assert forall|b: nat| b < self.free_lists.len() implies self.wf_bucket(b) by {
                    assert(self.wf_bucket(bucket as nat));
                    /*if b != bucket {
                    assert(self.free_lists[b as int] === old_self.free_lists[b as int]);
                }*/
                    assert(old_self.wf_bucket(b));
                    //assert(self.free_lists[b as int].is_Some());
                    //assert(self.free_lists[b as int].wf());
                    //assert(self.free_lists[b as int].is_constant());
                }
                assert forall|b: nat, i: nat| #[trigger] self.wf_perm(b, i) by {
                    assert(old_self.wf_perm(b, i));
                    if b < ORDER && i < self.free_lists[b as int]@.len() {
                        assert(self.wf_perm(b, i));
                    } else {
                        assert(self.wf_perm(b, i));
                    }
                }
            }
        }
        if self.inv() {
            assert(old_self.inv()) by {
                assert forall|b: nat| b < old_self.free_lists.len() implies old_self.wf_bucket(
                    b,
                ) by {
                    assert(self.wf_bucket(b));
                }
                assert forall|b: nat, i: nat| #[trigger] old_self.wf_perm(b, i) by {
                    assert(self.wf_perm(b, i));
                }
            }
        }
    }

    pub open spec fn spec_remove_or_insert_one(
        &self,
        old_self: Self,
        bucket: nat,
        idx: nat,
    ) -> bool {
        let list = self.free_lists[bucket as int];
        let old_list = old_self.free_lists[bucket as int];
        &&& list@ =~~= old_list@.remove(idx as int)
        &&& old_list@ =~~= list@.push(old_list@[idx as int])
        &&& self.free_lists =~~= old_self.free_lists.update(bucket as int, list)
        &&& self.perms =~~= old_self.perms.remove((bucket, idx))
    }

    pub open spec fn _spec_remove_or_insert_one(
        &self,
        old_self: &Self,
        bucket: nat,
        idx: nat,
        nodeptr: SnpPPtr<Node<()>>,
        node_perm: SnpPointsTo<Node<()>>,
        free_perm: SnpPointsToRaw,
    ) -> bool {
        let size = spec_bit64(bucket as u64) as nat;
        &&& self.wf_bucket(bucket as nat)
        &&& old_self.wf_bucket(bucket as nat)
        &&& Self::valid_bucket(bucket)
        &&& old_self.free_lists.len() == ORDER
        &&& self.free_lists.len() == ORDER
        &&& node_perm@.ptr_not_null_wf(nodeptr)
        &&& node_perm@.snp() === SwSnpMemAttr::spec_default()
        &&& nodeptr.uptr.spec_valid_addr_with(size)
        &&& free_perm@.size() + MIN_ADDR_ALIGN!() == size
        &&& free_perm@.wf_freemem((nodeptr.id() + MIN_ADDR_ALIGN!(), free_perm@.size()))
        &&& free_perm@.snp() === SwSnpMemAttr::spec_default()
    }

    pub open spec fn _spec_remove_or_insert_one2(
        &self,
        old_self: &Self,
        bucket: nat,
        idx: nat,
        nodeptr: SnpPPtr<Node<()>>,
        node_perm: SnpPointsTo<Node<()>>,
        free_perm: SnpPointsToRaw,
    ) -> bool {
        let list = old_self.free_lists[bucket as int];
        let oldlen = list@.len();
        let newlist = self.free_lists[bucket as int];
        //&&& old_self.perms.dom().insert((bucket as nat, oldlen)) =~~= self.perms.dom()
        &&& self.perms.contains_key((bucket as nat, oldlen))
        &&& self.perms.dom().remove((bucket as nat, oldlen)) === old_self.perms.dom()
        &&& old_self.perms =~~= Map::new(
            |key| old_self.perms.contains_key(key),
            |k: (nat, nat)|
                if k.0 != bucket || k.1 < idx {
                    self.perms[k]
                } else {
                    self.perms[(k.0, (k.1 + 1) as nat)]
                },
        )
        &&& self.perms[(bucket, idx)]
            === free_perm/* &&& self.perms =~~= Map::new(
            |key| self.perms.contains_key(key),
            |k: (nat, nat)| if k.0 != bucket || k.1 < idx {old_self.perms[k]} else if k.1 > idx {old_self.perms[(k.0, (k.1 - 1) as nat)]} else {free_perm}
        )*/

        &&& self.free_lists =~~= old_self.free_lists.update(
            bucket as int,
            self.free_lists[bucket as int],
        )
        &&& newlist@ =~~= list@.insert(
            idx as int,
            SpecListItem {
                ptr: nodeptr,
                snp: node_perm@.snp(),
                val: node_perm@.value().get_Some_0().val,
            },
        )  //
        //&&& newlist@ =~~= list@.subrange(0, idx as int).push(SpecListItem {ptr: nodeptr, snp: node_perm@.snp()}) + list@.subrange(idx as int, list@.len() as int)

    }

    pub proof fn proof_remove_or_add_idx(
        &self,
        old_self: &Self,
        bucket: nat,
        idx: nat,
        nodeptr: SnpPPtr<Node<()>>,
        node_perm: SnpPointsTo<Node<()>>,
        free_perm: SnpPointsToRaw,
    )
        requires
            self._spec_remove_or_insert_one(old_self, bucket, idx, nodeptr, node_perm, free_perm),
            self._spec_remove_or_insert_one2(old_self, bucket, idx, nodeptr, node_perm, free_perm),
            idx <= old_self.free_lists[bucket as int]@.len(),
            idx < self.free_lists[bucket as int]@.len(),
        ensures
            old_self.inv() == self.inv(),
    {
        let list = old_self.free_lists[bucket as int];
        let oldlen = list@.len();
        let newlist = self.free_lists[bucket as int];
        let newlen = newlist@.len();
        let left = list@.subrange(0, idx as int).push(
            SpecListItem {
                ptr: nodeptr,
                snp: node_perm@.snp(),
                val: node_perm@.value().get_Some_0().val,
            },
        );
        let right = list@.subrange(idx as int, list@.len() as int);
        assert(left.len() == idx + 1);
        assert(right.len() == oldlen - idx);
        assert(oldlen + 1 == self.free_lists[bucket as int]@.len());
        if old_self.inv() {
            assert(self.inv()) by {
                assert forall|b: nat| b < self.free_lists.len() implies self.wf_bucket(b) by {
                    assert(self.wf_bucket(bucket as nat));
                    assert(old_self.wf_bucket(b));
                }
                assert forall|b: nat, i: nat| #[trigger] self.wf_perm(b, i) by {
                    assert(old_self.wf_perm(b, i));
                    if b < ORDER && self.perms.contains_key((b, i)) {
                        if b != bucket || i < idx {
                            assert(idx <= oldlen);
                            assert((b, i) !== (bucket, oldlen));
                            assert(old_self.perms.contains_key((b, i)));
                            assert(old_self.perms[(b, i)] === self.perms[(b, i)]);
                            assert(self.wf_perm(b, i));
                        } else if idx < i < newlen {
                            assert(old_self.wf_perm(b, (i - 1) as nat));
                            assert(i <= oldlen);
                            assert(old_self.perms.contains_key((b, (i - 1) as nat)));
                            assert(self.wf_perm(b, i));
                        } else {
                            assert(self.perms[(b, i)] === free_perm);
                            assert(self.wf_perm(b, i));
                        }
                    }
                }
            }
        }
        if self.inv() {
            assert(old_self.inv()) by {
                assert forall|b: nat| b < old_self.free_lists.len() implies old_self.wf_bucket(
                    b,
                ) by {
                    assert(self.wf_bucket(b));
                }
                assert forall|b: nat, i: nat| #[trigger] old_self.wf_perm(b, i) by {
                    assert(self.wf_perm(b, i));
                    if b < ORDER && i < old_self.free_lists[b as int]@.len() {
                        assert(i < self.free_lists[b as int]@.len());
                        assert(self.perms.contains_key((b, i)));
                        assert(old_self.perms.contains_key((b, i)));
                        if b != bucket || i < idx {
                            assert(old_self.perms[(b, i as nat)] === self.perms[(b, i)]);
                        } else if idx <= i < oldlen {
                            assert(self.wf_perm(b, i + 1));
                            assert(old_self.perms[(b, i as nat)] === self.perms[(b, i + 1)]);
                        }
                    } else {
                        if self.perms.contains_key((b, i)) {
                            assert(b < ORDER && i < self.free_lists[b as int]@.len());
                            assert(b == bucket);
                            assert(i == oldlen);
                            assert(!old_self.perms.contains_key((b, i)));
                        } else {
                            assert(!old_self.perms.contains_key((b, i)));
                        }
                    }
                }
            }
        }
    }
}

} // verus!
verus! {

pub open spec fn alloc_valid_size(old_size: usize, size: usize) -> bool {
    &&& size >= old_size
    &&& spec_bit64_is_pow_of_2(size as int)
    &&& size >= MIN_ADDR_ALIGN!()
    //&&& size % align == 0

}

} // verus!
verus! {

impl BuddyAllocator {
    pub const fn new() -> (ret: BuddyAllocator)
        ensures
            ret@.wf_before_validate_write(),
            forall|i: int|
                0 <= i < ORDER_USIZE as int ==> ret@.free_lists[i]@.len()
                    == 0,
    //forall |i: int| 0 <= i < ORDER_USIZE as int ==> ret@.free_lists[i].is_Some(),

    {
        let mut free_lists = new_array_linked_list32();
        let tracked mut perms: Map<(nat, nat), SnpPointsToRaw> = Map::tracked_empty();
        let ret = BuddyAllocator { perms: Tracked(perms), free_lists };
        proof {
            assert forall|bucket: nat| bucket < ret@.free_lists.len() implies ret@.wf_bucket(
                bucket,
            ) by {
                //assert(ret@.free_lists[bucket as int].is_Some());
                assert(ret@.free_lists[bucket as int].inv());
                assert(ret@.free_lists[bucket as int].is_constant());
            }
            assert forall|b: nat, i: nat| #[trigger] ret@.wf_perm(b, i) by {}
        }
        ret
    }

    #[inline]
    fn pop(&mut self, bucket: usize) -> (ret: Option<(usize_t, Tracked<SnpPointsToRaw>)>)
        requires
            old(self)@.inv(),
            SpecBuddyAllocator::valid_bucket(bucket as nat),
        ensures
            self@.inv(),
            ret.is_Some() ==> {
                ret.get_Some_0().1@@.wf_freemem(
                    (ret.get_Some_0().0 as int, spec_bit64(bucket as u64) as nat),
                )
            },
            ret.is_Some() ==> self@.spec_pop_or_push_element(old(self)@, bucket as nat),
            ret.is_None() ==> {
                &&& old(self)@ =~~= self@
                &&& self@.free_lists[bucket as int]@.len() == 0
            },
    {
        let ghost old_self = *self;
        let ghost gbucket = bucket as nat;
        proof {
            bit_shl64_pow2_auto();
        }
        proof {
            assert(self@.wf_bucket(gbucket));
        }
        let ghost old_list = old_self.free_lists[gbucket as int];
        let ghost old_len = old_list@.len();
        let mut list = self.free_lists.take(bucket);
        proof {
            assert(old_self@.wf_perm(gbucket, (old_len - 1) as nat));
        }
        let ret = list.pop();
        // TODO: Remove this dirty update back.
        self.free_lists.update(bucket, list);
        match ret {
            Some((nodeptr, tnode_perm)) => {
                let tracked free_perm = self.perms.borrow_mut().tracked_remove(
                    (gbucket, list@.len()),
                );
                proof {
                    assert(old_self@.perms =~~= self@.perms.insert(
                        (gbucket, list@.len()),
                        free_perm,
                    ));
                    assert(old_self@.perms.remove((gbucket, list@.len())) =~~= self@.perms);
                    assert(old_self@.free_lists =~~= self@.free_lists.update(
                        gbucket as int,
                        old_self.free_lists[gbucket as int],
                    ));
                    assert(list@ =~~= old_list@.drop_last());
                    assert(old_list@.last() === SpecListItem {
                        ptr: nodeptr,
                        snp: tnode_perm@@.snp(),
                        val: tnode_perm@@.value().get_Some_0().val,
                    });
                    assert(old_list@.drop_last() =~~= list@);
                    old_self@.proof_add_one_to_bucket(
                        &self@,
                        gbucket,
                        nodeptr,
                        tnode_perm@,
                        free_perm,
                    );
                    assert(self@.wf_perm(gbucket, old_len));
                }
                let tracked node_rperm = tnode_perm.get().trusted_into_raw();
                let tracked ret_perm = node_rperm.trusted_join(free_perm);
                let ret = Some((nodeptr.to_usize(), Tracked(ret_perm)));
                proof {
                    assert(ret.get_Some_0().1.is_constant());
                    assert(ret.get_Some_0().1.wf());
                }
                return ret
            },
            None => {
                proof {
                    assert(old_self@.perms =~~= self@.perms);
                    assert(old_self@.free_lists =~~= self@.free_lists);
                }
                return None
            },
        }
    }

    #[inline]
    fn push(&mut self, bucket: usize, start: usize_t, Tracked(perm): Tracked<SnpPointsToRaw>)
        requires
            bucket.is_constant(),
            start.is_constant(),
            SpecBuddyAllocator::valid_bucket(bucket as nat),
            perm@.wf_freemem((start as int, spec_bit64((bucket as u64)) as nat)),
            old(self)@.inv(),
        ensures
            self@.inv(),
            old(self)@.spec_pop_or_push_element(self@, bucket as nat),
            start == self@.free_lists[bucket as int]@.last().ptr.id(),
    {
        let ghost old_self = *self;
        let tracked (mut node_rperm, free_perm) = perm.trusted_split(MIN_ADDR_ALIGN!() as nat);
        let tracked mut node_perm = node_rperm.trusted_into();
        proof {
            bit_shl64_pow2_auto();
        }
        let nodeptr = SnpPPtr::<Node<()>>::from_usize(start);
        nodeptr.replace(Tracked(&mut node_perm), Node::default());
        proof {
            assert(self@.wf_bucket(bucket as nat));
            let len = self.free_lists[bucket as int]@.len();
            assert(self@.wf_perm(bucket as nat, len));
            self.perms.borrow_mut().tracked_insert((bucket as nat, len), free_perm);
        }
        let mut current_bucket = self.free_lists.take(bucket);
        current_bucket.push(nodeptr, Tracked(node_perm));
        // TODO: Remove this dirty update back.
        self.free_lists.take_end(bucket, current_bucket);
        proof {
            self@.proof_add_one_to_bucket(&old_self@, bucket as nat, nodeptr, node_perm, free_perm);
        }
    }

    pub fn alloc_inner(&mut self, size: usize, align: usize) -> (ret: Option<
        (usize, Tracked<SnpPointsToRaw>),
    >)
        requires
            spec_bit64_is_pow_of_2(align as int),
            0 < (size as int) <= POW2!(31),
            0 < (align as int) <= POW2!(31),
            size.is_constant(),
            align.is_constant(),
            old(self)@.inv(),
        ensures
            self@.inv(),
            ret.is_Some() ==> alloc_valid_ptr(size, ret.get_Some_0()),
            ret.is_Some() ==> ret.get_Some_0().is_constant(),
            ret.is_Some() ==> (spec_align_up(ret.get_Some_0().0 as int, align as int), size as nat)
                === (ret.get_Some_0().0 as int, size as nat),
    {
        let old_size = size;
        let mut size = size;
        if let Some((addr, perm)) = self._alloc_inner(&mut size, align) {
            let prev_addr = addr;
            let addr: usize_t = align_up_by(addr as u64, align as u64) as usize;
            let Tracked(mut ret_perm) = perm;
            if addr != prev_addr {
                return None;
            }
            proof {
                assert(size == ret_perm@.size());
                assert(size >= old_size);
                if old_size < ret_perm@.size() {
                    ret_perm = ret_perm.trusted_split(old_size as nat).0;
                } else {
                    assert(old_size == ret_perm@.size());
                }
            }
            mem_set_zeros(addr, old_size, Tracked(&mut ret_perm));
            Some((addr, Tracked(ret_perm)))
        } else {
            None
        }
    }

    pub fn _alloc_inner(&mut self, size: &mut usize_t, align: usize_t) -> (ret: Option<
        (usize_t, Tracked<SnpPointsToRaw>),
    >)
        requires
            spec_bit64_is_pow_of_2(align as int),
            0 < (*old(size) as int) <= POW2!(31),
            0 < (align as int) <= POW2!(31),
            old(size).is_constant(),
            align.is_constant(),
            old(self)@.inv(),
        ensures
            self@.inv(),
            ret.is_Some() ==> valid_free_ptr(*size, ret.get_Some_0()),
            ret.is_Some() ==> alloc_valid_size(*old(size), *size),
            *size % align == 0,
            size.is_constant(),
    {
        proof {
            bit_shl64_pow2_auto();
        }
        let ghost old_size = *size;
        *size =
        max(max(align as u64, MIN_ADDR_ALIGN as u64), next_power_of_two((*size) as u64)) as usize;
        assert(*size < POW2!(32));
        assert(*size >= MIN_ADDR_ALIGN);
        let size = *size;
        let bucket = pow2_to_bits(size as u64) as usize;
        let mut i = bucket;
        let mut ret = None;
        assert(bucket < 32);
        assert(bucket >= 3);
        while i < ORDER_USIZE
            invariant_except_break
                bucket as int <= i as int <= ORDER,
                SpecBuddyAllocator::valid_bucket(bucket as nat),
                spec_bit64(bucket as u64) == size as int,
                size >= old_size,
                self@.inv(),
                !ret.is_Some(),
                i.is_constant(),
                ret.is_constant(),
                self.is_constant(),
                bucket.is_constant(),
                size.is_constant(),
            ensures
                ret.is_Some() ==> valid_free_ptr(size, ret.get_Some_0()),
                ret.is_Some() ==> alloc_valid_size(old_size, size),
                ret.is_constant(),
                self.is_constant(),
                self@.inv(),
        {
            proof {
                bit_shl64_pow2_auto();
                assert(self@.wf_bucket(i as nat));
            }
            if !self.free_lists.index(i).is_empty() && i > bucket {
                // Split buffers
                let mut j = i;
                while j >= bucket + 1
                    invariant
                        bucket as int <= (i as int) < ORDER,
                        bucket as int <= (j as int) <= i as int,
                        SpecBuddyAllocator::valid_bucket(bucket as nat),
                        spec_bit64(bucket as u64) as int == size as int,
                        self@.inv(),
                        self@.free_lists[j as int]@.len() > 0,
                        i.is_constant(),
                        j.is_constant(),
                        ret.is_constant(),
                        self.is_constant(),
                        bucket.is_constant(),
                        size.is_constant(),
                {
                    proof {
                        bit_shl64_pow2_auto();
                    }
                    let ghost prev_self = *self;
                    if let Some((start1, tperm)) = self.pop(j) {
                        let offset = 1usize << (j - 1);
                        let start2 = start1 + offset;
                        let tracked mut perm1;
                        let tracked mut perm2;
                        proof {
                            let tracked perm = tperm.get();
                            let tracked (p1, p2) = perm.trusted_split(offset as nat);
                            perm1 = p1;
                            perm2 = p2;
                        }
                        self.push(j - 1, start2, Tracked(perm2));
                        self.push(j - 1, start1, Tracked(perm1));
                    }
                    j = j - 1;
                }
            }
            let ghost len = self.free_lists[bucket as int]@.len();
            proof {
                assert(self@.wf_bucket(bucket as nat));
                assert(self@.wf_perm(bucket as nat, (len - 1) as nat));
            }
            if let Some(addr_with_perm) = self.pop(bucket) {
                ret = Some(addr_with_perm);
                break ;
            }
            i = i + 1;
        }
        ret
    }

    //pub fn dealloc(&mut self, addr: u64, layout: Layout) {}
    /// Dealloc a range of memory from the heap
    pub fn dealloc_inner(
        &mut self,
        addr: usize_t,
        size: usize_t,
        Tracked(perm): Tracked<SnpPointsToRaw>,
    )
        requires
            perm@.wf_freemem((addr as int, size as nat)),
            spec_bit64_is_pow_of_2(size as int),
            size < (1usize << ORDER),
            size.is_constant(),
            size > MIN_ADDR_ALIGN!(),
            addr % size == 0,
            old(self)@.inv(),
        ensures
            self@.inv(),
    {
        proof {
            bit_shl64_pow2_auto();
        }
        let mut current_bucket = pow2_to_bits(size as u64) as usize;
        let mut current_addr: usize = addr;
        let tracked mut current_perm = perm;
        let ghost mut current_size = size as usize;
        // Put back into free list
        //self.push(current_bucket, current_addr, Tracked(perm));
        // Merge free buddy lists
        let len = self.free_lists.len();
        while current_bucket + 1 < len
            invariant
                current_bucket.is_constant(),
                len.is_constant(),
                current_addr.is_constant(),
                self.is_constant(),
                current_perm@.wf_freemem((current_addr as int, current_size as nat)),
                current_size == (1u64 << current_bucket as u64),
                current_bucket as int + 1 <= len as int,
                SpecBuddyAllocator::valid_bucket(current_bucket as nat),
                len == self@.free_lists.len(),
                self@.inv(),
                current_addr as u64 % (spec_bit64(current_bucket as u64)) == 0,
            ensures
                current_bucket.is_constant(),
                current_addr.is_constant(),
                self.is_constant(),
                current_perm@.wf_freemem((current_addr as int, current_size as nat)),
                current_size == (1u64 << current_bucket as u64),
                current_bucket as int + 1 <= len as int,
                SpecBuddyAllocator::valid_bucket(current_bucket as nat),
                self@.inv(),
                current_addr as u64 % (spec_bit64(current_bucket as u64)) == 0,
        {
            let buddy = current_addr ^ (1 << current_bucket);
            let ghost prev_self = self@;
            let check = |ptr: SnpPPtr<Node<()>>| -> (ret: bool)
                requires
                    ptr.is_constant(),
                ensures
                    ret == (ptr.id() == buddy as int),
                { ptr.to_usize() == buddy };
            proof {
                assert(self@.wf_bucket(current_bucket as nat));
            }
            let mut list = self.free_lists.take(current_bucket);
            let ghost prev_list = list;
            let removed_items = list.remove_iter(check, 1);
            assert((removed_items.0@.len() == 0) ==> prev_list === list);
            let ghost removed_ids = removed_items.1@;
            let mut removed = removed_items.0;
            self.free_lists.update(current_bucket, list);
            if let Some((ptr, tperm)) = removed.pop() {
                let tracked mut removed_perm;
                proof {
                    proof_buddy(current_addr as u64, current_bucket as u64, current_size as u64);
                    assert(removed_ids.len() == 1);
                    assert(check.ensures((ptr,), true));
                    assert(ptr.id() == buddy as int);
                    let ghost removed_id = removed_ids[0];
                    let tracked mut removed_node_perm;
                    let tracked Tracked(perm) = tperm;
                    removed_node_perm = perm;
                    assert(perm@.pptr() == buddy as int);
                    assert(prev_self.wf_perm(current_bucket as nat, removed_id as nat));
                    assert(prev_self.wf_perm(current_bucket as nat, list@.len() as nat));
                    assert(prev_self.wf_perm(current_bucket as nat, (list@.len() - 1) as nat));
                    assert(prev_self.perms === self@.perms);
                    let tracked removed_free_perm = self.perms.borrow_mut().tracked_remove(
                        (current_bucket as nat, removed_id as nat),
                    );
                    removed_perm =
                    removed_node_perm.trusted_into_raw().trusted_join(removed_free_perm);
                    let key_map = Map::new(
                        |k: (nat, nat)|
                            k.0 < ORDER && k.1 < prev_self.free_lists[k.0 as int]@.len() && k !== (
                                current_bucket as nat,
                                (prev_list@.len() - 1) as nat,
                            ),
                        |k: (nat, nat)|
                            if k.0 != current_bucket as nat || k.1 < removed_id as nat {
                                k
                            } else {
                                (k.0, k.1 + 1)
                            },
                    );
                    assert forall|j1: (nat, nat), j2: (nat, nat)|
                        !builtin::spec_eq(j1, j2) && key_map.dom().contains(j1)
                            && key_map.dom().contains(j2) implies !builtin::spec_eq(
                        key_map.index(j1),
                        key_map.index(j2),
                    ) by {
                        assert(prev_self.wf_perm(j1.0, j1.1));
                    }
                    assert forall|j| key_map.dom().contains(j) implies self@.perms.dom().contains(
                        key_map.index(j),
                    ) by {
                        let (bb, ii) = j;
                        let (b, i) = key_map.index(j);
                        assert(prev_self.wf_perm(b, i));
                        assert(prev_self.wf_perm(bb, ii));
                        assert(prev_self.perms.contains_key((b, i)));
                    }
                    self.perms.borrow_mut().tracked_map_keys_in_place(key_map);
                    assert(self@.inv()) by {
                        assert forall|k|
                            k !== (
                                current_bucket as nat,
                                (prev_list@.len() - 1) as nat,
                            ) implies prev_self.perms.contains_key(k) == self@.perms.contains_key(
                            k,
                        ) by {
                            assert(prev_self.wf_perm(k.0, k.1));
                            if prev_self.perms.contains_key(k) {
                                assert(key_map.contains_key(k));
                            }
                            if self@.perms.contains_key(k) {
                                assert(key_map.contains_key(k));
                                assert(prev_self.perms.contains_key(k));
                            }
                        }
                        assert forall|k|
                            k === (
                                current_bucket as nat,
                                (prev_list@.len() - 1) as nat,
                            ) implies !self@.perms.contains_key(k) by {
                            assert(!key_map.contains_key(k));
                        }
                        assert(prev_self.perms.dom().remove(
                            (current_bucket as nat, (prev_list@.len() - 1) as nat),
                        ) =~~= self@.perms.dom());
                        prev_self.proof_remove_or_add_idx(
                            &self@,
                            current_bucket as nat,
                            removed_id as nat,
                            ptr,
                            removed_node_perm,
                            removed_free_perm,
                        );
                    }
                    assert(removed_perm@.size() == current_size as nat);
                    assert(self@.wf_perm(current_bucket as nat, list@.len() as nat));
                }
                if current_addr > buddy {
                    //assert(buddy as int + current_size  == current_addr as int);
                    current_addr = buddy;
                    proof {
                        current_perm = removed_perm.trusted_join(current_perm);
                    }
                } else {
                    //assert(current_addr as int + current_size == buddy as int);
                    proof {
                        current_perm = current_perm.trusted_join(removed_perm);
                    }
                };
                current_bucket = current_bucket + 1;
                proof {
                    current_size = (1usize << current_bucket as usize);
                }
            } else {
                assert(removed@.len() == 0);
                assert(prev_list =~~= list);
                assert(self@.free_lists =~~= prev_self.free_lists);
                break ;
            }
        }
        self.push(current_bucket, current_addr, Tracked(current_perm));
    }
}

} // verus!
verus! {

impl BuddyAllocator {
    pub fn add_mem(
        &mut self,
        start: &mut usize,
        end: &mut usize,
        Tracked(perm): Tracked<SnpPointsToRaw>,
    )
        requires
            (*old(start)) < (*old(end)),
            old(start).is_constant(),
            old(end).is_constant(),
            old(start).spec_valid_addr_with(1),
            old(end).spec_valid_addr_with(0),
            old(self)@.inv(),
            old(self).is_constant(),
            perm@.wf_freemem(((*old(start) as int), (*old(end) - *old(start)) as nat)),
            perm@.snp() === SwSnpMemAttr::spec_default(),
        ensures
            self@.inv(),
            self.is_constant(),/*self@.inv(),
        GVA::new(*start as int).is_valid_end(),
        GVA::new(*end as int).is_valid_end(),
        spec_is_align_up_by_int(*old(start) as int, MIN_ADDR_ALIGN!() as int, *start as int),
        spec_is_align_down_by_int(*old(end) as int, MIN_ADDR_ALIGN!() as int, *end as int),*/

    {
        let ghost oldstart = *start;
        let ghost oldend = *end;
        proof {
            assert(spec_bit64_is_pow_of_2(MIN_ADDR_ALIGN!() as int));
        }
        *start = align_up_by((*start) as u64, MIN_ADDR_ALIGN as u64) as usize;
        *end = align_down_by((*end).into(), MIN_ADDR_ALIGN.into()).into();
        let current_end = *end;
        let mut current_start = *start;
        proof {
            assert(spec_size::<Node<()>>() == MIN_ADDR_ALIGN!());
        }
        if (current_start >= current_end) {
            return ;
        }
        let tracked (mut removed_start_perm, mut perm2) = perm.trusted_split(
            (current_start - oldstart) as nat,
        );
        let tracked (mut total_perm, mut removed_end_perm) = perm2.trusted_split(
            (current_end - current_start) as nat,
        );
        while (current_start < current_end) && (current_start + MIN_ADDR_ALIGN <= current_end)
            invariant
                current_start as int <= current_end as int,
                current_start.spec_valid_addr_with(0),
                current_end.spec_valid_addr_with(0),
                current_start as usize % MIN_ADDR_ALIGN == 0,
                current_end as usize % MIN_ADDR_ALIGN == 0,
                self@.inv(),
                total_perm@.wf_freemem(
                    ((current_start as int), (current_end - current_start) as nat),
                ),
                total_perm@.snp() === SwSnpMemAttr::spec_default(),
                current_end.is_constant(),
                current_start.is_constant(),
                self.is_constant(),
        {
            let totalsize = current_end - current_start;
            let ghost old_self = *self;
            proof {
                let ghost g_start = current_start as usize;
                //assert(g_start & sub(MIN_ADDR_ALIGN!(), 1usize) == 0usize) by(bit_vector)
                //requires g_start % MIN_ADDR_ALIGN!() == 0usize;
                proof_bit_usize_and_rel_mod(g_start, MIN_ADDR_ALIGN!());
                lemma_get_low_bits_via_bit_op(current_start as u64, MIN_ADDR_ALIGN!() as u64);
                proof_bit_usize_not(g_start);
                lemma_prev_power_of_two(totalsize as u64);
            }
            let size = if current_start != 0 {
                let lowbit = current_start & (!current_start + 1usize);
                min(lowbit as u64, prev_power_of_two(totalsize as u64)) as usize
            } else {
                prev_power_of_two(totalsize as u64) as usize
            };
            let size = min((1usize << (ORDER!() - 1usize) as usize) as u64, size as u64) as usize;
            let tracked (mut cur_perm, mut remain_perm) = total_perm.trusted_split(size as nat);
            proof {
                total_perm = remain_perm;
                bit_shl64_pow2_auto();  // prove size is power of 2 and bucket is valid;
            }
            // Get the bucket id.
            let bucket = pow2_to_bits(size as u64) as usize;
            self.push(bucket, current_start, Tracked(cur_perm));
            current_start = current_start + size;
        }
    }
}

} // verus!
