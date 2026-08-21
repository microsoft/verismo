use verus_state_machines_macros::tokenized_state_machine;
#[cfg(verus_only)]
use vstd::modes::tracked_swap;
use vstd::multiset::*;
use vstd::prelude::*;

verus! {

tokenized_state_machine!(address_space {
    fields {
        #[sharding(constant)]
        pub initial_dom: Set<int>,

        #[sharding(multiset)]
        pub parts: Multiset<Set<int>>,
    }

    #[invariant]
    pub fn parts_stay_within_initial_dom(&self) -> bool {
        forall |part: Set<int>| #[trigger] self.parts.count(part) > 0
            ==> part.subset_of(self.initial_dom)
    }

    #[invariant]
    pub fn parts_cover_initial_dom(&self) -> bool {
        forall |addr: int| self.initial_dom.contains(addr) ==>
            exists |part: Set<int>| #[trigger] self.parts.count(part) > 0
                && part.contains(addr)
    }

    #[invariant]
    pub fn parts_do_not_overlap(&self) -> bool {
        forall |left: Set<int>, right: Set<int>, addr: int|
            #![auto]
            self.parts.count(left) > 0
                && self.parts.count(right) > 0
                && left.contains(addr)
                && right.contains(addr)
            ==> left == right && self.parts.count(left) == 1
    }

    init! {
        initialize(initial_dom: Set<int>) {
            init initial_dom = initial_dom;
            init parts = Multiset::empty().insert(initial_dom);
        }
    }

    transition! {
        split(part: Set<int>, range: Set<int>) {
            remove parts -= {part};
            require(range.subset_of(part));
            add parts += {range};
            add parts += {part.difference(range)};
        }
    }

    transition! {
        join(left: Set<int>, right: Set<int>) {
            remove parts -= {left};
            remove parts -= {right};
            add parts += {left.union(right)};
        }
    }

    transition! {
        prove_disjoint(left: Set<int>, right: Set<int>) {
            remove parts -= {left};
            have parts >= {right};
            assert(left.disjoint(right));
            add parts += {left};
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, initial_dom: Set<int>) {
        assert forall |addr: int| initial_dom.contains(addr) implies
            exists |part: Set<int>| #[trigger] post.parts.count(part) > 0
                && part.contains(addr) by {
            assert(post.parts.count(initial_dom) > 0);
        }
    }

    #[inductive(split)]
    fn split_inductive(
        pre: Self,
        post: Self,
        part: Set<int>,
        range: Set<int>,
    ) {
        assert forall |addr: int| pre.initial_dom.contains(addr) implies
            exists |new_part: Set<int>| #[trigger] post.parts.count(new_part) > 0
                && new_part.contains(addr) by {
            let old_part = choose |old_part: Set<int>| #![auto]
                pre.parts.count(old_part) > 0 && old_part.contains(addr);
            if old_part == part {
                if range.contains(addr) {
                    assert(post.parts.count(range) > 0);
                } else {
                    assert(part.difference(range).contains(addr));
                    assert(post.parts.count(part.difference(range)) > 0);
                }
            } else {
                assert(pre.parts.remove(part).count(old_part) > 0);
                assert(post.parts.count(old_part) > 0);
            }
        }
    }

    #[inductive(join)]
    fn join_inductive(
        pre: Self,
        post: Self,
        left: Set<int>,
        right: Set<int>,
    ) {
        assert forall |addr: int| pre.initial_dom.contains(addr) implies
            exists |new_part: Set<int>| #[trigger] post.parts.count(new_part) > 0
                && new_part.contains(addr) by {
            let old_part = choose |old_part: Set<int>| #![auto]
                pre.parts.count(old_part) > 0 && old_part.contains(addr);
            if old_part == left || old_part == right {
                assert(left.union(right).contains(addr));
                assert(post.parts.count(left.union(right)) > 0);
            } else {
                assert(pre.parts.remove(left).remove(right).count(old_part) > 0);
                assert(post.parts.count(old_part) > 0);
            }
        }
    }

    #[inductive(prove_disjoint)]
    fn prove_disjoint_inductive(
        pre: Self,
        post: Self,
        left: Set<int>,
        right: Set<int>,
    ) {
        assert(post.parts =~= pre.parts);
    }
});

pub tracked struct UniqueAddress {
    tracked inst: address_space::Instance,
    tracked part: address_space::parts,
}

impl UniqueAddress {
    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool {
        self.part.instance_id() == self.inst.id()
    }

    pub closed spec fn dom(self) -> Set<int> {
        self.part.element()
    }

    pub open spec fn is_range(self, start: int, len: int) -> bool {
        self.dom() =~= Set::range(start, start + len)
    }

    pub closed spec fn address_space(self) -> InstanceId {
        self.inst.id()
    }

    pub proof fn init(initial_dom: Set<int>) -> (tracked space: Self)
        ensures
            space.dom() == initial_dom,
    {
        let tracked (Tracked(inst), Tracked(mut parts)) =
            address_space::Instance::initialize(initial_dom);
        let tracked part = parts.remove(initial_dom);
        UniqueAddress { inst, part }
    }

    pub proof fn split(tracked self, range: Set<int>) -> (tracked res: (Self, Self))
        requires
            range.subset_of(self.dom()),
        ensures
            res.0.address_space() == self.address_space(),
            res.1.address_space() == self.address_space(),
            res.0.dom() == range,
            res.1.dom() == self.dom().difference(range),
    {
        use_type_invariant(&self);
        let ghost dom = self.dom();
        let tracked UniqueAddress { inst, part } = self;
        let tracked (Tracked(selected), Tracked(rest)) = inst.split(dom, range, part);
        (
            UniqueAddress { inst, part: selected },
            UniqueAddress { inst, part: rest },
        )
    }

    pub proof fn join(tracked self, tracked other: Self) -> (tracked joined: Self)
        requires
            self.address_space() == other.address_space(),
        ensures
            joined.address_space() == self.address_space(),
            joined.dom() == self.dom().union(other.dom()),
    {
        use_type_invariant(&self);
        use_type_invariant(&other);
        let ghost left_dom = self.dom();
        let ghost right_dom = other.dom();
        let tracked UniqueAddress { inst, part: left } = self;
        let tracked UniqueAddress { part: right, .. } = other;
        let tracked joined = inst.join(left_dom, right_dom, left, right);
        UniqueAddress { inst, part: joined }
    }

    pub proof fn prove_disjoint(tracked &mut self, tracked other: &Self)
        requires
            old(self).address_space() == other.address_space(),
        ensures
            final(self).address_space() == old(self).address_space(),
            final(self).dom() == old(self).dom(),
            final(self).dom().disjoint(other.dom()),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        let tracked mut current = UniqueAddress::init(Set::empty());
        tracked_swap(self, &mut current);
        let ghost left_dom = current.dom();
        let tracked UniqueAddress { inst, part } = current;
        let tracked part = inst.prove_disjoint(left_dom, other.dom(), part, &other.part);
        *self = UniqueAddress { inst, part };
    }
}
}

#[cfg(all(verus_only, feature = "verification-test"))]
verus! {
proof fn test_address_space_initializes_requested_domain() {
    let ghost initial = Set::empty().insert(1).insert(3);
    let tracked space = UniqueAddress::init(initial);
    assert(space.dom() =~= initial);
    assert(space.address_space() == space.address_space());
}

proof fn test_address_space_splits_subsets_and_empty_tokens() {
    let ghost initial = Set::range(0, 4);
    let ghost selected = Set::range(0, 2);
    let tracked space = UniqueAddress::init(initial);
    let ghost id = space.address_space();
    let tracked (left, rest) = space.split(selected);
    assert(left.dom() =~= selected);
    assert(rest.dom() =~= initial.difference(selected));
    assert(left.address_space() == id);
    assert(rest.address_space() == id);

    let tracked (empty, left) = left.split(Set::empty());
    assert(empty.dom().is_empty());
    assert(left.dom() =~= selected);

    let tracked (empty1, empty2) = empty.split(Set::empty());
    assert(empty1.dom().is_empty());
    assert(empty2.dom().is_empty());

    let tracked full_space = UniqueAddress::init(initial);
    let tracked (full, empty) = full_space.split(initial);
    assert(full.dom() =~= initial);
    assert(empty.dom().is_empty());
}

proof fn test_address_space_joins_separated_domains() {
    let ghost initial = Set::range(0, 6);
    let ghost low_dom = Set::range(0, 2);
    let ghost middle_dom = Set::range(2, 4);
    let tracked whole = UniqueAddress::init(initial);
    let tracked (low, rest) = whole.split(low_dom);
    let tracked (middle, high) = rest.split(middle_dom);

    let tracked outer = low.join(high);
    assert(outer.dom() =~= low_dom.union(Set::range(4, 6)));

    let tracked joined = outer.join(middle);
    assert(joined.dom() =~= initial);
}

proof fn test_distinct_tokens_have_disjoint_domains() {
    let tracked whole = UniqueAddress::init(Set::range(0, 6));
    let tracked (mut left, right) = whole.split(Set::range(0, 3));
    left.prove_disjoint(&right);
    assert(left.dom().disjoint(right.dom()));
}

proof fn test_rejects_out_of_domain_split() {
    let tracked space = UniqueAddress::init(Set::empty().insert(1));
    let tracked _ = space.split(Set::empty().insert(2));
}

proof fn test_rejects_cross_instance_join() {
    let tracked left = UniqueAddress::init(Set::empty().insert(1));
    let tracked right = UniqueAddress::init(Set::empty().insert(2));
    let tracked _ = left.join(right);
}

}
