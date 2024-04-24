use super::*;
use crate::tspec::*;
use crate::*;

#[macro_export]
/// Ensure dummy holder does not take effect when comparing
macro_rules! define_dummy_holder_axiom {
    () => {
        verus!{
        #[verifier(external_body)]
        //#[verifier(broadcast_forall)]
        pub broadcast proof fn axiom_equal(left: Self, right: Self)
        ensures
            (left.value() == right.value()) == #[trigger](left =~= right),
            (left.value() == right.value()) == (left === right),
        {}

        #[verifier(external_body)]
        //#[verifier(broadcast_forall)]
        pub broadcast proof fn axiom_addr_type_dummy_holder(&self)
        ensures
            self.dummy === arbitrary(),
        {}
    }
    };
}

verus! {

impl<T> SpecAddr<T> {
    define_dummy_holder_axiom!{}
}

impl<T> SpecPage<T> {
    define_dummy_holder_axiom!{}
}

} // verus!
verus! {

impl<T> SpecAddr<T> {
    #[verifier::inline]
    pub open spec fn value(&self) -> int {
        self.as_int()
    }

    pub open spec fn to_u64(&self) -> u64 {
        self.value as u64
    }

    pub open spec fn is_valid(&self) -> bool {
        &&& 0 <= self.value()
            < VM_MEM_SIZE!()
        //&&& self.value() % BLOCK_SIZE!() == 0

    }

    pub open spec fn is_valid_end(&self) -> bool {
        &&& 0 <= self.value()
            <= VM_MEM_SIZE!()
        //&&& self.value() % BLOCK_SIZE!() == 0

    }

    pub open spec fn is_valid_with(&self, size: nat) -> bool {
        (*self + size as int).is_valid_end() && self.value() >= 0
    }

    pub open spec fn is_aligned(&self, align: int) -> bool {
        &&& (self.value() % align == 0)
    }

    pub open spec fn to_page(&self) -> SpecPage<T> {
        SpecPage::new(self.value() / PAGE_SIZE!())
    }

    pub open spec fn to_up_page(&self) -> SpecPage<T> {
        (*self + (PAGE_SIZE!() - 1)).to_page()
    }

    pub open spec fn align_up_by(&self, align: int) -> (ret: Self) {
        Self::new(spec_align_up(self.value(), align as int))
    }

    pub open spec fn align_by(&self, align: int) -> (ret: Self) {
        Self::new(spec_align_down(self.value(), align as int))
    }

    pub open spec fn to_offset(&self) -> int {
        self.value() % (PAGE_SIZE as int)
    }

    pub open spec fn convert<T2>(&self, page: SpecPage<T2>) -> SpecAddr<T2> {
        page.to_addr() + self.to_offset() as int
    }

    pub open spec fn new2(val: int, dummy: Ghost<T>) -> Self {
        SpecAddr { value: spec_cast_integer::<_, nat>(val), dummy: dummy }
    }

    pub open spec fn new(val: int) -> Self {
        Self::new2(val, spec_unused())
    }

    pub open spec fn new_u64(val: u64) -> Self {
        Self::new(spec_cast_integer::<_, int>(val))
    }

    pub open spec fn null() -> Self {
        Self::new(0)
    }

    pub open spec fn is_null(&self) -> bool {
        self.value() == 0
    }

    pub open spec fn to_mem(&self, n: nat) -> SpecMem<T> {
        SpecMem::from_range(*self, n)
    }

    #[verifier(inline)]
    pub open spec fn to_set(&self, n: nat) -> Set<int> {
        range_to_set(self.as_int(), n)
    }

    #[verifier(inline)]
    pub open spec fn to_set_with(&self, end: SpecAddr<T>) -> Set<int> {
        self.to_set((end.value() - self.value()) as nat)
    }

    // Replace to_set with lemma_to_set to include basic proofs.
    pub proof fn lemma_to_set(&self, n: nat) -> (ret: Set<int>)
        ensures
            ret.len() == n,
            ret.finite(),
            ret === self.to_set(n),
            n == 0 ==> ret.is_empty(),
    {
        let ret = lemma_to_set(self.as_int(), n);
        lemma_ret_is_empty(ret);
        ret
    }
}

} // verus!
verus! {

impl<T> SpecPage<T> {
    pub open spec fn value(&self) -> int {
        self.as_int()
    }

    pub open spec fn to_u64(&self) -> u64 {
        self.value as u64
    }

    pub open spec fn is_valid(&self) -> bool {
        0 <= self.value() < VM_PAGE_NUM!()
    }

    pub open spec fn is_valid_end(&self) -> bool {
        0 <= self.value() <= VM_PAGE_NUM!()
    }

    pub open spec fn is_valid_with(&self, size: nat) -> bool {
        self.value() >= 0 && self.value() + size <= VM_PAGE_NUM!()
    }

    pub open spec fn is_valid_with_int(&self, size: int) -> bool {
        self.value() >= 0 && self.value() + size <= VM_PAGE_NUM!()
    }

    pub open spec fn new(val: int) -> Self {
        Self::new2(val, spec_unused())
    }

    pub open spec fn new2(val: int, dummy: Ghost<T>) -> Self {
        SpecPage { value: val as nat, dummy: dummy }
    }

    pub open spec fn null() -> Self {
        Self::new(0)
    }

    pub open spec fn is_null(&self) -> bool {
        self.value() == 0
    }

    pub open spec fn to_addr(&self) -> SpecAddr<T> {
        let page = *self;
        SpecAddr::new(self.value() * PAGE_SIZE!())
    }

    pub open spec fn len_with_end(&self, end: SpecPage<T>) -> nat {
        let gva1 = self.to_addr();
        let gva2 = end.to_addr();
        let len = (gva2.value() - gva1.value());
        if len > 0 {
            len as nat
        } else {
            0
        }
    }

    #[verifier(inline)]
    pub open spec fn to_set(&self, n: nat) -> Set<int> {
        range_to_set(self.as_int(), n)
    }

    #[verifier(inline)]
    pub open spec fn to_set_with(&self, end: SpecPage<T>) -> Set<int> {
        self.to_set((end.value() - self.value()) as nat)
    }

    // Replace to_set with lemma_to_set to include basic proofs.
    pub proof fn lemma_to_set(&self, n: nat) -> (ret: Set<int>)
        ensures
            ret.len() == n,
            ret.finite(),
            ret === self.to_set(n),
            n == 0 <==> ret.is_empty(),
    {
        let ret = lemma_to_set(self.as_int(), n);
        lemma_ret_is_empty(ret);
        ret
    }

    pub open spec fn to_mem(&self) -> SpecMem<T> {
        let page = *self;
        page.to_addr().to_mem(PAGE_SIZE!() as nat)
    }

    pub open spec fn valid_as_size(&self, psize: PageSize) -> bool {
        match psize {
            PageSize::Size4k => { true },
            PageSize::Size2m => { self.value() % (PAGE_2M_SIZE!() / PAGE_SIZE!()) == 0 },
        }
    }
}

#[verifier(inline)]  // inline due to unsupported for bit-vector
pub open spec fn spec_page_align_down(addr: int) -> int {
    //addr - addr%PAGE_SIZE is unsupported
    addr / (PAGE_SIZE!() as int) * (PAGE_SIZE!() as int)
}

impl<T> IntValue for SpecPage<T> {
    open spec fn as_int(&self) -> int {
        self.value as int
    }

    open spec fn from_int(val: int) -> Self {
        Self::new(val)
    }
}

impl<T> IntValue for SpecAddr<T> {
    open spec fn as_int(&self) -> int {
        self.value as int
    }

    open spec fn from_int(val: int) -> Self {
        Self::new(val)
    }
}

impl<T> IntOrd for SpecPage<T> {
    #[verifier(inline)]
    open spec fn ord_int(&self) -> int {
        self.as_int()
    }
}

impl<T> IntOrd for SpecAddr<T> {
    #[verifier(inline)]
    open spec fn ord_int(&self) -> int {
        self.as_int()
    }
}

impl<T> SpecMem<T> {
    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_inv(&self)
        ensures
            (self.offset() + self.len()) <= PAGE_SIZE!(),
            self.offset() < PAGE_SIZE!(),
    {
    }

    pub proof fn proof_same_page(&self)
        ensures
            self.last().to_page() == self.to_page(),
            self.first().to_page() == self.to_page(),
    {
        let first_value = self.first().value();
        assert(first_value == self.to_page().to_addr().value() + self.offset());
        assert((self.to_page().to_addr().value() + self.offset()) / PAGE_SIZE!()
            === self.to_page().value());
        if self.len() > 0 {
            let last_value = self.last().value();
            assert(last_value == self.to_page().to_addr().value() + self.offset() + self.len() - 1);
            assert(self.offset() + self.len() <= PAGE_SIZE!());
            assert((self.to_page().as_int() * PAGE_SIZE!() + self.offset() + self.len() - 1)
                / PAGE_SIZE!() == self.to_page().as_int());
        } else {
            assert(self.last() == self.first());
        }
    }

    #[verifier(inline)]
    pub open spec fn inv(&self) -> bool {
        self.offset() + self.len() <= PAGE_SIZE!()
    }

    pub open spec fn from_range(addr: SpecAddr<T>, size: nat) -> Self
        recommends
            (addr + size as int - 1int).to_page() === addr.to_page(),
    {
        SpecMem { first: addr, size: size }
    }

    pub open spec fn convert<T2>(&self, pn: SpecPage<T2>) -> SpecMem<T2> {
        SpecMem { first: pn.to_addr() + self.first().to_offset(), size: self.size }
    }

    pub open spec fn is_aligned(&self, align: int) -> bool {
        self.offset() as int % align == 0
    }

    #[verifier(inline)]
    pub open spec fn contains(&self, addr: SpecAddr<T>) -> bool {
        self.to_set().contains(addr.as_int())
    }

    pub open spec fn is_valid(&self) -> bool {
        &&& self.len() > 0
        &&& self.to_page().is_valid()
    }

    pub open spec fn disjoint(&self, rhs: Self) -> bool {
        range_disjoint(self.first().as_int(), self.len(), rhs.first().as_int(), rhs.len())
    }

    pub proof fn lemma_disjoint(&self, rhs: Self) -> (ret: bool)
        ensures
            ret == self.disjoint(rhs),
            ret == self.to_set().disjoint(rhs.to_set()),
    {
        lemma_range_set_disjoint(self.first().as_int(), self.len(), rhs.first().as_int(), rhs.len())
    }

    #[verifier(inline)]
    pub open spec fn spec_index(&self, i: int) -> SpecAddr<T> {
        self.first() + i
    }

    #[verifier(inline)]
    pub open spec fn first(&self) -> SpecAddr<T> {
        self.first
    }

    pub open spec fn last(&self) -> SpecAddr<T> {
        if self.len() > 0 {
            self.first() + (self.len() - 1) as int
        } else {
            self.first()
        }
    }

    #[verifier(inline)]
    pub open spec fn end(&self) -> SpecAddr<T> {
        self.first() + (self.len() as int)
    }

    pub open spec fn offset(&self) -> nat {
        self.first().to_offset() as nat
    }

    pub open spec fn len(&self) -> nat {
        self.size
    }

    #[verifier(inline)]
    pub open spec fn to_set(&self) -> Set<int> {
        self.first().to_set(self.len())
    }

    pub proof fn lemma_to_set(&self) -> (ret: Set<int>)
        ensures
            ret.len() == self.len(),
            ret.finite(),
            ret === self.to_set(),
            ret === self.first().to_set(self.len()),
    {
        self.first().lemma_to_set(self.len())
    }

    pub open spec fn to_page(&self) -> SpecPage<T> {
        self.first().to_page()
    }

    pub proof fn lemma_aligned_mem_eq_or_disjoint(mem1: SpecMem<T>, mem2: SpecMem<T>, align: int)
        requires
            align == 8,
            mem1.is_aligned(align),
            mem2.is_aligned(align),
            mem1.len() == align,
            mem2.len() == align,
        ensures
            mem1 === mem2 || mem1.disjoint(mem2),
    {
        if !(mem1 =~= mem2) {
            assert(!(mem1.first() =~= mem2.first()));
            assert forall|i| 0 <= i < mem1.len() implies !#[trigger] mem2.contains(mem1[i]) by {
                assert forall|j| 0 <= j < mem2.len() implies !(mem2[j] =~= mem1[i]) by {
                    assert(mem2.first() != mem1.first());
                    assert(mem2[j] == mem2.first() + j);
                    assert(mem1[j] == mem1.first() + j);
                }
            }
        }
    }
}

} // verus!
