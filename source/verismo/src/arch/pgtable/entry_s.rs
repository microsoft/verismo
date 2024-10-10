use super::*;
use crate::arch::addr_s::*;
use crate::arch::entities::*;
use crate::tspec::*;
use crate::*;

verus! {

impl PTLevel {
    pub open spec fn spec_pgsize(&self) -> int {
        let val = match *self {
            PTLevel::L3 => L3_PGSIZE,
            PTLevel::L2 => L2_PGSIZE,
            PTLevel::L1 => L1_PGSIZE,
            PTLevel::L0 => L0_PGSIZE,
        };
        val as int
    }

    #[verifier(inline)]
    pub open spec fn parent_lvl(&self) -> Option<PTLevel> {
        match *self {
            PTLevel::L3 => Option::None,
            PTLevel::L2 => Option::Some(PTLevel::L3),
            PTLevel::L1 => Option::Some(PTLevel::L2),
            PTLevel::L0 => Option::Some(PTLevel::L1),
        }
    }

    #[verifier(inline)]
    pub open spec fn child_lvl(&self) -> Option<PTLevel> {
        match *self {
            PTLevel::L3 => Option::Some(PTLevel::L2),
            PTLevel::L2 => Option::Some(PTLevel::L1),
            PTLevel::L1 => Option::Some(PTLevel::L0),
            PTLevel::L0 => Option::None,
        }
    }

    pub open spec fn spec_offset(&self) -> int {
        (39 - (self.as_int() * (PT_ENTRY_NUM_BIT as int)))
    }

    pub open spec fn spec_table_index<T: AddrType>(&self, vaddr: SpecAddr<T>) -> int {
        (vaddr.value() / self.spec_pgsize()) % (PT_ENTRY_NUM as int)
    }
}

} // verus!
verus! {

impl<T: AddrType> SpecPageTableEntry<T> {
    pub open spec fn new(value: int, dummy: Ghost<T>) -> Self {
        SpecPageTableEntry { value: value, dummy: dummy }
    }

    pub open spec fn new_val(value: int) -> Self {
        SpecPageTableEntry { value: value, dummy: spec_unused() }
    }

    pub open spec fn contains_flag(&self, flag: PteFlag) -> bool {
        (self.spec_value() / spec_int_pow2(flag.as_int())) % 2 == 1
    }

    /// Question: spec_int_pow2(52) will cause mod memdb always
    /// verified without checking the actual logic;
    pub open spec fn spec_ppn(&self) -> SpecPage<T> {
        let bits = spec_page_frame_bits();
        let addr = self.spec_value() % (BIT64!(bits) as int);
        SpecAddr::new2(addr, self.dummy).to_page()
    }

    pub open spec fn is_encrypted(&self) -> bool {
        self.contains_flag(PteFlag::C)
    }

    pub open spec fn is_present(&self) -> bool {
        self.contains_flag(PteFlag::P)
    }

    pub open spec fn is_writable(&self) -> bool {
        self.contains_flag(PteFlag::W)
    }

    pub open spec fn spec_addr(&self) -> SpecAddr<T> {
        self.spec_ppn().to_addr()
    }

    pub open spec fn spec_translate_page<VT: AddrType>(&self, v: SpecPage<VT>) -> Option::<
        SpecPage<T>,
    > {
        if self.is_present() {
            Option::Some(self.spec_ppn())
        } else {
            Option::None
        }
    }

    pub open spec fn spec_translate<VT: AddrType>(&self, v: SpecAddr<VT>) -> Option::<SpecAddr<T>> {
        if self.is_present() {
            Option::Some(self.spec_addr() + v.to_offset())
        } else {
            Option::None
        }
    }

    pub open spec fn addr_for_idx(&self, idx: nat) -> SpecAddr<T>
        recommends
            idx < PT_ENTRY_NUM,
    {
        let offset = (idx * PT_ENTRY_SIZE) as int;
        self.spec_addr() + offset
    }
}

} // verus!
