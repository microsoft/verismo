use super::*;
use crate::arch::addr_s::VM_PAGE_NUM;
use crate::debug::VPrint;

verismo_simple! {
#[derive(VClone, Copy, VPrint)]
#[repr(C, align(1))]
pub struct HyperVMemMapEntry {
    pub starting_gpn: u64,
    pub numpages: u64,
    pub mem_type: u16,
    pub flags: u16,
    pub reserved: u32,
}

proof fn lemma_eq_hv_mementry(v1: HyperVMemMapEntry, v2: HyperVMemMapEntry)
requires
    v1.starting_gpn === v2.starting_gpn,
    v1.numpages === v2.numpages,
    v1.mem_type === v2.mem_type,
    v1.flags === v2.flags,
    v1.reserved === v2.reserved,
ensures
    v1 === v2
{}

impl MemRangeInterface for HyperVMemMapEntry {
    #[verifier(inline)]
    open spec fn self_wf(&self) -> bool {
        self.wf()
    }

    #[verifier(inline)]
    open spec fn real_wf(r: (usize_s, usize_s)) -> bool {
        r.self_wf()
    }

    proof fn proof_constant_real_wf(r: (usize_s, usize_s)) {}

    open spec fn spec_end_max() -> usize {
        VM_PAGE_NUM
    }

    open spec fn spec_real_range(&self) -> (usize_s, usize_s) {
        (self.starting_gpn.vspec_cast_to(), self.numpages.vspec_cast_to())
    }

    #[inline]
    fn real_range(&self) -> (usize_s, usize_s) {
        (self.starting_gpn.into(), self.numpages.into())
    }

    #[verifier(inline)]
    open spec fn spec_set_range(self, r: (usize_s, usize_s)) -> Self {
        HyperVMemMapEntry {
            starting_gpn: r.0.vspec_cast_to(),
            numpages: r.1.vspec_cast_to(),
            mem_type: self.mem_type,
            flags: self.flags,
            reserved: self.reserved,
        }
    }

    fn update_range(&mut self, r: (usize_s, usize_s)){
        let ghost oldself = *self;
        self.starting_gpn = r.0 as u64;
        self.numpages = r.1 as u64;
        proof {
            proof_sectype_cast_eq::<usize, u64, ()>(r.0);
            proof_sectype_cast_eq::<usize, u64, ()>(r.1);
            assert(r.0 as u64_s as usize_s === r.0);
            assert(r.1 as u64_s as usize_s === r.1);
            assert(self.starting_gpn === oldself.spec_set_range(r).starting_gpn);
            assert(self.numpages === oldself.spec_set_range(r).numpages);
            assert(self.flags === oldself.spec_set_range(r).flags);
            assert(self.reserved === oldself.spec_set_range(r).reserved);
            assert(self.mem_type === oldself.spec_set_range(r).mem_type);
            lemma_eq_hv_mementry(oldself.spec_set_range(r), *self);
            // BUG(verus):
            assume(oldself.spec_set_range(r) === *self);
        }
    }

    #[inline]
    fn end_max() -> usize_s {
        VM_PAGE_NUM as usize_s
    }
}


pub type HyperVMemMapTable = Array<HyperVMemMapEntry, 0x80>;

#[derive(SpecGetter, SpecSetter)]
#[repr(C, align(1))]
pub struct HvParamTable {
    pub cpu_count: u64,
    pub reserved: Array<u8, 16>,
    pub mem_table: HyperVMemMapTable,
}
}

verismo_simple! {
    impl HyperVMemMapEntry {
        #[verifier(inline)]
        pub open spec fn range(&self) -> (int, nat) {
            (self.starting_gpn as int * PAGE_SIZE!(),  ((self.numpages as nat) * PAGE_SIZE!()) as nat)
        }
    }
}
