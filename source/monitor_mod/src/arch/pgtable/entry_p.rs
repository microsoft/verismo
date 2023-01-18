use super::*;
use crate::arch::addr_s::*;
use crate::arch::entities::*;
use crate::tspec::*;
use crate::*;

verus! {
    pub proof fn lemma_pt_entry_count()
    ensures
        PT_ENTRY_NUM!() == 512,
    {
        assert(PT_ENTRY_NUM!() == 512) by(bit_vector);
    }

    impl PTLevel {
        #[verifier(bit_vector)]
        pub proof fn lemma_size_offset()
        ensures
            0x1000 == BIT64!(12u64),
            0x200000 == BIT64!(21u64),
            0x40000000 == BIT64!(30u64),
            0x8000000000u64 == BIT64!(39u64),
        {}

        pub proof fn proof_size_offset(lvl: Self, size: u64, offset: u64)
        requires
            size as int == lvl.spec_pgsize(),
            offset as int == lvl.spec_offset(),
        ensures
            size == (1u64 << offset)
        {
            bit_shl64_pow2_auto();
            assert(size == (1u64 << offset));
        }

        pub proof fn proof_table_index_range<T: AddrType>(&self, vaddr: SpecAddr<T>)
        ensures
            0 <= self.spec_table_index(vaddr) < PT_ENTRY_NUM!(),
        {
            bits_p::bit_shl64_auto();
            proof_div_pos_neg_rel(vaddr.value(), self.spec_pgsize());
            proof_mod_range(vaddr.value() /self.spec_pgsize(), PT_ENTRY_NUM!() as int)
        }

        pub proof fn proof_table_index<T: AddrType>(vaddr: u64, lvl: PTLevel)
        ensures
            0 <= lvl.spec_table_index(GVA::new(vaddr as int)) < PT_ENTRY_NUM!(),
            ((vaddr >> (lvl.spec_offset() as u64)) & PT_ENTRY_IDX_MASK!()) as int == lvl.spec_table_index(GVA::new(vaddr as int)),
        {
            Self::lemma_table_index::<T>(vaddr, lvl);
            lemma_pt_entry_count();
        }

        pub proof fn lemma_table_index<T: AddrType>(val: u64, lvl: PTLevel) -> (ret: int)
        ensures
            ret == lvl.spec_table_index(SpecAddr::<T>::new(val as int)),
            (val >> (lvl.spec_offset() as u64))  == (val / (lvl.spec_pgsize() as u64)),
            (val >> (lvl.spec_offset() as u64)) & PT_ENTRY_IDX_MASK!() == (val / lvl.spec_pgsize() as u64) % PT_ENTRY_NUM!(),
            ((val >> (lvl.spec_offset() as u64)) & PT_ENTRY_IDX_MASK!()) as int == ret,
        {
            let ret = lvl.spec_table_index(SpecAddr::<T>::new(val as int));
            let t1 = val >> (lvl.spec_offset() as u64);
            bit_shl64_pow2_auto();
            proof_bit_u64_and_rel_mod(t1, PT_ENTRY_NUM!());
            assert(t1 & PT_ENTRY_IDX_MASK!() == t1 % PT_ENTRY_NUM!());
            bit_rsh64_div_rel(val, 12);
            bit_rsh64_div_rel(val, 21);
            bit_rsh64_div_rel(val, 30);
            bit_rsh64_div_rel(val, 39);
            PTLevel::proof_size_offset(lvl, (lvl.spec_pgsize() as u64), (lvl.spec_offset() as u64));
            lemma_pt_entry_count();
            lemma_bits64!();
            bit_shl64_pow2_auto();
            assert(PT_ENTRY_NUM!() == PT_ENTRY_NUM!() as int);
            assert(ret == (val as int / lvl.spec_pgsize()) % (PT_ENTRY_NUM!() as int));
            assert((val as int / lvl.spec_pgsize()) == (val / lvl.spec_pgsize() as u64)) by(nonlinear_arith)
            requires
                0 < lvl.spec_pgsize() < MAXU64!();
            assert(ret == (val / lvl.spec_pgsize() as u64) % PT_ENTRY_NUM!());
            ret
        }

        proof fn test_spec_next_lvl()
        ensures
            PTLevel::L2.parent_lvl().get_Some_0() == PTLevel::L3
        {}
    }

    impl<T: AddrType> SpecPageTableEntry<T> {
        pub proof fn lemma_each_table_is_one_page(&self, idx: nat)
        requires
            idx < PT_ENTRY_NUM!(),
        ensures
            self.addr_for_idx(idx).to_page() === self.spec_ppn(),
        {
            assert(PT_ENTRY_NUM!() == 512) by {
                bit_shl64_pow2_auto();
            };
            assert(PAGE_SIZE!() === PT_ENTRY_NUM!() * PT_ENTRY_SIZE!());
        }

        proof fn test_flags(entry: Self)
        requires
            entry.spec_value() == 0xff,
        ensures
            !entry.contains_flag(PteFlag::C)
        {
            reveal_with_fuel(spec_nat_pow2, 64);
            // Fixme: z3-4.11.2 need below assert but z3-4.10.1 does not need it
            bit_shl64_auto();
            assert(spec_int_pow2(PteFlag::C.as_int()) == BIT64!(51u64));
            //assert(entry.contains_flag(PteFlag::C) == true);
            //assert(entry.spec_value()/spec_int_pow2(PteFlag::C.as_int()) % 2 == 1);
        }
    }
}
