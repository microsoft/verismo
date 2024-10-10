use super::*;
use crate::addr_e::*;
use crate::arch::addr_s::*;
use crate::arch::pgtable::entry_p;
use crate::debug::VPrintAtLevel;
use crate::global::*;
use crate::registers::{AnyRegTrait, RegisterPerm, RegisterPermValue};
use crate::snp::ghcb::*;
use crate::snp::SnpCoreSharedMem;
use crate::*;

verus! {

pub const L4_MAX_ADDR: usize = 0x1000_0000_0000_0000usize;

pub fn vn_to_pn(page: u64, Tracked(page_perm): Tracked<&SnpPointsToRaw>) -> (ret: u64)
    requires
        page_perm@.range().0 <= (page as int).to_addr(),
        page_perm@.range().end() >= (page as int).to_addr(),
        page_perm@.snp().guestmap[page as int] == spec_vn_to_pn(page as int),
    ensures
        ret == spec_vn_to_pn(page as int),
{
    page
}

pub fn va_to_pa(vaddr: u64, Tracked(page_perm): Tracked<&SnpPointsToRaw>) -> (ret: u64)
    requires
        page_perm@.range().0 <= vaddr,
        page_perm@.range().end() >= vaddr,
        page_perm@.snp().guestmap[(vaddr as int).to_page()] == spec_va_to_pa(
            vaddr as int,
        ).to_page(),
    ensures
        ret == spec_va_to_pa(vaddr as int),
{
    vaddr
}

pub fn pa_to_va(paddr: u64, Tracked(page_perm): Tracked<&SnpPointsToRaw>) -> (ret: u64)
    requires
        page_perm@.range().0 <= spec_pa_to_va(paddr as int),
        page_perm@.range().end() >= spec_pa_to_va(paddr as int),
        page_perm@.snp().guestmap[spec_pa_to_va(paddr as int).to_page()] == (
        paddr as int).to_page(),
    ensures
        ret == spec_pa_to_va(paddr as int),
{
    paddr
}

impl PTE {
    pub open spec fn has_next(&self) -> bool {
        &&& self.spec_psize() == 0
        &&& self.spec_present() == 1
    }

    pub open spec fn to_attr(&self) -> PTAttr {
        PTAttr {
            encrypted: self.spec_encrypted() == 1,
            x: self.spec_nx() == 0,
            w: self.spec_write() == 1,
        }
    }
}

} // verus!
verus! {

#[verifier(inline)]
pub open spec fn lvl_to_size(lvl: nat) -> nat {
    if lvl == 0 {
        0x1000
    } else if lvl == 1 {
        0x20_0000
    } else if lvl == 2 {
        0x10_0000_0000
    } else if lvl == 3 {
        0x1_0000_0000_0000
    } else if lvl == 4 {
        0x1000_0000_0000_0000
    } else {
        0
    }
}

impl PtePerm {
    pub closed spec fn perm(&self) -> Option<SnpPointsTo<PageTable>> {
        self.perm
    }

    pub closed spec fn next_tb(&self) -> PageTable {
        self.perm().get_Some_0()@.get_value()
    }

    pub closed spec fn next_tbptr(&self) -> int {
        let ppage: int = self.val.spec_page() as int;
        spec_page_table_pa_to_va(ppage.to_addr())
    }

    pub closed spec fn val(&self) -> PTE {
        self.val
    }

    spec fn wf_current_psize(&self) -> bool {
        if self.lvl != 1 && self.lvl != 2 {
            &&& self.val.spec_psize() == 0
        } else {
            true
        }
    }

    spec fn wf_range(&self) -> bool {
        lvl_to_size(self.lvl) == self.range.1
    }

    spec fn wf_current_perm(&self) -> bool {
        // The last level does not carry any mem perm
        // since those are used as non-pt memory.
        if self.has_next() {
            self.wf_current_perm_with_mem()
        } else {
            self.perm.is_None()
        }
    }

    // When write pte val, we provide both pt and non-pt memory perm.
    spec fn wf_current_perm_with_mem(&self) -> bool {
        let perm = self.perm.get_Some_0();
        &&& self.perm.is_Some()
        &&& perm@.value().is_Some()
        &&& perm@.is_wf_pte(self.next_tbptr())
    }

    pub closed spec fn wf(&self, lvl_idx: (nat, int)) -> bool {
        &&& self.wf_current_psize()
        &&& self.wf_current_perm()
        &&& self.wf_range()
        &&& self.lvl == lvl_idx.0
        &&& self.range.0 == lvl_idx.1
    }

    pub closed spec fn has_next(&self) -> bool {
        if self.lvl != PAGE_TABLE_LEVELS {
            &&& self.val.has_next()
            &&& self.lvl != 0
        } else {
            true
        }
    }
}

} // verus!
verus! {

impl TrackedPTEPerms {
    pub open spec fn invfn() -> spec_fn(TrackedPTEPerms) -> bool {
        |v: TrackedPTEPerms| wf_ptes(v@)
    }

    pub open spec fn view(&self) -> PtePerms {
        self.perms@
    }
}

} // verus!
verus! {

impl PtePermsTrait for PtePerms {
    open spec fn pte(&self, vaddr: int) -> Option<PtePerm> {
        self.entry(vaddr, 0)
    }

    open spec fn pde(&self, vaddr: int) -> Option<PtePerm> {
        self.entry(vaddr, 1)
    }

    open spec fn pdpe(&self, vaddr: int) -> Option<PtePerm> {
        self.entry(vaddr, 2)
    }

    open spec fn pml4e(&self, vaddr: int) -> Option<PtePerm> {
        self.entry(vaddr, 3)
    }

    closed spec fn entry(&self, vaddr: int, lvl: nat) -> Option<PtePerm> {
        let lvl_idx = (lvl, vaddr / PAGE_SIZE!());
        if self.contains_key(lvl_idx) {
            Some(self[lvl_idx])
        } else {
            None
        }
    }
}

pub open spec fn lvl_index(lvl: nat, addr: int) -> (nat, int) {
    (lvl, spec_align_down(addr, lvl_to_size(lvl) as int))
}

pub proof fn lemma_max_lvl_index(lvl: nat, addr: int) -> (ret: (nat, int))
    requires
        addr.spec_valid_addr_with(0x1000),
        lvl == PAGE_TABLE_LEVELS,
    ensures
        ret.1 == 0,
        ret === lvl_index(lvl, addr),
{
    let ret = lvl_index(lvl, addr);
    assert(spec_align_down(addr, lvl_to_size(lvl) as int) == 0) by {
        assert(lvl_to_size(lvl) == L4_MAX_ADDR);
        assert(0 <= addr < L4_MAX_ADDR);
        assert(addr / (L4_MAX_ADDR as int) * L4_MAX_ADDR as int == 0);
    }
    ret
}

pub closed spec fn pte_perms_wf_prev(perms: PtePerms, lvl: nat, addr: int) -> bool {
    let prev_idx = lvl_index(lvl + 1, addr);
    let idx = lvl_index(lvl, addr);
    &&& (perms.contains_key(prev_idx) && perms[prev_idx].has_next()) == perms.contains_key(idx)
    &&& perms[idx].val().value === perms[prev_idx].next_tb()[spec_table_index(
        addr as u64,
        lvl,
    )].vspec_cast_to()
}

pub open spec fn wf_ptes(m: Map<(nat, int), PtePerm>) -> bool {
    &&& m[(PAGE_TABLE_LEVELS as nat, 0)].val().value == static_cr3_value()
    &&& m.contains_key(top_lvl_idx())
    // All existed entries are valid
    &&& forall|i|
        m.contains_key(i) ==> #[trigger] m[i].wf(
            i,
        )
    // When an entry exists
    &&& forall|lvl: nat, addr: int| 0 <= lvl < 4 ==> pte_perms_wf_prev(m, lvl, addr)
}

spec fn pte_perms_contains(perms: PtePerms, lvl: nat, addr: int) -> bool {
    {
        &&& forall|i| perms.contains_key(i) ==> #[trigger] perms[i].wf(i)
        &&& perms.contains_key(top_lvl_idx())
        &&& forall|l: nat|
            lvl <= l < 4 ==> #[trigger] perms.contains_key(lvl_index(l, addr)) == (
            perms.contains_key(lvl_index(l + 1, addr)) && perms[lvl_index(l + 1, addr)].has_next())
    }
}

} // verus!
#[vbit_struct(VAddrIndex, u64)]
#[derive(IsConstant)]
pub struct SpecVAddrIndex {
    #[vbits(12, 20)]
    pub index0: u64,
    #[vbits(21, 29)]
    pub index1: u64,
    #[vbits(30, 38)]
    pub index2: u64,
    #[vbits(39, 47)]
    pub index3: u64,
}

verus! {

spec fn spec_page_table_pa_to_va(pa: int) -> int {
    pa
}

pub closed spec fn spec_table_index(vaddr: u64, lvl: nat) -> int {
    let ret = if lvl == 0 {
        VAddrIndex::spec_new(vaddr).spec_index0()
    } else if lvl == 1 {
        VAddrIndex::spec_new(vaddr).spec_index1()
    } else if lvl == 2 {
        VAddrIndex::spec_new(vaddr).spec_index2()
    } else if lvl == 3 {
        VAddrIndex::spec_new(vaddr).spec_index3()
    } else {
        0
    };
    ret as int
}

pub proof fn proof_table_index(vaddr: u64, lvl: nat)
    ensures
        0 <= spec_table_index(vaddr, lvl) < PT_ENTRY_NUM,
        PT_ENTRY_NUM == 512,
{
    entry_p::lemma_pt_entry_count();
    let addr_index = VAddrIndex { value: vaddr };
    addr_index.lemma_bound_index0();
    assert(0 <= addr_index.spec_index0() < PT_ENTRY_NUM);
    addr_index.lemma_bound_index1();
    assert(0 <= addr_index.spec_index1() < PT_ENTRY_NUM);
    addr_index.lemma_bound_index2();
    assert(0 <= addr_index.spec_index2() < PT_ENTRY_NUM);
    addr_index.lemma_bound_index3();
    assert(0 <= addr_index.spec_index3() < PT_ENTRY_NUM);
}

} // verus!
verus! {

fn next_addr(vaddr: u64) -> (ret: u64)
    ensures
        ret == vaddr / 0x200 * 0x200,
{
    vaddr / 0x200 * 0x200
}

fn table_index(vaddr: u64, lvl: u8) -> (ret: usize)
    ensures
        0 <= ret < PT_ENTRY_NUM,
        PT_ENTRY_NUM == 512,
        (ret as int) == spec_table_index(vaddr, lvl as nat),
{
    proof {
        proof_table_index(vaddr as u64, lvl as nat);
    }
    let ret = if lvl == 0 {
        VAddrIndex::new(vaddr).get_index0()
    } else if lvl == 1 {
        VAddrIndex::new(vaddr).get_index1()
    } else if lvl == 2 {
        VAddrIndex::new(vaddr).get_index2()
    } else if lvl == 3 {
        VAddrIndex::new(vaddr).get_index3()
    } else {
        0
    };
    ret as usize
}

} // verus!
verus! {

#[derive(IsConstant)]
pub struct PTEWithPtr {
    pte: PTE,
    ptr: Option<SnpPPtr<PageTable>>,
    index: usize_t,
}

pub fn check_is_encrypted(
    vaddr: usize,
    Tracked(mem_perm): Tracked<&SnpPointsToRaw>,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
) -> (ret: Option<bool>)
    requires
        (*old(cs)).inv(),
        (vaddr as int).spec_valid_addr_with(0x1000),
        mem_perm@.wf_range((vaddr as int, PAGE_SIZE as nat)),
    ensures
        (*cs).inv(),
        (*cs).only_lock_reg_updated((*old(cs)), set![], set![spec_PT().lockid()]),
        ret.is_Some() ==> ret.get_Some_0() == mem_perm@.snp().encrypted(),
{
    match borrow_entry(vaddr as u64, 0, Tracked(mem_perm), Tracked(cs)) {
        Some(pte_with_ptr) => {
            let PTEWithPtr { pte, ptr, index } = pte_with_ptr;
            Some(pte.get_encrypted() == 1)
        },
        _ => { None },
    }
}

fn borrow_entry(
    vaddr: u64,
    lvl: u8,
    Tracked(mem_perm): Tracked<&SnpPointsToRaw>,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
) -> (ret: Option<PTEWithPtr>)
    requires
        (*old(cs)).inv(),
        (vaddr as int).spec_valid_addr_with(0x1000),
        lvl <= PAGE_TABLE_LEVELS,
        mem_perm@.wf_range((vaddr as int, PAGE_SIZE as nat)),
    ensures
        cs.inv(),
        ret.is_Some() ==> ret.is_constant(),
        cs.only_lock_reg_updated((*old(cs)), set![], set![spec_PT().lockid()]),
        (ret.is_Some() && (lvl == 0)) ==> wf_pte_mem_perm(ret.get_Some_0().pte, mem_perm),
{
    assert(cs.wf_top_pt());
    let ghost cr3_u64: u64 = cs.snpcore.regs[RegName::Cr3].val::<u64_s>().vspec_cast_to();
    assert(cr3_u64 == static_cr3_value());
    let tracked cr3perm = cs.snpcore.regs.tracked_borrow(RegName::Cr3);
    assert(contains_PT(cs.lockperms));
    let tracked mut pt_lock = cs.lockperms.tracked_remove(spec_PT_lockid());
    let (tracked_ptr, Tracked(mut ptperm_perm), Tracked(pt_lock)) = PT().acquire(
        Tracked(pt_lock),
        Tracked(&cs.snpcore.coreid),
    );
    let TrackedPTEPerms { perms } = tracked_ptr.take(Tracked(&mut ptperm_perm));
    let Tracked(mut pt_perms) = perms;
    assert(wf_ptes(pt_perms));
    let ghost cr3_u64: u64 = cr3perm.val::<u64_s>().vspec_cast_to();
    assert(cr3_u64 == static_cr3_value());
    assert(pt_perms[top_lvl_idx()].val().value == static_cr3_value());
    let ret = _borrow_entry(
        vaddr,
        lvl,
        Tracked(mem_perm),
        Tracked(cr3perm),
        Tracked(&mut pt_perms),
    );
    tracked_ptr.put(Tracked(&mut ptperm_perm), TrackedPTEPerms { perms: Tracked(pt_perms) });
    PT().release(Tracked(&mut pt_lock), Tracked(ptperm_perm), Tracked(&cs.snpcore.coreid));
    proof {
        cs.lockperms.tracked_insert(spec_PT_lockid(), pt_lock);
    }
    ret
}

pub closed spec fn cr3_to_pte_ptr(cr3perm: RegisterPermValue<u64_s>) -> PTEWithPtr {
    PTEWithPtr { pte: PTE::spec_new(cr3perm.value.vspec_cast_to()), ptr: None, index: 0 }
}

fn _borrow_entry(
    vaddr: u64,
    lvl: u8,
    Tracked(mem_perm): Tracked<&SnpPointsToRaw>,
    Tracked(cr3perm): Tracked<&RegisterPerm>,
    Tracked(pt_perms): Tracked<&mut PtePerms>,
) -> (ret: Option<PTEWithPtr>)
    requires
        (vaddr as int).spec_valid_addr_with(0x1000),
        lvl <= PAGE_TABLE_LEVELS,
        cr3perm.id() == CR3.reg_id(),
        cr3perm.wf_notshared(),
        cr3perm.val::<u64_s>().is_constant(),
        cr3perm.val::<u64_s>().vspec_cast_to() === old(pt_perms)[top_lvl_idx()].val().value,
        wf_ptes(*old(pt_perms)),
        mem_perm@.wf_range((vaddr as int, PAGE_SIZE as nat)),
    ensures
        *pt_perms =~~= *old(pt_perms),
        ret.is_Some() ==> ret.is_constant(),
        ret.is_Some() ==> pt_perms[lvl_index(lvl as nat, vaddr as int)].val()
            === ret.get_Some_0().pte,
        ret.is_Some() ==> ret.get_Some_0().index == spec_table_index(vaddr, lvl as nat),
        ret.is_Some() ==> ret.get_Some_0().ptr.is_Some() == (lvl != PAGE_TABLE_LEVELS),
        ret.is_Some() && ret.get_Some_0().ptr.is_Some() ==> ret.get_Some_0().ptr.get_Some_0().id()
            == pt_perms[lvl_index(lvl as nat + 1, vaddr as int)].next_tbptr(),
        ret.is_Some() ==> pt_perms.contains_key(lvl_index(lvl as nat, vaddr as int)),
        (ret.is_Some() && (lvl == 0)) ==> wf_pte_mem_perm(ret.get_Some_0().pte, mem_perm),
        lvl == PAGE_TABLE_LEVELS ==> ret === Some(cr3_to_pte_ptr(cr3perm@)),
{
    let ghost old_pt_perms = *pt_perms;
    proof {
        axiom_rel_pt_perm_mem_perm(pt_perms, mem_perm);
    }
    let ghost mut lvl_idx;
    let ghost glvl = lvl as nat;
    let ghost gaddr = vaddr as int;
    proof {
        lvl_idx = lvl_index(glvl, gaddr);
    }
    if lvl == PAGE_TABLE_LEVELS {
        let cr3 = CR3.read(Tracked(cr3perm));
        proof {
            assert(lvl_idx.1 == 0) by {
                lemma_max_lvl_index(glvl, gaddr);
            }
            assert(lvl_idx === top_lvl_idx());
            assert(pt_perms[lvl_idx].val().value === cr3perm.val::<u64_s>().vspec_cast_to());
            assert(cr3 === cr3perm@.value());
        }
        //(new_strlit("cr3"), cr3).leak_debug();
        return Some(PTEWithPtr { pte: PTE::new(cr3.into()), ptr: None, index: 0 });
    }
    let tracked mut prev_pt_perms = pt_perms.tracked_remove_keys(pt_perms.dom());
    proof {
        assert(prev_pt_perms =~~= old_pt_perms);
    }
    let prev = _borrow_entry(
        vaddr,
        lvl + 1,
        Tracked(mem_perm),
        Tracked(cr3perm),
        Tracked(&mut prev_pt_perms),
    );
    let ghost prev_lvl_idx = lvl_index(glvl + 1, gaddr);
    proof {
        pt_perms.tracked_union_prefer_right(prev_pt_perms);
        assert(*pt_perms =~~= old_pt_perms);
    }
    let ret = if let Some(tmp) = prev {
        let prev_entry = tmp.pte;
        if (lvl + 1) == PAGE_TABLE_LEVELS || (prev_entry.get_psize() == 0
            && prev_entry.get_present() == 1) {
            proof {
                assert(pt_perms.contains_key(prev_lvl_idx));
                assert(prev_pt_perms[prev_lvl_idx] === pt_perms[prev_lvl_idx]);
                assert(pt_perms[prev_lvl_idx].wf(prev_lvl_idx));
                assert(PTE::spec_new(prev.get_Some_0().pte.value.vspec_cast_to())
                    === pt_perms[prev_lvl_idx].val());
                //assert(prev.get_Some_0().pte === pt_perms[prev_lvl_idx].val());
                prev.get_Some_0().pte.lemma_new_eq();
                assert(pt_perms[prev_lvl_idx].has_next());
                assert(pte_perms_wf_prev(*pt_perms, glvl, gaddr));
                assert(pt_perms.contains_key(lvl_idx));
            }
            let tracked pte_perm = pt_perms.tracked_remove(prev_lvl_idx);
            let tracked PtePerm { lvl: lvl_nat, val, range, perm } = pte_perm;
            let ppage: usize = prev_entry.get_page() as usize;  // ppage == start_page.
            let page_table_ptr = SnpPPtr::<PageTable>::from_usize(ppage.to_addr());
            assert(perm.is_Some());
            let tracked perm = perm.tracked_unwrap();
            let page_table = page_table_ptr.borrow(Tracked(&perm));
            let idx = table_index(vaddr, lvl);
            assert(page_table@.len() == PT_ENTRY_NUM);
            assert(idx < PT_ENTRY_NUM);
            let pte_val = *page_table.index(idx);
            let ret = PTEWithPtr {
                pte: PTE::new(pte_val.into()),
                ptr: Some(page_table_ptr),
                index: idx,
            };
            proof {
                ret.pte.lemma_new_eq();
                pt_perms[lvl_index(lvl as nat, vaddr as int)].val().lemma_new_eq();
                assert(ret.index == spec_table_index(vaddr, lvl as nat));
                let tracked pte_perm = PtePerm { lvl: lvl_nat, val, range, perm: Some(perm) };
                pt_perms.tracked_insert(prev_lvl_idx, pte_perm);
            }
            //(new_strlit("pte_val"), pte_val).leak_debug();
            Some(ret)
        } else {
            None
        }
    } else {
        None
    };
    return ret;
}

} // verus!
verus! {

// Push a new pte into the mem perm.
// When there are more than one pte in the queue,
// we do not guarantee the actual pte used by the perm token.
// To enforce the use of the recent pte,
// tlb flush is required to remove any other potentials.
pub open spec fn write_pte_ensures_memperm(
    prev_pte: PTE,
    pte: PTE,
    prev_mem_perm: SnpPointsToBytes,
    mem_perm: SnpPointsToBytes,
) -> bool {
    let same_map = prev_pte.spec_page() == pte.spec_page();
    let same_enc = prev_pte.spec_encrypted() == pte.spec_encrypted();
    &&& mem_perm.wf()
    &&& mem_perm.snp().pte == prev_mem_perm.snp().pte.push(pte.to_attr())
    &&& mem_perm.snp() === prev_mem_perm.snp().spec_set_pte(mem_perm.snp().pte)
    &&& mem_perm.snp.hw_rmp_wf()
    &&& mem_perm.range() === prev_mem_perm.range()
    &&& same_map && same_enc ==> mem_perm.bytes() === prev_mem_perm.bytes()
}

pub open spec fn write_pte_requires_memperm(
    val: PTE,
    addr: int,
    lvl: nat,
    mem_perms: Map<int, SnpPointsToRaw>,
) -> bool {
    let start = addr;
    let end = addr + lvl_to_size(lvl);
    forall|i: int|
        start <= i < end && i % PAGE_SIZE!() == 0 ==> #[trigger] mem_perms.contains_key(i)
            && mem_perms[i]@.wf_range((i, PAGE_SIZE as nat))
}

pub open spec fn write_pte_ensures(
    addr: int,
    lvl: nat,
    prev_pte: PTE,
    pte: PTE,
    prev_mem_perms: Map<int, SnpPointsToRaw>,
    mem_perms: Map<int, SnpPointsToRaw>,
) -> bool {
    let start = addr;
    let end = addr + lvl_to_size(lvl);
    forall|i: int|
        start <= i < end && i % PAGE_SIZE!() == 0 ==> #[trigger] mem_perms.contains_key(i)
            && write_pte_ensures_memperm(prev_pte, pte, prev_mem_perms[i]@, mem_perms[i]@)
}

impl SnpPPtr<u64_s> {
    // Requires to use permissions of all virtual memory related to the pte
    // mem_perms: page idx => memory perm.
    // Returns new memory permission tokens reflecting the updated pte.
    #[verifier(external_body)]
    fn write_pte(
        &self,
        val: PTE,
        Ghost(lvl): Ghost<(nat)>,
        Ghost(addr): Ghost<(int)>,
        Tracked(pte_perms): Tracked<&mut PtePerms>,
        Tracked(mem_perms): Tracked<&mut Map<int, SnpPointsToRaw>>,
    )
        requires
            wf_ptes(*old(pte_perms)),
            old(pte_perms).contains_key(lvl_index(lvl, addr)),
            old(pte_perms)[lvl_index(lvl + 1, addr)].next_tbptr() + spec_table_index(
                addr as u64,
                lvl,
            ) * 8 == self.id(),
            addr % (lvl_to_size(lvl) as int) == 0,
            write_pte_requires_memperm(val, addr, lvl, *old(mem_perms)),
        ensures
            pte_perms[lvl_index(lvl, addr)].val === val,
            write_pte_ensures(
                addr,
                lvl,
                old(pte_perms)[lvl_index(lvl, addr)].val,
                val,
                *old(mem_perms),
                *mem_perms,
            ),
    {
        self.replace(Tracked::assume_new(), val.value.into());
    }
}

} // verus!
verus! {

// Hold mem perm to ensure that no concurrent use of the memory.
// The mem perm will be updated to reflect the new PTE value.
// Return true if succeeds.
pub open spec fn ensures_mem_enc_dec_memperm(
    enc: bool,
    prev_mem_perm: SnpPointsToRaw,
    mem_perm: SnpPointsToRaw,
) -> bool {
    &&& prev_mem_perm@.snp().spec_set_pte(seq![mem_perm@.snp().pte()]) === mem_perm@.snp()
    &&& mem_perm@.snp().pte() === prev_mem_perm@.snp().pte().spec_set_encrypted(enc)
    &&& prev_mem_perm@.snp().pte().spec_encrypted() != enc
    &&& prev_mem_perm@.bytes() === mem_perm@.bytes()
    &&& prev_mem_perm@.range() === mem_perm@.range()
}

pub fn set_page_enc_dec(
    vaddr: u64,
    enc: bool,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
    Tracked(mem_perm0): Tracked<&mut Map<int, SnpPointsToRaw>>,
) -> (ret: bool)
    requires
        (*old(cs)).inv(),
        (vaddr as int).spec_valid_addr_with(PAGE_SIZE as nat),
        (vaddr as int) % PAGE_SIZE!() == 0,
        old(mem_perm0).contains_key(0),
        old(mem_perm0)[0]@.wf_range((vaddr as int, PAGE_SIZE as nat)),
    ensures
        cs.inv(),
        cs.only_lock_reg_updated((*old(cs)), set![], set![spec_PT().lockid()]),
        ret ==> ensures_mem_enc_dec_memperm(enc, old(mem_perm0)[0], mem_perm0[0]),
        !ret ==> mem_perm0[0] === old(mem_perm0)[0],
        mem_perm0.contains_key(0),
        mem_perm0[0]@.wf_range((vaddr as int, PAGE_SIZE as nat)),
{
    let ghost addr_id: int = vaddr.vspec_cast_to();
    let ghost old_mem_perm0 = *mem_perm0;
    let tracked cr3perm = cs.snpcore.regs.tracked_borrow(RegName::Cr3);
    assert(contains_PT(cs.lockperms));
    let tracked mut pt_lock = cs.lockperms.tracked_remove(spec_PT_lockid());
    let (tracked_ptr, Tracked(mut ptperm_perm), Tracked(pt_lock)) = PT().acquire(
        Tracked(pt_lock),
        Tracked(&cs.snpcore.coreid),
    );
    // Dummy take to get PTE permission.
    let TrackedPTEPerms { perms } = tracked_ptr.take(Tracked(&mut ptperm_perm));
    let Tracked(mut pt_perms) = perms;
    let lvl = 0;
    assert(wf_ptes(pt_perms));
    let pte_val_opt = _borrow_entry(
        vaddr,
        lvl,
        Tracked(mem_perm0.tracked_borrow(0)),
        Tracked(cr3perm),
        Tracked(&mut pt_perms),
    );
    let ret = if let Option::Some(pte_with_ptr) = pte_val_opt {
        let PTEWithPtr { pte, ptr, index } = pte_with_ptr;
        assert(ptr.is_Some());
        let mut pte_addr: usize = ptr.unwrap().to_usize();
        let encryption = if enc {
            1
        } else {
            0
        };
        if pte.get_encrypted() != encryption {
            let new_pte = pte.set_encrypted(encryption);
            let tracked mut memmap_perm = Map::<int, SnpPointsToRaw>::tracked_empty();
            proof {
                let tracked mem_perm = mem_perm0.tracked_remove(0);
                memmap_perm.tracked_insert(addr_id, mem_perm);
                proof_table_index(vaddr, lvl as nat);
            }
            pte_addr = pte_addr + index * 8;
            let pte_ptr = SnpPPtr::<u64_s>::from_usize(pte_addr);
            proof {
                assert(memmap_perm.contains_key(addr_id));
            }
            pte_ptr.write_pte(
                new_pte,
                Ghost(lvl as nat),
                Ghost(addr_id),
                Tracked(&mut pt_perms),
                Tracked(&mut memmap_perm),
            );
            proof {
                assert(memmap_perm.contains_key(addr_id));
            }
            let tracked mut mem_perm = memmap_perm.tracked_remove(addr_id);
            invlpg(vaddr, Tracked(&mut mem_perm));
            proof {
                mem_perm0.tracked_insert(0, mem_perm);
            }
            true
        } else {
            (new_strlit("double private/share from richos\n"), pte.get_encrypted()).leak_debug();
            false
        }
    } else {
        false
    };
    tracked_ptr.put(Tracked(&mut ptperm_perm), TrackedPTEPerms { perms: Tracked(pt_perms) });
    PT().release(Tracked(&mut pt_lock), Tracked(ptperm_perm), Tracked(&cs.snpcore.coreid));
    proof {
        cs.lockperms.tracked_insert(spec_PT_lockid(), pt_lock);
    }
    return ret;
}

pub fn set_pages_enc_dec(
    start_page: u64,
    size: u64,
    enc: bool,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
    Tracked(mem_perms): Tracked<&mut Map<int, SnpPointsToRaw>>,
)
    requires
        (*old(cs)).inv(),
        start_page.spec_valid_pn_with(size as nat),
        forall|page: int|
            start_page <= page < start_page + size ==> old(mem_perms).contains_key(page) && old(
                mem_perms,
            )[page]@.wf_range((page.to_addr(), PAGE_SIZE as nat)),
    ensures
        cs.inv(),
        cs.only_lock_reg_updated((*old(cs)), set![], set![spec_PT().lockid()]),
        mem_perms.dom() =~~= old(mem_perms).dom(),
        forall|page: int|
            start_page <= page < start_page + size ==> #[trigger] mem_perms.contains_key(page)
                && mem_perms[page]@.wf_range((page.to_addr(), PAGE_SIZE as nat))
                && ensures_mem_enc_dec_memperm(enc, old(mem_perms)[page], mem_perms[page]),
{
    let mut i = 0;
    let ghost old_mem_perms = *mem_perms;
    let ghost old_cs = (*cs);
    while i < size
        invariant
            i <= size,
            (*cs).inv(),
            (*cs).only_lock_reg_updated(old_cs, set![], set![spec_PT().lockid()]),
            start_page.spec_valid_pn_with(size as nat),
            mem_perms.dom() =~~= old_mem_perms.dom(),
            forall|page: int|
                start_page <= page < start_page + size ==> #[trigger] mem_perms.contains_key(page)
                    && mem_perms[page]@.wf_range((page.to_addr(), PAGE_SIZE as nat)),
            forall|page: int|
                start_page + i <= page < start_page + size ==> old_mem_perms[page]
                    === #[trigger] mem_perms[page],
            forall|page: int|
                start_page <= page < start_page + i ==> #[trigger] mem_perms.contains_key(page)
                    && ensures_mem_enc_dec_memperm(enc, old_mem_perms[page], mem_perms[page]),
    {
        let tracked mut mem_perm0 = Map::tracked_empty();
        let page = start_page + i;
        let ghost oldperm = mem_perms[page as int];
        let ghost prev_cs = (*cs);
        proof {
            mem_perm0.tracked_insert(0, mem_perms.tracked_remove(page as int));
        }
        let ok = set_page_enc_dec(page.to_addr(), enc, Tracked(cs), Tracked(&mut mem_perm0));
        if !ok {
            new_strlit("\nfailed set_pages_enc_dec\n").leak_debug();
            vc_terminate(SM_TERM_MEM, Tracked(&mut cs.snpcore));
        }
        i = i + 1;
        proof {
            let ghost newperm = mem_perm0[0];
            old_cs.lemma_update_prop(
                prev_cs,
                (*cs),
                set![],
                set![spec_PT().lockid()],
                set![],
                set![spec_PT().lockid()],
            );
            mem_perms.tracked_insert(page as int, mem_perm0.tracked_remove(0));
            assert(old_mem_perms[page as int] === oldperm);
            assert(mem_perms[page as int] === newperm);
            assert(ensures_mem_enc_dec_memperm(enc, oldperm, newperm));
        }
    }
}

pub open spec fn wf_pte_mem_perm(pte: PTE, perm: &SnpPointsToRaw) -> bool {
    &&& (pte@.spec_encrypted() == 1)
        == perm@.snp().pte().spec_encrypted()/*&&& (pte@.spec_nx() == 0)== perm@.snp().pte().spec_x()
    &&& (pte@.spec_write() == 1) == perm@.snp().pte().spec_w()*/

}

// trusted hardware spec indicating the page table defines the access permission.
#[verifier(external_body)]
pub proof fn axiom_rel_pt_perm_mem_perm(tracked pte_perms: &PtePerms, tracked perm: &SnpPointsToRaw)
    ensures
        wf_pte_mem_perm(pte_perms[lvl_index(0, perm@.range().0)].val, perm),
{
}

} // verus!
