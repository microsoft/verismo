use super::*;
use crate::arch::addr_s::*;
use crate::tspec::*;

verus! {
impl<VT: AddrType, PT: AddrType> MemMap<VT, PT>
{
pub proof fn lemma_is_one_to_one_map_two_diff_va(&self, vpage1: SpecPage<VT>, vpage2: SpecPage<VT>)
requires
    self.is_one_to_one_map(),
    vpage1 !== vpage2,
    self.translate(vpage1).is_Some(),
    self.translate(vpage2).is_Some(),
ensures
    self.translate(vpage1).get_Some_0() !== self.translate(vpage2).get_Some_0(),
{
    reveal(MemMap::is_one_to_one_map);
}

pub proof fn lemma_one_to_one_map_two_disjoint_vmem(&self, vmem1: SpecMem<VT>, vmem2: SpecMem<VT>)
requires
    self.is_one_to_one_map(),
    vmem1.disjoint(vmem2),
ensures
    self.translate_addr_seq(vmem1).disjoint(self.translate_addr_seq(vmem2)),
{
    let smem1 = self.translate_addr_seq(vmem1);
    let smem2 = self.translate_addr_seq(vmem2);
    if  self.translate(vmem1.to_page()).is_None() || self.translate(vmem2.to_page()).is_None()
    {
        assert(smem1.len() == 0 || smem2.len() == 0);
        assert(smem1.disjoint(smem2));
    } else {
        reveal(MemMap::is_one_to_one_map);
        if smem1.to_page() === smem2.to_page() {
            assert(vmem1.to_page() === vmem2.to_page());
            assert(smem1.disjoint(smem2));
        } else {
            assert(smem1.disjoint(smem2)) by {
                reveal(MemMap::is_one_to_one_map);
            }
        }
    }
}

pub proof fn lemma_two_disjoint_same_page_vmem(&self, vmem1: SpecMem<VT>, vmem2: SpecMem<VT>)
requires
    vmem1.disjoint(vmem2),
    vmem1.to_page() === vmem2.to_page(),
ensures
    self.translate_addr_seq(vmem1).disjoint(self.translate_addr_seq(vmem2))
{}

pub proof fn lemma_identity_map_is_one_to_one(&self)
requires
    self.is_identity_map(),
ensures
    self.is_one_to_one_map(),
{
    reveal(MemMap::is_identity_map);
    reveal(MemMap::is_one_to_one_map);
    assert forall |vpage: SpecPage<VT>|
        (#[trigger] self.translate(vpage)).is_Some()
    implies
        (self.reverse(self.translate(vpage).get_Some_0()).is_Some() &&
        self.reverse(self.translate(vpage).get_Some_0()).get_Some_0() =~= vpage)
    by {
        assert(self.translate(vpage).get_Some_0().as_int() === vpage.as_int());
        assert(self.reverse(self.translate(vpage).get_Some_0()).is_Some());
        let p = self.reverse(self.translate(vpage).get_Some_0()).get_Some_0();
        assert(self.translate(p).get_Some_0().value() =~= p.value());
    }
    assert forall |ppage: SpecPage<PT>|
        (#[trigger] self.reverse(ppage)).is_Some()
    implies
        (self.translate(self.reverse(ppage).get_Some_0()).is_Some() &&
        self.translate(self.reverse(ppage).get_Some_0()).get_Some_0() ===
        ppage)
    by {}
}

pub proof fn lemma_valid_translate(&self, page: SpecPage<VT>)
requires
    page.is_valid(),
    self.is_valid(),
    self.translate(page).is_Some(),
ensures
    self.translate(page).get_Some_0().is_valid(),
{

}
}
}
