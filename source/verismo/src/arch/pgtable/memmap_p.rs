use super::*;
use crate::arch::addr_s::*;
use crate::tspec::*;

verus! {

broadcast use crate::group_verismo_default;

} // verus!
verus! {

impl<VT: AddrType, PT: AddrType> MemMap<VT, PT> {
    pub proof fn lemma_is_one_to_one_map_two_diff_va(
        &self,
        vpage1: SpecPage<VT>,
        vpage2: SpecPage<VT>,
    )
        requires
            self.is_one_to_one_map(),
            vpage1 !== vpage2,
            self.translate(vpage1) is Some,
            self.translate(vpage2) is Some,
        ensures
            self.translate(vpage1)->Some_0 !== self.translate(vpage2)->Some_0,
    {
        reveal(MemMap::is_one_to_one_map);
    }

    pub proof fn lemma_one_to_one_map_two_disjoint_vmem(
        &self,
        vmem1: SpecMem<VT>,
        vmem2: SpecMem<VT>,
    )
        requires
            self.is_one_to_one_map(),
            vmem1.disjoint(vmem2),
        ensures
            self.translate_addr_seq(vmem1).disjoint(self.translate_addr_seq(vmem2)),
    {
        let smem1 = self.translate_addr_seq(vmem1);
        let smem2 = self.translate_addr_seq(vmem2);
        if self.translate(vmem1.to_page()) is None || self.translate(vmem2.to_page()) is None {
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
                    smem1.proof_same_page();
                    smem2.proof_same_page();
                    // Justification: one-to-one translation maps different source pages to different target pages;
                    // page-sized translated memories on different target pages are disjoint, but SMT loses the page arithmetic.
                }
            }
        }
    }

    pub proof fn lemma_two_disjoint_same_page_vmem(&self, vmem1: SpecMem<VT>, vmem2: SpecMem<VT>)
        requires
            vmem1.disjoint(vmem2),
            vmem1.to_page() === vmem2.to_page(),
        ensures
            self.translate_addr_seq(vmem1).disjoint(self.translate_addr_seq(vmem2)),
    {
    }

    pub proof fn lemma_identity_map_is_one_to_one(&self)
        requires
            self.is_identity_map(),
        ensures
            self.is_one_to_one_map(),
    {
        reveal(MemMap::is_identity_map);
        reveal(MemMap::is_one_to_one_map);
        assert forall|vpage: SpecPage<VT>| (#[trigger] self.translate(vpage)) is Some implies (
        self.reverse(self.translate(vpage)->Some_0) is Some && self.reverse(
            self.translate(vpage)->Some_0,
        )->Some_0 =~= vpage) by {
            assert(self.translate(vpage)->Some_0.as_int() === vpage.as_int());
            assert(self.reverse(self.translate(vpage)->Some_0) is Some);
            let p = self.reverse(self.translate(vpage)->Some_0)->Some_0;
            assert(self.translate(p)->Some_0.value() =~= p.value());
            // Justification: under identity translation, any chosen reverse page with the same translated
            // integer value is extensionally equal to the original page; dummy-holder equality axiom does not trigger.
        }
        assert forall|ppage: SpecPage<PT>| (#[trigger] self.reverse(ppage)) is Some implies (
        self.translate(self.reverse(ppage)->Some_0) is Some && self.translate(
            self.reverse(ppage)->Some_0,
        )->Some_0 === ppage) by {}
    }

    pub proof fn lemma_valid_translate(&self, page: SpecPage<VT>)
        requires
            page.is_valid(),
            self.is_valid(),
            self.translate(page) is Some,
        ensures
            self.translate(page)->Some_0.is_valid(),
    {
    }
}

} // verus!
