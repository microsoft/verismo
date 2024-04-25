use crate::addr_e::*;
use crate::arch::addr_s::PAGE_SIZE;
use crate::debug::VPrintAtLevel;
use crate::global::*;
use crate::pgtable_e::*;
use crate::ptr::*;
use crate::snp::ghcb::*;
use crate::snp::SnpCoreSharedMem;
use crate::tspec::*;
use crate::tspec_e::*;
use crate::vbox::VBox;

verus! {

pub open spec fn mk_shared_ensures_pageperm(
    prev_page_perm: SnpPointsToBytes,
    page_perm: SnpPointsToBytes,
) -> bool {
    &&& page_perm.wf_range(prev_page_perm.range())
    &&& page_perm.snp().is_shared_from(prev_page_perm.snp())
}

pub proof fn lemma_mk_shared_default_to_shared(
    prev_page_perm: SnpPointsToBytes,
    page_perm: SnpPointsToBytes,
)
    requires
        mk_shared_ensures_pageperm(prev_page_perm, page_perm),
        prev_page_perm.snp() === SwSnpMemAttr::spec_default(),
        prev_page_perm.wf(),
    ensures
        page_perm.snp() === SwSnpMemAttr::shared(),
{
    assert(page_perm.snp().pte =~~= SwSnpMemAttr::shared().pte);
}

proof fn lemma_mk_private_shared_to_default(
    prev_page_perm: SnpPointsToBytes,
    page_perm: SnpPointsToBytes,
)
    requires
        mk_private_ensures_pageperm(prev_page_perm, page_perm),
        prev_page_perm.snp() === SwSnpMemAttr::shared(),
        prev_page_perm.wf(),
    ensures
        page_perm.snp() === SwSnpMemAttr::spec_default(),
{
    assert(page_perm.snp().pte =~~= SwSnpMemAttr::spec_default().pte);
}

pub open spec fn mk_private_ensures_pageperm(
    prev_page_perm: SnpPointsToBytes,
    page_perm: SnpPointsToBytes,
) -> bool {
    &&& page_perm.wf_range(prev_page_perm.range())
    &&& page_perm.snp().is_vmpl0_private()
    &&& page_perm.snp().pte() === prev_page_perm.snp().pte().spec_set_encrypted(true)
    &&& page_perm.snp() === prev_page_perm.snp().spec_set_pte(page_perm.snp().pte).spec_set_rmp(
        page_perm.snp().rmp,
    )
    &&& page_perm.snp().rmp === SwSnpMemAttr::spec_default().rmp
}

pub open spec fn spec_is_shared_page_perms(
    page_perms: Map<int, SnpPointsToRaw>,
    start_page: int,
    npages: nat,
) -> bool {
    forall|i|
        start_page <= i < (start_page + npages) ==> #[trigger] page_perms.contains_key(i)
            && page_perms[i]@.wf_range((i.to_addr(), PAGE_SIZE as nat)) && page_perms[i]@.snp()
            === SwSnpMemAttr::shared()
}

pub open spec fn spec_is_vmprivate_const_perms(
    page_perms: Map<int, SnpPointsToRaw>,
    start_page: int,
    npages: nat,
) -> bool {
    forall|i|
        start_page <= i < (start_page + npages) ==> #[trigger] page_perms.contains_key(i)
            && page_perms[i]@.wf_range((i.to_addr(), PAGE_SIZE as nat))
            && page_perms[i]@.snp().requires_pvalidate(i.to_addr(), 0, 0)
            && page_perms[i]@.bytes().is_constant()
}

// Make a page as shared via GHCB MSR
pub fn early_mk_shared(
    start_page: u64,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
    Tracked(page_perm0): Tracked<&mut Map<int, SnpPointsToRaw>>,
)
    requires
        (*old(cs)).inv(),
        old(page_perm0).contains_key(0),
        old(page_perm0)[0]@.wf_const_default(((start_page as int).to_addr(), PAGE_SIZE as nat)),
    ensures
        (*cs).inv(),
        (*cs).only_lock_reg_coremode_updated(
            (*old(cs)),
            set![GHCB_REGID()],
            set![spec_PT().lockid()],
        ),
        page_perm0.contains_key(0),
        mk_shared_ensures_pageperm(old(page_perm0)[0]@, page_perm0[0]@),
{
    let page_op = PageOps::Shared;
    let tracked mut page_perm = page_perm0.tracked_remove(0);
    let ghost old_page_perm = page_perm;
    ghcb_change_page_state_via_msr(
        vn_to_pn(start_page, Tracked(&page_perm)) as usize,
        page_op,
        Tracked(&mut page_perm),
        Tracked(&mut cs.snpcore),
    );
    let ghost perm1 = page_perm;
    proof {
        page_perm0.tracked_insert(0, page_perm);
    }
    let ok = set_page_enc_dec(start_page.to_addr(), false, Tracked(cs), Tracked(page_perm0));
    if !ok {
        new_strlit("\nfailed early_mk_shared\n").leak_debug();
        vc_terminate(SM_TERM_MEM, Tracked(&mut cs.snpcore));
    }
}

} // verus!
verus! {

impl GhcbHandle {
    // start_page is virtual starting page;
    pub fn new_shared_vpage<T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>>(
        self,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
    ) -> (ret: (VBox<T>, Self))
        requires
            self.ghcb_wf(),
            (*old(cs)).inv_ac(),
            spec_size::<T>() == PAGE_SIZE,
        ensures
            (*cs).inv_ac(),
            (*cs).only_lock_reg_coremode_updated(
                (*old(cs)),
                set![],
                set![spec_ALLOCATOR_lockid(), spec_PT_lockid()],
            ),
            ret.0.snp() === SwSnpMemAttr::shared(),
            ret.0.is_shared_page(),
            ret.1.ghcb_wf(),
    {
        let ghost oldcs = (*cs);
        let ret: VBox<T> = VBox::new_aligned_uninit(PAGE_SIZE, Tracked(cs));
        let (ptr, Tracked(perm)) = ret.into_raw();
        let page: u64 = ptr.as_u64().to_page();
        let tracked mut page_perms = Map::tracked_empty();
        proof {
            assert(ptr.id().spec_valid_addr_with(spec_size::<T>()));
            page_perms.tracked_insert(page as int, perm.tracked_into_raw());
        }
        let ghost old_page_perms = page_perms;
        let ghost prevcs = (*cs);
        let handle = self.mk_shared(page, 1, Tracked(cs), Tracked(&mut page_perms));
        proof {
            assert(old_page_perms.contains_key(page as int));
            assert(page_perms.contains_key(page as int));
            oldcs.lemma_update_prop(
                prevcs,
                (*cs),
                set![],
                set![spec_ALLOCATOR_lockid()],
                set![],
                set![spec_PT_lockid()],
            );
            assert(set![spec_ALLOCATOR_lockid()].union(set![spec_PT_lockid()])
                =~~= set![spec_ALLOCATOR_lockid(), spec_PT_lockid()]);
            assert(mk_shared_ensures_pageperm(
                old_page_perms[page as int]@,
                page_perms[page as int]@,
            ));
            lemma_mk_shared_default_to_shared(
                old_page_perms[page as int]@,
                page_perms[page as int]@,
            );
            assert(page_perms[page as int]@.snp() === SwSnpMemAttr::shared());
        }
        let tracked perm = page_perms.tracked_remove(page as int).tracked_into();
        (VBox::from_raw(ptr.to_usize(), Tracked(perm)), handle)
    }

    pub fn mk_shared(
        self,
        start_page: u64,
        npages: u64,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
        Tracked(page_perms): Tracked<&mut Map<int, SnpPointsToRaw>>,
    ) -> (ret: Self)
        requires
            self.ghcb_wf(),
            (*old(cs)).inv(),
            npages > 0,
            spec_valid_page_state_change(start_page, npages as nat),
            wf_page_range(*old(page_perms), start_page as int, npages as nat),
        ensures
            ret.ghcb_wf(),
            ret.only_val_updated(self),
            (*cs).inv(),
            (*cs).only_lock_reg_coremode_updated((*old(cs)), set![], set![spec_PT_lockid()]),
            page_perms.dom() =~~= old(page_perms).dom(),
            forall|i|
                start_page <= i < (start_page + npages) ==> #[trigger] page_perms.contains_key(i)
                    && mk_shared_ensures_pageperm(old(page_perms)[i]@, page_perms[i]@),
    {
        let ghost oldcs = (*cs);
        let ghost old_page_perms = *page_perms;
        proof {
            assert(requires_pages_perms(*page_perms, start_page as int, npages as nat));
            assert(page_perms.contains_key(start_page as int));
        }
        let ret = self.ghcb_change_page_state_via_pg(
            vn_to_pn(start_page, Tracked(page_perms.tracked_borrow(start_page as int))),
            npages,
            PageOps::Shared,
            Tracked(page_perms),
            Tracked(cs),
        );
        let ghost prevcs = (*cs);
        proof {
            assert(forall|i|
                start_page <= i < (start_page + npages) ==> #[trigger] page_perms.contains_key(i)
                    && ensure_page_perm_change_state(
                    old_page_perms[i],
                    page_perms[i],
                    i,
                    PageOps::Shared,
                ));
            assert forall|i|
                start_page <= i < (start_page + npages) implies #[trigger] page_perms.contains_key(
                i,
            ) && ensure_page_perm_change_state(
                old_page_perms[i],
                page_perms[i],
                i,
                PageOps::Shared,
            ) by {
                assert(old_page_perms.contains_key(i));
                assert(page_perms.contains_key(i));
            }
            assert forall|i: int|
                start_page <= i < start_page + npages implies page_perms.contains_key(i)
                && page_perms[i]@.wf_range((i.to_addr(), PAGE_SIZE as nat)) by {
                assert(page_perms.contains_key(i));
                assert(old_page_perms.contains_key(i));
                assert(old_page_perms[i]@.wf_range((i.to_addr(), PAGE_SIZE as nat)));
            }
        }
        let ghost prev_page_perms = *page_perms;
        set_pages_enc_dec(start_page, npages as u64, false, Tracked(cs), Tracked(page_perms));
        proof {
            oldcs.lemma_update_prop(
                prevcs,
                (*cs),
                set![],
                set![],
                set![],
                set![spec_PT().lockid()],
            );
            assert(set![].union(set![spec_PT().lockid()]) =~~= set![spec_PT().lockid()]);
            assert forall|i|
                start_page <= i < (start_page + npages) implies #[trigger] page_perms.contains_key(
                i,
            ) && mk_shared_ensures_pageperm(old_page_perms[i]@, page_perms[i]@) by {
                assert(old_page_perms.contains_key(i));
                assert(prev_page_perms.contains_key(i));
                assert(page_perms.contains_key(i));
                let oldp = old_page_perms[i];
                let prevp = prev_page_perms[i];
                let p = page_perms[i];
                assert(oldp@.wf_range((i.to_addr(), PAGE_SIZE as nat)));
                assert(ensure_page_perm_change_state(oldp, prevp, i, PageOps::Shared));
                assert(ensures_mem_enc_dec_memperm(false, prevp, p));
                assert(p@.wf_range(oldp@.range()));
                assert(p@.snp().is_shared_from(oldp@.snp()));
                assert(p@.snp().is_shared());
            }
        }
        ret
    }

    pub fn mk_private(
        self,
        start_page: u64,
        npages: u64,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
        Tracked(page_perms): Tracked<&mut Map<int, SnpPointsToRaw>>,
    ) -> (ret: Self)
        requires
            self.ghcb_wf(),
            (*old(cs)).inv(),
            npages > 0,
            spec_valid_page_state_change(start_page, npages as nat),
            wf_page_range(*old(page_perms), start_page as int, npages as nat),
        ensures
            ret.ghcb_wf(),
            ret.only_val_updated(self),
            (*cs).inv(),
            (*cs).only_lock_reg_coremode_updated((*old(cs)), set![], set![spec_PT_lockid()]),
            page_perms.dom() =~~= old(page_perms).dom(),
            forall|i|
                start_page <= i < (start_page + npages) ==> #[trigger] page_perms.contains_key(i)
                    && mk_private_ensures_pageperm(old(page_perms)[i]@, page_perms[i]@),
    {
        let end_page = start_page + npages;
        let ghost oldcs = (*cs);
        let ghost old_page_perms = *page_perms;
        proof {
            assert(page_perms.contains_key(start_page as int));
        }
        let ret = self.ghcb_change_page_state_via_pg(
            vn_to_pn(start_page, Tracked(page_perms.tracked_borrow(start_page as int))),
            npages,
            PageOps::Private,
            Tracked(page_perms),
            Tracked(cs),
        );
        let ghost prevcs = (*cs);
        proof {
            assert forall|i: int|
                start_page <= i < start_page + npages implies page_perms.contains_key(i)
                && page_perms[i]@.wf_range((i.to_addr(), PAGE_SIZE as nat)) by {
                assert(page_perms.contains_key(i));
                assert(old_page_perms.contains_key(i));
                assert(old_page_perms[i]@.wf_range((i.to_addr(), PAGE_SIZE as nat)));
            }
        }
        let ghost prev_page_perms = *page_perms;
        set_pages_enc_dec(start_page, npages as u64, true, Tracked(cs), Tracked(page_perms));
        proof {
            oldcs.lemma_update_prop(
                prevcs,
                (*cs),
                set![],
                set![],
                set![],
                set![spec_PT().lockid()],
            );
            assert(set![].union(set![spec_PT().lockid()]) =~~= set![spec_PT().lockid()]);
            assert forall|i|
                start_page <= i < start_page + npages implies 
                (#[trigger] page_perms.contains_key(i)
                && spec_perm_requires_pvalidate(
                page_perms[i],
                i.to_addr(),
                PAGE_SIZE as nat,
                true,
            )) by {
                assert(prev_page_perms.contains_key(i));
                assert(page_perms.contains_key(i));
                assert(prev_page_perms[i]@.snp().wf());
                assert(!prev_page_perms[i]@.snp().pte().spec_encrypted());
                assert(page_perms[i]@.snp_wf_range((i.to_addr(), PAGE_SIZE as nat)));
                assert(!page_perms[i]@.snp().rmp@.spec_validated());
                assert(page_perms[i]@.snp().deterministic_pte());
            }
        }
        pvalmem2(
            start_page.to_addr(),
            end_page.to_addr(),
            true,
            Tracked(page_perms),
            Tracked(&mut cs.snpcore),
        );
        proof {
            assert forall|i| start_page <= i < (start_page + npages) 
            implies 
            (#[trigger]page_perms.contains_key(i) && 
            mk_private_ensures_pageperm(
                old_page_perms[i]@,
                page_perms[i]@,
            )) by {
                let page_perm = page_perms[i]@;
                let prev_page_perm = old_page_perms[i]@;
                assert(old_page_perms.contains_key(i));
                assert(page_perms.contains_key(i));
                assert(prev_page_perms.contains_key(i));
                assert(page_perm.snp().is_vmpl0_private());
                assert(page_perm.snp().pte() === prev_page_perm.snp().pte().spec_set_encrypted(
                    true,
                ));
                assert(page_perm.snp() === prev_page_perm.snp().spec_set_pte(
                    page_perm.snp().pte,
                ).spec_set_rmp(page_perm.snp().rmp));
                assert(page_perm.snp().rmp === SwSnpMemAttr::spec_default().rmp);
            }
        }
        ret
    }
}

} // verus!
