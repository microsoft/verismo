use super::proto_s::SM_TERM_GHCB_RESP_INVALID;
use super::*;
use crate::debug::{VPrint, VPrintAtLevel};
use crate::global::*;
use crate::pgtable_e::va_to_pa;
use crate::vbox::*;

verus! {

#[verifier(external_body)]
proof fn trusted_ghcb_change_pages_state_via_pg(
    ppage: int,
    npages: nat,
    tracked page_perms: &mut Map<int, SnpPointsToRaw>,
    op: PageOps,
    tracked snpcore: &SnpCore,
)
    requires
        requires_pages_perms(*old(page_perms), ppage, npages),
    ensures
        ensure_pages_perm_change_state(*old(page_perms), *page_perms, ppage, npages, op),
{
}

pub fn ghcb_change_page_state_via_pg(
    ghcb_ptr: SnpPPtr<GhcbPage>,
    ppage: u64,
    npages: u64,
    op: PageOps,
    Tracked(page_perms): Tracked<&mut Map<int, SnpPointsToRaw>>,
    Tracked(ghcbpage_perm0): Tracked<&mut Map<int, SnpPointsTo<GhcbPage>>>,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
)
    requires
        old(cs).inv(),
        old(ghcbpage_perm0).contains_key(0),
        old(ghcbpage_perm0)[0]@.wf_shared(ghcb_ptr.id()),
        ghcb_ptr.is_constant(),
        spec_valid_page_state_change(ppage, npages as nat),
        requires_pages_perms(*old(page_perms), ppage as int, npages as nat),
        forall|i|
            ppage <= i < (ppage + npages) ==> old(page_perms).contains_key(i) && old(
                page_perms,
            )[i]@.wf_range((i.to_addr(), PAGE_SIZE as nat)),
    ensures
        ghcbpage_perm0.contains_key(0),
        ghcbpage_perm0[0]@.only_val_updated(old(ghcbpage_perm0)[0]@),
        ghcbpage_perm0[0]@.wf_shared(ghcb_ptr.id()),
        cs.inv(),
        cs.only_lock_reg_coremode_updated(*old(cs), set![], set![]),
        ensure_pages_perm_change_state(
            *old(page_perms),
            *page_perms,
            ppage as int,
            npages as nat,
            op,
        ),
        forall|i|
            ppage <= i < (ppage + npages) ==> page_perms.contains_key(i)
                && ensure_page_perm_change_state(
                old(page_perms)[i],
                #[trigger] page_perms[i],
                i as int,
                op,
            ),
{
    let mut offset = 0;
    let tracked mut ghcbpage_perm = ghcbpage_perm0.tracked_remove(0);
    let ghost old_page_perms = *page_perms;
    let ghost oldcs = *cs;
    while offset < npages
        invariant
            spec_valid_page_state_change(ppage, npages as nat),
            0 <= offset <= npages,
            ghcbpage_perm@.wf_shared(ghcb_ptr.id()),
            ghcb_ptr.is_constant(),
            cs.inv(),
            cs.only_lock_reg_coremode_updated(oldcs, set![], set![]),
            ensure_pages_perm_change_state(
                old_page_perms,
                *page_perms,
                ppage as int,
                offset as nat,
                op,
            ),
            forall|i| (ppage + offset) <= i < (ppage + npages) ==> page_perms.contains_key(i),
            forall|i|
                (ppage + offset) <= i < (ppage + npages) ==> old_page_perms[i] === page_perms[i],
            requires_pages_perms(old_page_perms, ppage as int, npages as nat),
    {
        let ghost prevcs = *cs;
        let n = if (npages - offset) < SNP_PAGE_STATE_CHANGE_MAX_ENTRY as u64 {
            (npages - offset) as u16
        } else {
            SNP_PAGE_STATE_CHANGE_MAX_ENTRY as u16
        };
        let tracked mut ghcbpage_perm0 = Map::tracked_empty();
        proof {
            ghcbpage_perm0.tracked_insert(0, ghcbpage_perm);
        }
        let ghost subdom = Set::new(|i| ppage + offset <= i < ppage + offset + n);
        assert forall|i| subdom.contains(i) implies page_perms.contains_key(i) by {
            assert(old_page_perms[i] === page_perms[i]);
            assert(ppage + offset <= i < ppage + npages);
        }
        assert(subdom.subset_of(page_perms.dom()));
        let ghost prev_page_perms = *page_perms;
        let tracked mut sub_page_perms = page_perms.tracked_remove_keys(subdom);
        let ghost removed_page_perms = *page_perms;
        assert forall|i|
            !subdom.contains(i) && prev_page_perms.contains_key(i) implies page_perms.contains_key(
            i,
        ) && page_perms[i] === prev_page_perms[i] by {}
        internal::ghcb_change_page_state_via_pg_internal(
            ghcb_ptr.clone(),
            ppage + offset as u64,
            n,
            op,
            Tracked(&mut sub_page_perms),
            Tracked(&mut ghcbpage_perm0),
            Tracked(cs),
        );
        offset = offset + n as u64;
        proof {
            let tracked sub_page_perms = sub_page_perms.tracked_remove_keys(subdom);
            page_perms.tracked_union_prefer_right(sub_page_perms);
            assert forall|i|
                !sub_page_perms.contains_key(i) && prev_page_perms.contains_key(
                    i,
                ) implies page_perms.contains_key(i) && page_perms[i] === prev_page_perms[i] by {
                assert(removed_page_perms.contains_key(i));
                assert(removed_page_perms[i] === prev_page_perms[i]);
                assert(removed_page_perms[i] === page_perms[i]);
            }
            assert forall|i|
                ppage <= i < (ppage + offset) implies #[trigger] page_perms.contains_key(i)
                && ensure_page_perm_change_state(
                old_page_perms[i],
                page_perms[i],
                i as int,
                op,
            ) by {
                if i < ppage + offset - n {
                    assert(prev_page_perms.contains_key(i));
                    assert(!subdom.contains(i));
                    assert(page_perms.contains_key(i));
                    assert(page_perms[i] === prev_page_perms[i]);
                } else {
                    assert(subdom.contains(i));
                    assert(sub_page_perms.contains_key(i));
                    assert(page_perms[i] === sub_page_perms[i]);
                }
            }
            assert forall|i| (ppage + offset) <= i < (ppage + npages) implies (
            page_perms.contains_key(i) && old_page_perms[i] === page_perms[i]) by {
                assert(!subdom.contains(i));
                assert(!sub_page_perms.contains_key(i));
                assert(page_perms[i] === prev_page_perms[i]);
                assert(prev_page_perms.contains_key(i));
            }
            ghcbpage_perm = ghcbpage_perm0.tracked_remove(0);
            oldcs.lemma_update_prop(prevcs, *cs, set![], set![], set![], set![]);
        }
    }
    proof {
        ghcbpage_perm0.tracked_insert(0, ghcbpage_perm);
    }
}

} // verus!
mod internal {
    use super::*;
    verus! {

pub fn ghcb_change_page_state_via_pg_internal(
    ghcb_ptr: SnpPPtr<GhcbPage>,
    ppage: u64,
    npages: u16,
    op: PageOps,
    Tracked(page_perms): Tracked<&mut Map<int, SnpPointsToRaw>>,
    Tracked(ghcbpage_perm0): Tracked<&mut Map<int, SnpPointsTo<GhcbPage>>>,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
)
    requires
        old(cs).inv(),
        old(ghcbpage_perm0).contains_key(0),
        old(ghcbpage_perm0)[0]@.wf_shared(ghcb_ptr.id()),
        ghcb_ptr.is_constant(),
        spec_valid_page_state_change(ppage, npages as nat),
        npages <= SNP_PAGE_STATE_CHANGE_MAX_ENTRY,
        requires_pages_perms(*old(page_perms), ppage as int, npages as nat),
        forall|i|
            ppage <= i < (ppage + npages) ==> old(page_perms).contains_key(i) && old(
                page_perms,
            )[i]@.wf_range((i.to_addr(), PAGE_SIZE as nat)),
    ensures
        ghcbpage_perm0.contains_key(0),
        ghcbpage_perm0[0]@.only_val_updated(old(ghcbpage_perm0)[0]@),
        ghcbpage_perm0[0]@.wf_shared(ghcb_ptr.id()),
        cs.inv(),
        cs.only_lock_reg_coremode_updated(*old(cs), set![], set![]),
        ensure_pages_perm_change_state(
            *old(page_perms),
            *page_perms,
            ppage as int,
            npages as nat,
            op,
        ),
{
    if npages == 0 {
        return ;
    }
    let tracked mut ghcbpage_perm = ghcbpage_perm0.tracked_remove(0);
    let scratch_ptr = ghcb_ptr.shared_buffer();
    let scratch_paddr = scratch_ptr.as_u64();
    let mut ghcb = VBox::<GhcbPage>::from_raw(ghcb_ptr.to_usize(), Tracked(ghcbpage_perm));
    ghcb.box_update(GhcbClear);
    let (ghcb_ptr, Tracked(mut ghcbpage_perm)) = ghcb.into_raw();
    let tracked (left, right) = ghcbpage_perm.tracked_into_raw().trusted_split(
        GhcbPage::spec_shared_buffer_offset(),
    );
    let tracked (scratch_perm, right) = right.trusted_split(spec_size::<SnpPageStateChange>());
    let mut scratch: VBox<SnpPageStateChange> = VBox::from_raw(
        scratch_ptr.to_usize(),
        Tracked(scratch_perm.trusted_into()),
    );
    // Clear the buffer
    scratch.box_update((FillPageStateChangeFn, ppage, npages, op));
    let (scratch_ptr, Tracked(scratch_perm)) = scratch.into_raw();
    let mut exit_code = SVM_EXIT_PAGE_STATE_CHANGE;
    let mut exit_info1 = 0;
    let mut exit_info2 = 0;
    let tracked mut ghcbpage_perm = left.trusted_join(scratch_perm.tracked_into_raw()).trusted_join(
        right,
    ).tracked_into();
    let (mut header, Tracked(mut ghcbpage_perm)) = scratch_ptr.header().copy_with::<GhcbPage>(
        Tracked(ghcbpage_perm),
    );
    let ghost oldcs = *cs;
    let ghost old_ghcbpage_perm = ghcbpage_perm;
    while header.cur_entry.le(&header.end_entry)
        invariant
            header.is_constant(),
            ghcbpage_perm@.wf_shared(ghcb_ptr.id()),
            ghcb_ptr.is_constant(),
            ghcbpage_perm@.only_val_updated(old_ghcbpage_perm@),
            cs.inv(),
            cs.only_lock_reg_coremode_updated(oldcs, set![], set![]),
            page_perms === old(page_perms),
    {
        let mut ghcb = VBox::<GhcbPage>::from_raw(ghcb_ptr.to_usize(), Tracked(ghcbpage_perm));
        ghcb.box_update((GhcbSetSwScratchFn, scratch_paddr));
        let (_, Tracked(mut tmp_ghcbpage_perm)) = ghcb.into_raw();
        let tracked mut ghcbpage_perm0 = Map::tracked_empty();
        let ghost prevcs = *cs;
        let mut exit_code = SVM_EXIT_PAGE_STATE_CHANGE;
        let mut exit_info1 = 0;
        let mut exit_info2 = 0;
        proof {
            ghcbpage_perm0.tracked_insert(0, tmp_ghcbpage_perm);
        }
        let resp = ghcb_page_proto(
            ghcb_ptr.clone(),
            &mut exit_code,
            &mut exit_info1,
            &mut exit_info2,
            Tracked(&mut ghcbpage_perm0),
            Tracked(cs),
        );
        proof {
            oldcs.lemma_update_prop(prevcs, *cs, set![], set![], set![], set![]);
            assert(cs.only_lock_reg_coremode_updated(oldcs, set![], set![]));
        }
        match resp {
            SvmStatus::Ok => {},
            _ => {
                proof {
                    reveal_strlit("Bad change page state");
                }
                new_strlit("Bad change page state").err(Tracked(cs));
                vc_terminate(SM_TERM_GHCB_RESP_INVALID, Tracked(&mut cs.snpcore));
            },
        }
        let scratch_ptr: SnpPPtr<SnpPageStateChange> = ghcb_ptr.shared_buffer().to();
        let (tmpheader, Tracked(mut tmp_ghcb_perm)) = scratch_ptr.header().copy_with::<GhcbPage>(
            Tracked(ghcbpage_perm0.tracked_remove(0)),
        );
        header = tmpheader;
        //header.leak_debug();
        proof {
            // TODO: Add page_perm updates
            ghcbpage_perm = tmp_ghcb_perm;
        }
    }
    proof {
        trusted_ghcb_change_pages_state_via_pg(
            ppage as int,
            npages as nat,
            page_perms,
            op,
            &cs.snpcore,
        );
        ghcbpage_perm0.tracked_insert(0, ghcbpage_perm);
    }
}

} // verus!
}

verus! {

pub const SNP_PAGE_STATE_CHANGE_MAX_ENTRY: usize = 253;

} // verus!
#[vbit_struct(SnpPageStateChangeEntry, u64)]
pub struct SpecSnpPageStateChangeEntry {
    #[vbits(0, 11)]
    pub cur_page: u64,
    #[vbits(12, 51)]
    pub gpn: u64,
    #[vbits(52, 55)]
    pub operation: u64,
    #[vbits(56, 56)]
    pub psize: u64,
}

verus! {

impl SpecSnpPageStateChangeEntry {
    pub open spec fn req_entry(gpn: u64, opval: u64, psize: u64) -> SpecSnpPageStateChangeEntry {
        SpecSnpPageStateChangeEntry::empty().spec_set_gpn(gpn).spec_set_operation(
            opval,
        ).spec_set_psize(psize)
    }
}

} // verus!
verismo_simple! {
#[repr(C, align(1))]
#[derive(Copy, VClone, VPrint, SpecGetter, SpecSetter)]
pub struct SnpPageStateChangeHeader {
    pub cur_entry: u16,
    pub end_entry: u16,
    pub reserved: u32,
}

#[repr(C, align(1))]
#[derive(SpecGetter, SpecSetter)]
pub struct SnpPageStateChange {
    #[def_offset]
    pub header: SnpPageStateChangeHeader,
    pub entries: [u64; SNP_PAGE_STATE_CHANGE_MAX_ENTRY],
}
}

verus! {

use crate::vbox::MutFnTrait;

pub struct FillPageStateChangeFn;

pub type FillPageStateChange = (FillPageStateChangeFn, u64, u16, PageOps);

impl<'a> MutFnTrait<'a, FillPageStateChange, bool> for SnpPageStateChange {
    open spec fn spec_update_requires(&self, params: FillPageStateChange) -> bool {
        let (_, ppage, npages, op) = params;
        &&& self.is_constant()
        &&& spec_valid_page_state_change(ppage, npages as nat)
        &&& npages <= SNP_PAGE_STATE_CHANGE_MAX_ENTRY
        &&& npages > 0
    }

    open spec fn spec_update(&self, prev: &Self, params: FillPageStateChange, ret: bool) -> bool {
        let (_, ppage, npages, op) = params;
        let opval = op.as_int() as u64;
        &&& self.is_constant()
        &&& forall|k: int|
            0 <= k < npages ==> SnpPageStateChangeEntry::spec_new(self.entries@[k].vspec_cast_to())@
                === SpecSnpPageStateChangeEntry::req_entry((ppage + k) as u64, opval, 0)
    }

    fn box_update(&'a mut self, params: FillPageStateChange) -> (ret: bool) {
        let (_, ppage, npages, op) = params;
        self.header.cur_entry = 0u64.into();
        self.header.end_entry = (npages - 1).into();
        let mut i: u16 = 0;
        let opval = op.as_u64();
        let ghost prev = *self;
        while i < npages
            invariant
                0 <= i <= npages,
                self.header === prev.header,
                self.is_constant(),
                spec_valid_page_state_change(ppage, npages as nat),
                opval == op.as_int(),
                npages <= SNP_PAGE_STATE_CHANGE_MAX_ENTRY,
                forall|k: int|
                    0 <= k < i ==> SnpPageStateChangeEntry::spec_new(
                        self.entries@[k].vspec_cast_to(),
                    )@ === SpecSnpPageStateChangeEntry::req_entry((ppage + k) as u64, opval, 0),
        {
            let gpn = ppage + i as u64;
            let entry = SnpPageStateChangeEntry::empty().set_gpn(gpn).set_operation(
                opval,
            ).set_psize(0);
            self.entries.update((i as usize), entry.value.into());
            i = i + 1;
        }
        true
    }
}

} // verus!
