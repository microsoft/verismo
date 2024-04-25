use super::rmp_t::{pvalidate, rmpadjust};
use super::*;
use crate::addr_e::*;
use crate::arch::reg::RflagBit;
use crate::arch::rmp::*;
use crate::registers::{CoreIdPerm, SnpCore};
use crate::snp::ghcb::*;

verus! {

pub open spec fn spec_perm_requires_pvalidate(
    perm: SnpPointsToRaw,
    addr: int,
    size: nat,
    val: bool,
) -> bool {
    &&& perm@.snp().requires_pvalidate(
        addr,
        RMP_4K as int,
        if val {
            1
        } else {
            0
        },
    )
    &&& perm@.snp_wf_range((addr, size as nat))
}

pub open spec fn spec_perms_requires_pvalidate(
    page_perms: Map<int, SnpPointsToRaw>,
    start_page: int,
    end_page: int,
    val: bool,
) -> bool {
    forall|i|
        start_page <= i < end_page ==> #[trigger] page_perms.contains_key(i)
            && spec_perm_requires_pvalidate(page_perms[i], i.to_addr(), PAGE_SIZE as nat, val)
}

pub open spec fn spec_perm_ensures_pvalidate(
    perm: SnpPointsToRaw,
    old_perm: SnpPointsToRaw,
    start: int,
    size: nat,
    val: bool,
) -> bool {
    &&& perm@.snp().ensures_pvalidated(old_perm@.snp(), val)
    &&& perm@.snp_wf_range((start, size))
    &&& old_perm@.bytes().wf() ==> perm@.bytes().wf()
}

pub open spec fn spec_perms_ensures_pvalidate(
    page_perms: Map<int, SnpPointsToRaw>,
    old_perms: Map<int, SnpPointsToRaw>,
    start_page: int,
    end_page: int,
    val: bool,
) -> bool {
    &&& old_perms.dom() =~~= page_perms.dom()
    &&& forall|i|
        start_page <= i < end_page ==> #[trigger] page_perms.contains_key(i)
            && spec_perm_ensures_pvalidate(
            page_perms[i],
            old_perms[i],
            i.to_addr(),
            PAGE_SIZE as nat,
            val,
        )
}

pub fn pvalmem2(
    start: u64,
    end: u64,
    val: bool,
    Tracked(perms): Tracked<&mut Map<int, SnpPointsToRaw>>,
    Tracked(snpcore): Tracked<&mut SnpCore>,
)
    requires
        end as int % PAGE_SIZE!() == 0,
        start as int % PAGE_SIZE!() == 0,
        start < end,
        spec_perms_requires_pvalidate(
            *old(perms),
            (start as int).to_page(),
            (end as int).to_page(),
            val,
        ),
        old(snpcore).inv(),
        old(snpcore).coreid@.vmpl == 0,
    ensures
        spec_perms_ensures_pvalidate(
            *perms,
            *old(perms),
            (start as int).to_page(),
            (end as int).to_page(),
            val,
        ),
        snpcore.inv(),
        *old(snpcore) === *snpcore,
{
    let ghost old_perms = *perms;
    let ghost old_snpcore = *snpcore;
    let mut vaddr = start;
    while vaddr < end
        invariant
            vaddr.is_constant(),
            end.is_constant(),
            end as int % PAGE_SIZE!() == 0,
            vaddr as int % PAGE_SIZE!() == 0,
            (start as int) <= (vaddr as int) <= (end as int),
            forall|i|
                (start as int).to_page() <= i < (end as int).to_page()
                    ==> #[trigger] old_perms.contains_key(i),
            forall|i|
                (vaddr as int).to_page() <= i < (end as int).to_page()
                    ==> #[trigger] perms.contains_key(i) && old_perms.contains_key(i) && perms[i]
                    === old_perms[i],
            spec_perms_requires_pvalidate(
                old_perms,
                (start as int).to_page(),
                (end as int).to_page(),
                val,
            ),
            spec_perms_requires_pvalidate(
                *perms,
                (vaddr as int).to_page(),
                (end as int).to_page(),
                val,
            ),
            spec_perms_ensures_pvalidate(
                *perms,
                old_perms,
                (start as int).to_page(),
                (vaddr as int).to_page(),
                val,
            ),
            snpcore.inv(),
            snpcore.coreid@.vmpl == 0,
            old_snpcore === *snpcore,
    {
        let ghost pn = (vaddr as int).to_page();
        proof {
            assert(perms.contains_key(pn));
        }
        let tracked current_perm = perms.tracked_remove(pn);
        let next_vaddr = vaddr + PAGE_SIZE as u64;
        let Tracked(current_perm) = pvalmem(
            vaddr,
            next_vaddr,
            val,
            Tracked(current_perm),
            Tracked(snpcore),
        );
        assert((vaddr as int).to_page() + 1 == (next_vaddr as int).to_page());
        vaddr = next_vaddr;
        proof {
            perms.tracked_insert(pn, current_perm);
            assert(perms.contains_key(pn));
            assert forall|i|
                (vaddr as int).to_page() <= i < (
                end as int).to_page() implies #[trigger] perms.contains_key(i)
                && old_perms.contains_key(i) && perms[i] === old_perms[i] by {
                assert(old_perms.contains_key(i));
                assert(perms.contains_key(i));
            }
            assert forall|i|
                (start as int).to_page() <= i < (
                vaddr as int).to_page() implies #[trigger] perms.contains_key(i)
                && spec_perm_ensures_pvalidate(
                perms[i],
                old_perms[i],
                i.to_addr(),
                PAGE_SIZE as nat,
                val,
            ) by {
                assert(old_perms.contains_key(i));
                assert(perms.contains_key(i));
            }
            assert forall|i|
                (vaddr as int).to_page() <= i < (
                end as int).to_page() implies #[trigger] perms.contains_key(i)
                && spec_perm_requires_pvalidate(perms[i], i.to_addr(), PAGE_SIZE as nat, val) by {
                assert(old_perms.contains_key(i));
                assert(perms.contains_key(i));
            }
            assert(spec_perms_ensures_pvalidate(
                *perms,
                old_perms,
                (start as int).to_page(),
                (vaddr as int).to_page(),
                val,
            ));
        }
    }
}

pub fn pvalmem(
    start: u64,
    end: u64,
    val: bool,
    Tracked(perm): Tracked<SnpPointsToRaw>,
    Tracked(snpcore): Tracked<&mut SnpCore>,
) -> (ret: Tracked<SnpPointsToRaw>)
    requires
        spec_perm_requires_pvalidate(perm, start as int, (end - start) as nat, val),
        end as int % PAGE_SIZE!() == 0,
        start as int % PAGE_SIZE!() == 0,
        start < end,
        old(snpcore).inv(),
        old(snpcore).coreid@.vmpl == 0,
    ensures
        ret@@.snp_wf_range((start as int, (end - start) as nat)),
        ret@@.snp().ensures_pvalidated(perm@.snp(), val),
        spec_perm_ensures_pvalidate(ret@, perm, start as int, (end - start) as nat, val),
        snpcore.inv(),
        *old(snpcore) === *snpcore,
{
    let tracked mut perm = perm;
    let ghost old_perm = perm;
    let ghost mut expected_snp = perm@.snp();
    proof {
        expected_snp.rmp.val.validated = val;
        // = RmpEntry::new(old_perm@.snp().rmp@.spec_set_validated(val));
    }
    let tracked mut retp = SnpPointsToRaw::tracked_empty(start as int, expected_snp);
    let ghost gvalidate: int = if val {
        1
    } else {
        0
    };
    let ghost oldsnpcore = *snpcore;
    let mut vaddr = start;
    while vaddr < end
        invariant
            vaddr.is_constant(),
            end.is_constant(),
            end as int % PAGE_SIZE!() == 0,
            vaddr as int % PAGE_SIZE!() == 0,
            (start as int) <= (vaddr as int) <= (end as int),
            gvalidate == if val {
                1int
            } else {
                0int
            },
            perm@.snp() === old_perm@.snp(),
            perm@.snp().requires_pvalidate(vaddr as int, RMP_4K as int, gvalidate),
            perm@.snp_wf_range((vaddr as int, (end - vaddr) as nat)),
            retp@.snp().ensures_pvalidated(perm@.snp(), val),
            retp@.snp_wf_range((start as int, (vaddr - start) as nat)),
            snpcore.inv(),
            old_perm@.bytes().wf() ==> perm@.bytes().wf(),
            old_perm@.bytes().wf() ==> retp@.bytes().wf(),
            snpcore.coreid@.vmpl == 0,
            oldsnpcore === *snpcore,
    {
        let ghost prev_perm = perm;
        let tracked (mut current_perm, next_perm) = perm.trusted_split(PAGE_SIZE as nat);
        let ghost old_current_perm = current_perm;
        let mut rflags: u64 = 0;
        let validate = if val {
            1
        } else {
            0
        };
        let rc = pvalidate(
            vaddr,
            RMP_4K,
            validate,
            &mut rflags,
            Tracked(snpcore),
            Tracked(&mut current_perm),
        );
        if bit_check(rflags, RflagBit::CF.as_u64()) || rc != 0 {
            // failed validation ==> possible attack
            vc_terminate(SM_TERM_INVALID_PARAM, Tracked(snpcore));
        }
        vaddr = vaddr + PAGE_SIZE as u64;
        proof {
            assert(retp@.snp().ensures_pvalidated(perm@.snp(), val));
            assert(current_perm@.snp().ensures_pvalidated(perm@.snp(), val));
            assert(current_perm@.size() == PAGE_SIZE);
            // rmp status is valid
            retp@.snp().rmp.proof_eq(current_perm@.snp().rmp);
            assert(retp@.snp() === current_perm@.snp());
            HwSnpMemAttr::reveal_use_rflags();
            assert(retp@.snp.wf());
            if old_perm@.bytes().wf() {
                assert(retp@.bytes().wf());
                assert(old_current_perm@.bytes() =~~= prev_perm@.bytes().take(PAGE_SIZE as int));
                assert(old_current_perm@.bytes().wf());
                assert(current_perm@.bytes().wf());
                assert((retp@.bytes() + current_perm@.bytes()).wf());
            }
            retp = retp.tracked_join(current_perm);
            assert(old_perm@.bytes().wf() ==> retp@.bytes().wf());
            perm = next_perm;
            assert(retp@.range() === (start as int, (vaddr - start) as nat));
        }
    }
    Tracked(retp)
}

pub open spec fn spec_rmpadjmem_requires_at(
    page_perm: SnpPointsToRaw,
    i: int,
    attr: RmpAttrSpec,
) -> bool {
    &&& page_perm@.snp().requires_rmpadjust_mem((i as int).to_addr(), RMP_4K as int, attr, None)
    &&& page_perm@.wf_range((i.to_addr(), PAGE_SIZE as nat))
    &&& page_perm@.bytes().is_constant_to(attr.spec_vmpl() as nat)
}

pub open spec fn spec_rmpadjmem_requires(
    page_perms: Map<int, SnpPointsToRaw>,
    start_page: int,
    npages: nat,
    attr: RmpAttrSpec,
) -> bool {
    &&& start_page.spec_valid_pn_with(npages)
    &&& forall|i|
        start_page <= i < (start_page + npages) ==> #[trigger] page_perms.contains_key(i)
            && spec_rmpadjmem_requires_at(page_perms[i], i, attr)
}

pub open spec fn spec_ensures_rmpadjust(
    prev_perm: SnpPointsToRaw,
    perm: SnpPointsToRaw,
    page: int,
    attr: RmpAttrSpec,
) -> bool {
    &&& perm@.snp().ensures_rmpadjust(prev_perm@.snp(), attr)
    &&& perm@.wf_range((page.to_addr(), PAGE_SIZE as nat))
    &&& perm@.range() === prev_perm@.range()
    &&& perm@.bytes() =~~= prev_perm@.bytes()
}

pub open spec fn spec_ensures_rmpadjmem(
    prev_perms: Map<int, SnpPointsToRaw>,
    page_perms: Map<int, SnpPointsToRaw>,
    start_page: int,
    npages: nat,
    attr: RmpAttrSpec,
) -> bool {
    &&& forall|i|
        start_page <= i < (start_page + npages) ==> #[trigger] page_perms.contains_key(i)
            && spec_ensures_rmpadjust(prev_perms[i], page_perms[i], i, attr)
    &&& page_perms.dom() =~~= prev_perms.dom()
}

pub fn rmpadjmem(
    start_page: usize,
    npages: usize,
    attr: RmpAttr,
    Tracked(snpcore): Tracked<&mut SnpCore>,
    Tracked(perms): Tracked<&mut Map<int, SnpPointsToRaw>>,
)
    requires
        !attr@.is_vmsa(),
        spec_rmpadjmem_requires(*old(perms), start_page as int, npages as nat, attr@),
        old(snpcore).inv(),
        old(snpcore).coreid@.vmpl == 0,
    ensures
        spec_ensures_rmpadjmem(*old(perms), *perms, start_page as int, npages as nat, attr@),
        *old(snpcore) === *snpcore,
{
    let ghost old_perms = *perms;
    let ghost old_snpcore = *snpcore;
    let tracked mut page_perms = perms.tracked_remove_keys(perms.dom());
    proof {
        assert(page_perms =~~= old_perms);
    }
    let mut i = 0;
    while i < npages
        invariant
            0 <= i <= npages,
            forall|k|
                start_page as int + i <= k < start_page as int + npages ==> old_perms[k]
                    === page_perms[k],
            spec_rmpadjmem_requires(old_perms, start_page as int, npages as nat, attr@),
            spec_rmpadjmem_requires(page_perms, start_page as int + i, (npages - i) as nat, attr@),
            spec_ensures_rmpadjmem(old_perms, page_perms, start_page as int, i as nat, attr@),
            !attr@.is_vmsa(),
            snpcore.inv(),
            snpcore.coreid@.vmpl == 0,
            *snpcore === old_snpcore,
    {
        let page = start_page + i;
        let vaddr = page.to_addr() as u64;
        proof {
            assert(page_perms.contains_key(page as int));
        }
        let tracked mut current_perm = page_perms.tracked_remove(page as int);
        let ghost prev_perm = current_perm;
        let rc = rmpadjust(
            vaddr,
            RMP_4K,
            attr,
            Tracked(snpcore),
            Tracked(None),
            Tracked(&mut current_perm),
        );
        if rc != 0 {
            // failed validation ==> possible attack
            vc_terminate(SM_TERM_INVALID_PARAM, Tracked(snpcore));
        }
        i = i + 1;
        proof {
            // rmp status is valid
            assert(current_perm@.snp().ensures_rmpadjust(prev_perm@.snp(), attr@));
            assert(spec_ensures_rmpadjust(prev_perm, current_perm, page as int, attr@));
            assert(old_perms[page as int] === prev_perm);
            page_perms.tracked_insert(page as int, current_perm);
            assert(page_perms.contains_key(page as int));
            assert forall|k|
                start_page as int + i <= k < start_page as int + npages implies old_perms[k]
                === page_perms[k] by {
                assert(old_perms.contains_key(k));
                assert(page_perms.contains_key(k));
            }
            assert forall|k| start_page as int + i <= k < start_page as int + npages implies (
            #[trigger] page_perms.contains_key(k)) && spec_rmpadjmem_requires_at(
                page_perms[k],
                k,
                attr@,
            ) by {
                assert(old_perms.contains_key(k));
                assert(page_perms.contains_key(k));
                assert(page_perms[k] === old_perms[k]);
                assert(spec_rmpadjmem_requires_at(old_perms[k], k, attr@));
                assert(spec_rmpadjmem_requires_at(page_perms[k], k, attr@));
            }
            assert forall|k|
                start_page <= k < (start_page + i) implies #[trigger] page_perms.contains_key(k)
                && spec_ensures_rmpadjust(old_perms[k], page_perms[k], k, attr@) by {
                assert(page_perms.contains_key(k));
                assert(old_perms.contains_key(k));
            }
        }
    }
    proof {
        perms.tracked_union_prefer_right(page_perms);
    }
}

pub fn rmpadjust2(
    vaddr: u64,
    psize: u64,
    attr: RmpAttr,
    Tracked(mycore): Tracked<&SnpCore>,
    Tracked(newcore): Tracked<Option<CoreIdPerm>>,
    Tracked(perm): Tracked<&mut SnpPointsToRaw>,
) -> (ret: u64)
    requires
        old(perm)@.snp().requires_rmpadjust(vaddr as int, psize as int, attr@, newcore, old(perm)@),
        old(perm)@.wf_range((vaddr as int, PAGE_SIZE as nat)),
        old(perm)@.bytes().is_constant_to(attr.spec_vmpl() as nat),
        mycore.coreid@.vmpl == 0,
        attr.spec_vmpl() > mycore.coreid@.vmpl,
    ensures
        old(perm)@.snp.rmpadjust_ret(perm@.snp, ret, vaddr as int, psize as int, attr@),
        old(perm)@.range() === perm@.range(),
        old(perm)@.snp_bytes === perm@.snp_bytes,
        (ret == 0 && old(perm)@.wf()) ==> perm@.wf(),
{
    rmpadjust(vaddr, psize, attr, Tracked(mycore), Tracked(newcore), Tracked(perm))
}

} // verus!
