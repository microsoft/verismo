use super::*;
use crate::arch::rmp::*;
use crate::registers::SnpCore;
verus! {

pub open spec fn spec_reset_perm_at(
    perm: SnpPointsToRaw,
    old_perm: SnpPointsToRaw,
    vmpl: nat,
) -> bool {
    let vmpl = VMPL::from_int(vmpl as int);
    let rmp = perm@.snp().rmp@;
    let old_rmp = old_perm@.snp().rmp@;
    &&& rmp === old_rmp.spec_set_perms(rmp.perms).spec_set_vmsa(false)
    &&& rmp.perms[vmpl] =~~= PagePerm::empty()
    &&& perm@.bytes() =~~= old_perm@.bytes()
    &&& perm@.range() === old_perm@.range()
    &&& perm@.wf()
}

pub open spec fn spec_reset_perm(perm: SnpPointsToRaw, old_perm: SnpPointsToRaw) -> bool {
    let rmp = perm@.snp().rmp@;
    let old_rmp = old_perm@.snp().rmp@;
    &&& rmp === old_rmp.spec_set_perms(rmp.perms)
    &&& rmp.perms =~~= rmp_perm_init()
    &&& perm@.bytes() === old_perm@.bytes()
    &&& perm@.range() === old_perm@.range()
    &&& perm@.wf()
}

pub fn rmp_reset_vmpl_perm(
    page: usize,
    Tracked(snpcore): Tracked<&SnpCore>,
    Tracked(perm): Tracked<&mut SnpPointsToRaw>,
)
    requires
        old(perm)@.wf_range(((page as int).to_addr(), PAGE_SIZE as nat)),
        old(perm)@.snp().rmp@.spec_validated(),
        snpcore.inv(),
        page.spec_valid_pn_with(1),
    ensures
        perm@.wf_range(((page as int).to_addr(), PAGE_SIZE as nat)),
        spec_reset_perm(*perm, *old(perm)),
{
    let mut vmpl = 1;
    let ghost old_perm = *perm;
    while vmpl < 4
        invariant
            1 <= vmpl <= 4,
            perm@.wf_range(((page as int).to_addr(), PAGE_SIZE as nat)),
            perm@.bytes() === old_perm@.bytes(),
            perm@.range() === old_perm@.range(),
            snpcore.inv(),
            forall|i| 0 < i < vmpl ==> #[trigger] spec_reset_perm_at(*perm, old_perm, i),
            page.spec_valid_pn_with(1),
    {
        let rmp_attr = RmpAttr::empty().set_vmpl(vmpl as u64).set_perms(0);
        rmpadjust(
            page.to_addr() as u64,
            RMP_4K,
            rmp_attr,
            Tracked(snpcore),
            Tracked(None),
            Tracked(perm),
        );
        assert(rmp_attr@.perms() =~~= PagePerm::empty());
        assert(rmp_attr@.vmpl() == VMPL::from_int(vmpl as int));
        assert forall|i: int| 1 <= i < vmpl implies #[trigger] spec_reset_perm_at(
            *perm,
            old_perm,
            i as nat,
        ) by {
            let i = VMPL::from_int(i);
            assert(perm@.snp().rmp@.perms.contains_key(i));
            assert(perm@.snp().rmp@.perms[i] =~~= PagePerm::empty());
        }
    }
    assert(spec_reset_perm_at(*perm, old_perm, 1));
    assert(spec_reset_perm_at(*perm, old_perm, 2));
    assert(spec_reset_perm_at(*perm, old_perm, 3));
    assert(spec_reset_perm_at(*perm, old_perm, 4));
}

} // verus!
