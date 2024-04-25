use alloc::vec::Vec;

use super::*;
use crate::allocator::VeriSMoAllocator;
use crate::arch::rmp::*;
use crate::boot::params::*;
use crate::debug::{VPrint, VPrintAtLevel};
use crate::pgtable_e::check_is_encrypted;
use crate::snp::mem::{spec_is_shared_page_perms, spec_is_vmprivate_const_perms};

verus! {

pub open spec fn spec_is_default_pages_const_to_vmpl(
    page_perms: Map<int, SnpPointsToRaw>,
    start_page: int,
    npages: nat,
    vmpl: nat,
) -> bool {
    forall|i|
        start_page <= i < (start_page + npages) ==> #[trigger] page_perms.contains_key(i)
            && page_perms[i]@.wf_default((i.to_addr(), PAGE_SIZE as nat))
            && page_perms[i]@.bytes().is_constant_to(vmpl)
}

pub const RICHOS_VMPL: u8 = 1;

pub const VERISMO_RSVD_MEM: usize = 0x100000;

} // verus!
#[vbit_struct(OSMemPerm, u8)]
pub struct OSMemPermSpec {
    #[vbits(0, 0)]
    pub read: u8,
    #[vbits(1, 1)]
    pub write: u8,
    #[vbits(2, 2)]
    pub user_exe: u8,
    #[vbits(3, 3)]
    pub kern_exe: u8,
    // #[vbits(4, 4)]
    // pub sss: u8,
}

verus! {

impl OSMemPermSpec {
    pub open spec fn is_super_of(&self, other: Self) -> bool {
        &&& self.spec_read() <= other.spec_read()
        &&& self.spec_write() <= other.spec_write()
        &&& self.spec_user_exe() <= other.spec_user_exe()
        &&& self.spec_kern_exe() <= other.spec_kern_exe()
    }
}

} // verus!
verus! {

impl OSMemPermSpec {
    pub closed spec fn ram() -> Self {
        OSMemPermSpec::empty().spec_set_user_exe(1).spec_set_read(1).spec_set_write(
            1,
        ).spec_set_kern_exe(1)
    }

    pub closed spec fn readwrite() -> Self {
        Self::empty().spec_set_read(1).spec_set_write(1)
    }

    pub closed spec fn readonly() -> Self {
        Self::empty().spec_set_read(1)
    }

    pub closed spec fn locked_kern() -> Self {
        Self::empty().spec_set_kern_exe(1).spec_set_read(1).spec_set_write(0).spec_set_user_exe(0)
    }

    pub closed spec fn user_exeonly() -> Self {
        Self::empty().spec_set_user_exe(1)
    }
}

} // verus!
verus! {

impl OSMemPerm {
    pub open spec fn to_page_perm(&self) -> PagePerm {
        PagePerm::from_int(self.value as int)
    }

    #[verifier(external_body)]
    pub fn is_super_of(&self, other: &Self) -> (ret: bool)
        ensures
            ret == self@.is_super_of(other@),
    {
        (self.value & other.value) == other.value
    }

    pub const fn ram() -> (ret: Self)
        ensures
            ret@ === OSMemPermSpec::ram(),
    {
        Self::empty().set_read(1).set_write(1).set_user_exe(1).set_kern_exe(1)
    }

    pub const fn readonly() -> (ret: Self)
        ensures
            ret@ === OSMemPermSpec::readonly(),
    {
        Self::empty().set_read(1)
    }

    pub const fn locked_kern() -> (ret: Self)
        ensures
            ret@ === OSMemPermSpec::locked_kern(),
    {
        Self::empty().set_kern_exe(1).set_read(1).set_write(0).set_user_exe(0)
    }

    pub const fn user_exeonly() -> (ret: Self)
        ensures
            ret@ === OSMemPermSpec::user_exeonly(),
    {
        Self::empty().set_user_exe(1)
    }
}

} // verus!
verismo_simple! {
#[derive(VPrint)]
pub struct OSMemEntry {
    pub start_page: usize,
    pub npages: usize,
    pub osperm: u8,
    pub page_perms: Tracked<Map<int, SnpPointsToRaw>>,
}
}

pub type OSMem = Vec<OSMemEntry>;

verus! {

pub open spec fn os_mem_valid_snp(osperm: OSMemPerm, snp: SwSnpMemAttr) -> bool {
    let pte = snp.pte();
    let rmp = snp.rmp@;
    let rmp_perm = rmp.perms[VMPL::from_int(RICHOS_VMPL as int)];
    if rmp.spec_validated() {
        &&& rmp_perm =~~= osperm.to_page_perm()
        &&& snp.wf()
        &&& pte.spec_encrypted()
    } else {
        &&& snp === SwSnpMemAttr::shared()
        &&& osperm@ === OSMemPermSpec::ram()
        &&& !pte.spec_encrypted()
    }
}

pub open spec fn spec_contains_page_perm(
    page_perms: Map<int, SnpPointsToRaw>,
    i: int,
    osperm: OSMemPerm,
) -> bool {
    let page_perm = page_perms[i]@;
    &&& page_perms.contains_key(i)
    &&& page_perm.wf_not_null((i.to_addr(), PAGE_SIZE as nat))
    &&& os_mem_valid_snp(osperm, page_perm.snp())
    &&& page_perm.bytes().is_constant_to(RICHOS_VMPL as nat)
}

pub open spec fn spec_contains_page_perms(
    page_perms: Map<int, SnpPointsToRaw>,
    start_page: int,
    npages: nat,
    osperm: OSMemPerm,
) -> bool {
    &&& forall|i| #[trigger]
        page_perms.contains_key(i) ==> spec_contains_page_perm(page_perms, i, osperm)
    &&& page_perms.dom() =~~= Set::new(|i: int| start_page <= i < start_page + npages)
}

} // verus!
verismo_simple! {
impl OSMemEntry {
    pub open spec fn osmem_invfn() -> spec_fn(Vec<OSMemEntry>) -> bool {
        |v: Vec<OSMemEntry>| osmem_wf(v@)
    }

    pub open spec fn spec_osperm(&self) -> OSMemPerm {
        OSMemPerm::spec_new(self.osperm as u8)
    }

    pub fn osperm(&self) -> (ret: OSMemPerm)
    requires
        self.is_constant()
    ensures
        ret === self.spec_osperm()
    {
        OSMemPerm::new(self.osperm.into())
    }

    pub fn end(&self) -> (ret: usize_t)
    requires
        self.wf()
    ensures
        ret.spec_valid_pn_with(0),
        ret == self.spec_end(),
    {
        self.start_page.add(self.npages).into()
    }

    pub fn npages(&self) -> (ret: usize_t)
    requires
        self.wf()
    ensures
        ret == self.npages@.val,
    {
        self.npages.into()
    }

    pub open spec fn open_wf(&self) -> bool {
        &&& self.is_constant()
        &&& self.start_page.spec_valid_pn_with(self.npages as nat)
        &&& spec_contains_page_perms(
            self.page_perms@,
            self.start_page as int,
            self.npages as nat,
            self.spec_osperm(),
        )
    }

    pub closed spec fn closed_wf(&self) -> bool {
        self.open_wf()
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.closed_wf()
        &&& self.is_constant()
    }

    pub proof fn proof_open_wf(&self)
    ensures
        self.wf() == self.open_wf(),
    {}

    pub proof fn proof_contains(&self, gpn: int)
    requires
        self.wf(),
        self.spec_start() <= gpn < self.spec_end(),
    ensures
        self.start_page.spec_valid_pn_with(self.npages as nat),
        spec_contains_page_perm(self.page_perms@, gpn, self.spec_osperm())
    {
        assert(self.page_perms@.contains_key(gpn));
    }

    pub open spec fn spec_start(&self) -> int {
        self.start_page as int
    }

    pub open spec fn spec_end(&self) -> int {
        (self.start_page + self.npages) as int
    }
}
}
verus! {

pub open spec fn osmem_wf(osmem: Seq<OSMemEntry>) -> bool {
    &&& osmem.is_constant()
    &&& forall|i| 0 <= i < osmem.len() ==> osmem[i].wf()
}

pub fn osmem_adjust(
    ghcb_h: GhcbHandle,
    entry: OSMemEntry,
    shared: bool,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
) -> (ret: (GhcbHandle, OSMemEntry))
    requires
        ghcb_h.ghcb_wf(),
        entry.wf(),
        old(cs).inv(),
    ensures
        cs.inv(),
        ret.0.ghcb_wf(),
        ret.1.wf(),
        ret.1.osperm == entry.osperm,
        ret.1.start_page == entry.start_page,
        ret.1.npages == entry.npages,
        cs.only_lock_reg_coremode_updated(*old(cs), set![], set![spec_PT_lockid()]),
{
    let mut entry = entry;
    let start_page: usize = entry.start_page.into();
    let npages: usize = entry.npages.into();
    if npages == 0 {
        return (ghcb_h, entry);
    }
    let ghost old_page_perms = entry.page_perms@;
    proof {
        assert(old_page_perms.dom() =~~= Set::new(
            |i| start_page as int <= i < start_page + npages,
        ));
    }
    let Tracked(mut page_perms) = entry.page_perms;
    let mut ghcb_h = ghcb_h;
    if !shared {
        assert forall|i|
            start_page <= i < (start_page + npages) implies #[trigger] page_perms.contains_key(i)
            && page_perms[i]@.wf_range((i.to_addr(), PAGE_SIZE as nat)) by {
            assert(page_perms.contains_key(i));
            assert(spec_contains_page_perm(page_perms, i, entry.spec_osperm()));
        }
        ghcb_h =
        ghcb_h.mk_private(start_page as u64, npages as u64, Tracked(cs), Tracked(&mut page_perms));
        // TODO: zero all pages;
        let start = start_page.to_addr();
        let size = npages.to_addr();
        proof {
            assert forall|i|
                (start as int).to_page() <= i < ((start
                    + size) as int).to_page() implies #[trigger] page_perms.contains_key(i)
                && page_perms[i]@.snp_wf_range((i.to_addr(), PAGE_SIZE as nat)) by {
                assert(old_page_perms.contains_key(i));
                assert(page_perms.contains_key(i));
            }
            assert(forall|i|
                ((start as int).to_page() <= i < ((start + size) as int).to_page()) ==> (
                #[trigger] page_perms.contains_key(i) && page_perms[i]@.snp_wf_range(
                    (i.to_addr(), PAGE_SIZE as nat),
                )));
        }
        mem_set_zeros2(start, size, Tracked(&mut page_perms));
        let attr = RmpAttr::empty().set_vmpl(RICHOS_VMPL as u64).set_perms(
            entry.osperm.into(),
        ).set_vmsa(0);
        proof {
            assert(start_page.spec_valid_pn_with(npages as nat));
            assert forall|i|
                start_page <= i < (start_page + npages) implies #[trigger] page_perms.contains_key(
                i,
            ) && spec_rmpadjmem_requires_at(page_perms[i], i, attr@) by {
                assert(old_page_perms.contains_key(i));
                assert(page_perms.contains_key(i));
                let perm = page_perms[i];
                assert(perm@.bytes().is_constant_to(attr.spec_vmpl() as nat));
                assert(perm@.snp().rmp@.spec_validated());
            }
            assert(spec_rmpadjmem_requires(page_perms, start_page as int, npages as nat, attr@));
        }
        rmpadjmem(start_page, npages, attr, Tracked(&mut cs.snpcore), Tracked(&mut page_perms));
    } else {
        ghcb_h =
        ghcb_h.mk_shared(start_page as u64, npages as u64, Tracked(cs), Tracked(&mut page_perms));
    }
    entry.page_perms = Tracked(page_perms);
    proof {
        assert(entry.start_page.spec_valid_pn_with(npages as nat));
        assert(entry.page_perms@.dom() =~~= old_page_perms.dom());
        assert(entry.page_perms@.dom() =~~= Set::new(
            |i| start_page as int <= i < start_page + npages,
        ));
        assert forall|i| #[trigger] page_perms.contains_key(i) implies spec_contains_page_perm(
            page_perms,
            i,
            entry.spec_osperm(),
        ) by {
            assert(page_perms.contains_key(i));
            let page_perm = page_perms[i];
            assert(os_mem_valid_snp(entry.spec_osperm(), page_perm@.snp()));
            assert(page_perm@.bytes().is_constant_to(RICHOS_VMPL as nat));
        }
        assert(spec_contains_page_perms(
            entry.page_perms@,
            start_page as int,
            npages as nat,
            entry.spec_osperm(),
        ));
        assert(entry.wf());
    }
    (ghcb_h, entry)
}

pub fn osmem_add(
    osmem: &mut Vec<OSMemEntry>,
    start_page: usize,
    npages: usize,
    osperm: OSMemPerm,
    shared: bool,
    Tracked(page_perms): Tracked<Map<int, SnpPointsToRaw>>,
    Tracked(snpcore): Tracked<&mut SnpCore>,
)
    requires
        osmem_wf(old(osmem)@),
        start_page.spec_valid_pn_with(npages as nat),
        !shared ==> spec_is_default_pages_const_to_vmpl(
            page_perms,
            start_page as int,
            npages as nat,
            RICHOS_VMPL as nat,
        ),
        old(snpcore).inv(),
        shared ==> osperm@ === OSMemPermSpec::ram(),
        shared ==> spec_is_shared_page_perms(page_perms, start_page as int, npages as nat),
    ensures
        osmem_wf(osmem@),
        osmem@ === old(osmem)@.push(osmem@.last()),
        osmem@.last().start_page.spec_eq(start_page),
        osmem@.last().npages.spec_eq(npages),
        osmem@.last().spec_osperm() === osperm,
        spec_contains_page_perms(
            osmem@.last().page_perms@,
            start_page as int,
            npages as nat,
            osperm,
        ),
        *snpcore === *old(snpcore),
{
    let tracked mut page_perms = page_perms;
    let tracked mut page_perms = page_perms.tracked_remove_keys(
        Set::new(|k| start_page <= k < (start_page + npages)),
    );
    let ghost old_page_perms = page_perms;
    if !shared {
        let attr = RmpAttr::empty().set_vmpl(RICHOS_VMPL as u64).set_perms(
            osperm.value as u64,
        ).set_vmsa(0);
        proof {
            assert(start_page.spec_valid_pn_with(npages as nat));
            assert forall|i| old_page_perms.contains_key(i) implies spec_rmpadjmem_requires_at(
                old_page_perms[i],
                i,
                attr@,
            ) by {
                assert(start_page <= i < start_page + npages);
                assert(spec_is_default_pages_const_to_vmpl(
                    old_page_perms,
                    start_page as int,
                    npages as nat,
                    RICHOS_VMPL as nat,
                ));
                assert(old_page_perms[i]@.wf_const_default((i.to_addr(), PAGE_SIZE as nat)));
            }
            assert(spec_rmpadjmem_requires((page_perms), start_page as int, npages as nat, attr@));
        }
        rmpadjmem(start_page, npages, attr, Tracked(snpcore), Tracked(&mut page_perms));
    }
    let entry = OSMemEntry {
        start_page: start_page.into(),
        npages: npages.into(),
        osperm: osperm.value.into(),
        page_perms: Tracked(page_perms),
    };
    osmem.push(entry);
    proof {
        assert forall|i| 0 <= i < osmem.len() implies osmem[i].wf() by {
            if i == osmem.len() - 1 {
                assert forall|k| page_perms.contains_key(k) implies spec_contains_page_perm(
                    page_perms,
                    k,
                    osperm,
                ) by {
                    assert(start_page <= k < (start_page + npages));
                    assert(old_page_perms.contains_key(k));
                    assert(page_perms.contains_key(k));
                    assert(page_perms[k]@.wf_not_null((k.to_addr(), PAGE_SIZE as nat)));
                    assert(os_mem_valid_snp(osperm, page_perms[k]@.snp()));
                    assert(page_perms[k]@.bytes() === old_page_perms[k]@.bytes());
                }
                assert(page_perms.dom() =~~= Set::new(|k| start_page <= k < (start_page + npages)));
                assert(spec_contains_page_perms(
                    page_perms,
                    start_page as int,
                    npages as nat,
                    osperm,
                ));
            }
        }
    }
}

pub fn osmem_entry_merge(left: OSMemEntry, right: OSMemEntry) -> (ret: OSMemEntry)
    requires
        left.wf(),
        right.wf(),
        right.spec_start() == left.spec_end(),
        left.osperm == right.osperm,
    ensures
        ret.wf(),
        ret.osperm == left.osperm,
        ret.spec_start() == left.spec_start(),
        ret.spec_end() == right.spec_end(),
{
    let mut ret = left;
    ret.npages = ret.npages.add(right.npages);
    let Tracked(mut page_perms) = ret.page_perms;
    let Tracked(right_page_perms) = right.page_perms;
    proof {
        page_perms.tracked_union_prefer_right(right_page_perms);
    }
    ret.page_perms = Tracked(page_perms);
    ret
}

pub fn osmem_entry_split(entry: OSMemEntry, start: usize, npages: usize) -> (ret: (
    OSMemEntry,
    OSMemEntry,
    OSMemEntry,
))
    requires
        entry.wf(),
        entry.spec_start() <= start,
        entry.spec_end() >= start + npages,
    ensures
        ret.0.wf(),
        ret.1.wf(),
        ret.2.wf(),
        ret.1.spec_start() == start,
        ret.1.spec_end() == start + npages,
        ret.0.spec_start() == entry.spec_start(),
        ret.0.spec_end() == ret.1.spec_start(),
        ret.2.spec_start() == ret.1.spec_end(),
        ret.2.spec_end() == entry.spec_end(),
        ret.0.osperm == entry.osperm,
        ret.1.osperm == entry.osperm,
        ret.2.osperm == entry.osperm,
{
    let Tracked(mut page_perms) = entry.page_perms;
    let tracked perms0 = page_perms.tracked_remove_keys(
        Set::new(|i| entry.spec_start() <= i < start),
    );
    let tracked perms1 = page_perms.tracked_remove_keys(Set::new(|i| start <= i < start + npages));
    let tracked perms2 = page_perms.tracked_remove_keys(
        Set::new(|i| start + npages <= i < entry.spec_end()),
    );
    let entry0 = OSMemEntry {
        start_page: entry.start_page,
        npages: (start - entry.start_page.reveal_value()).into(),
        osperm: entry.osperm,
        page_perms: Tracked(perms0),
    };
    let entry1 = OSMemEntry {
        start_page: start.into(),
        npages: npages.into(),
        osperm: entry.osperm,
        page_perms: Tracked(perms1),
    };
    let entry2 = OSMemEntry {
        start_page: (start + npages).into(),
        npages: (entry.npages.reveal_value() - npages + entry.start_page.reveal_value()
            - start).into(),
        osperm: entry.osperm,
        page_perms: Tracked(perms2),
    };
    (entry0, entry1, entry2)
}

pub fn osmem_find(osmem: &Vec<OSMemEntry>, vpage: usize) -> (ret: Option<usize>)
    requires
        osmem_wf(osmem@),
    ensures
        ret.is_Some() ==> (0 <= ret.unwrap() < osmem.len()
            && osmem[ret.unwrap() as int].spec_start() <= vpage
            < osmem[ret.unwrap() as int].spec_end()),
{
    let mut i = 0;
    while i < osmem.len()
        invariant
            0 <= i <= osmem.len(),
            osmem_wf(osmem@),
        ensures
            0 <= i <= osmem.len(),
            i < osmem.len() ==> osmem[i as int].spec_start() <= vpage < osmem[i as int].spec_end(),
    {
        let (start_page, npages): (usize, usize) = (
            osmem[i].start_page.into(),
            osmem[i].npages.into(),
        );
        proof {
            assert(osmem[i as int].wf());
        }
        let end_page = start_page + npages;
        if vpage >= start_page && vpage < end_page {
            break ;
        }
        i = i + 1;
    }
    if i < osmem.len() {
        Some(i)
    } else {
        None
    }
}

} // verus!
verus! {

pub open spec fn spec_ensure_check_osperm(
    ppage: int,
    osperm: OSMemPerm,
    entry: OSMemEntry,
) -> bool {
    let perm = osperm@;
    let is_full = perm.spec_read() > 0 && perm.spec_write() > 0 && perm.spec_kern_exe() > 0
        && perm.spec_user_exe() > 0;
    &&& entry.spec_start() <= ppage < entry.spec_end()
    &&& entry.spec_osperm()@.is_super_of(osperm@)
}

pub fn osmem_check(osmem: &Vec<OSMemEntry>, ppage: usize, osperm: OSMemPerm) -> (ret: bool)
    requires
        osmem_wf(osmem@),
    ensures
        ret ==> (osperm.value == 0 || exists|i|
            0 <= i < osmem.len() && spec_ensure_check_osperm(ppage as int, osperm, osmem[i])),
{
    match osmem_find(osmem, ppage) {
        Some(i) => { OSMemPerm::new(osmem[i].osperm.into()).is_super_of(&osperm) },
        _ => { false },
    }
}

pub fn osmem_check_and_get(osmem: &mut Vec<OSMemEntry>, ppage: usize, osperm: OSMemPerm) -> (ret:
    Option<(usize, OSMemEntry)>)
    requires
        osmem_wf(old(osmem)@),
    ensures
        ret.is_None() ==> old(osmem) === osmem,
        ret.is_Some() ==> osmem@ === old(osmem)@.remove(ret.get_Some_0().0 as int)
            && ret.get_Some_0().1 === old(osmem)@[ret.get_Some_0().0 as int] && 0
            <= ret.get_Some_0().0 < old(osmem)@.len(),
        ret.is_Some() ==> spec_ensure_check_osperm(ppage as int, osperm, ret.get_Some_0().1),
{
    match osmem_find(osmem, ppage) {
        Some(i) if OSMemPerm::new(osmem[i].osperm.into()).is_super_of(&osperm) => {
            Option::Some((i, osmem.remove(i)))
        },
        _ => { Option::None },
    }
}

pub fn osmem_check_and_get_page<T: IsConstant + SpecSize + WellFormed + VTypeCast<SecSeqByte>>(
    osmem: &mut Vec<OSMemEntry>,
    ppage: usize,
    osperm: OSMemPerm,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
) -> (ret: Option<(VBox<T>, OSMemPerm)>)
    requires
        spec_size::<T>() == PAGE_SIZE,
        osmem_wf(old(osmem)@),
        old(cs).inv(),
    ensures
        osmem_wf(osmem@),
        ret.is_Some() ==> ret.get_Some_0().0.wf(),
        ret.is_Some() ==> ret.get_Some_0().0.is_page(),
        ret.is_Some() ==> ret.get_Some_0().0.snp().encrypted(),
        ret.is_Some() ==> os_mem_valid_snp(ret.get_Some_0().1, ret.get_Some_0().0.snp()),
        cs.inv(),
        (*cs).only_lock_reg_updated((*old(cs)), set![], set![spec_PT().lockid()]),
{
    let ghost old_osmem = *osmem;
    if let Some(e) = osmem_check_and_get(osmem, ppage, osperm) {
        let (i, entry) = e;
        assert(old_osmem[i as int].wf());
        assert(entry.wf());
        // TODO: insert two entry skipping vmsa;
        let npages: usize = entry.npages.into();
        if npages > 1 {
            let (left, mid, right) = osmem_entry_split(entry, ppage, 1);
            let osperm = mid.osperm();
            let Tracked(mut page_perms) = mid.page_perms;
            assert(page_perms.contains_key(ppage as int));
            let tracked page_perm = page_perms.tracked_remove(ppage as int);
            let check = check_is_encrypted(ppage.to_addr(), Tracked(&page_perm), Tracked(cs));
            match check {
                Some(encrypted) if encrypted => {},
                _ => {
                    new_strlit("Do not use richos-shared/unmapped memory!").leak_debug();
                    return None;
                },
            }
            assert(page_perm@.wf_not_null(((ppage as int).to_addr(), PAGE_SIZE!() as nat)));
            if right.npages.reveal_value() > 0 {
                osmem.insert(i, right);
            }
            if left.npages.reveal_value() > 0 {
                osmem.insert(i, left);
            }
            Some((VBox::from_raw(ppage.to_addr(), Tracked(page_perm.tracked_into())), osperm))
        } else {
            None
        }
    } else {
        None
    }
}

} // verus!
use global::*;
verus! {

pub fn _osmem_add_ram_from_allocator(
    allocator: &mut VeriSMoAllocator,
    tmposmem: Vec::<OSMemEntry>,
    Tracked(snpcore): Tracked<&mut SnpCore>,
) -> (ret: Vec::<OSMemEntry>)
    requires
        old(snpcore).inv(),
        old(allocator)@.inv(),
        old(allocator).wf(),
        tmposmem.len() == 0,
    ensures
        osmem_wf(ret@),
        snpcore.inv(),
        *snpcore == *old(snpcore),
        allocator@.inv(),
        allocator.wf(),
{
    let ghost prevcore = *snpcore;
    let mut tmposmem = tmposmem;
    new_strlit("remove ranges\n").leak_debug();
    let mut range_mem = allocator.remove_one_range();
    while range_mem.is_some()
        invariant
            osmem_wf(tmposmem@),
            snpcore.inv(),
            *snpcore === prevcore,
            allocator@.inv(),
            allocator.wf(),
            range_mem.is_None() ==> (allocator@.len() == 0),
            range_mem.is_Some() ==> range_mem.get_Some_0().1@@.wf_const_default(
                (range_mem.get_Some_0().0.0 as int, range_mem.get_Some_0().0.1 as nat),
            ),
        ensures
            osmem_wf(tmposmem@),
            range_mem.is_None(),
            allocator@.inv(),
            allocator.wf(),
            allocator@.len() == 0,
            snpcore.inv(),
            *snpcore === prevcore,
    {
        let (range, perm) = range_mem.unwrap();
        let start_addr: usize = page_align_up(range.0);
        let start_page = start_addr.to_page();
        let end_page = (range.1 + range.0).to_page();
        let end_addr = end_page.to_addr();
        let Tracked(mut perm) = perm;
        assert(perm@.range().0 == range.0);
        assert(perm@.range().1 == range.1);
        if start_page < end_page {
            assert(perm@.range().end() >= end_addr);
            assert(perm@.size() >= PAGE_SIZE);
            assert(0 <= start_addr - range.0 < PAGE_SIZE);
            let npages = end_page - start_page;
            let ghost aligned_size = end_addr - start_addr;
            assert(aligned_size == npages * PAGE_SIZE!());
            assert(perm@.wf_const_default(perm@.range()));
            let tracked (left, mut aligned_perm) = perm.trusted_split(
                (start_addr - range.0) as nat,
            );
            let tracked (aligned_perm, right) = aligned_perm.trusted_split(aligned_size as nat);
            let tracked page_perms = aligned_perm.tracked_to_pages();
            assert(aligned_perm@.wf_const_default(aligned_perm@.range()));
            proof {
                assert forall|i|
                    start_page <= i < (start_page
                        + npages) implies #[trigger] page_perms.contains_key(i)
                    && page_perms[i]@.wf_const_default((i.to_addr(), PAGE_SIZE as nat)) by {
                    assert(page_perms.contains_key(i));
                    let offset = i.to_addr() - aligned_perm@.range().0;
                    assert(page_perms[i]@.bytes() =~~= aligned_perm@.bytes().subrange(
                        offset,
                        offset + PAGE_SIZE as int,
                    ));
                    assert(aligned_perm@.bytes().is_constant());
                    assert(page_perms[i]@.bytes().is_constant()) by {
                        let b = page_perms[i]@.bytes();
                        assert forall|k| 0 <= k < b.len() implies b[k].is_constant() by {
                            let sub = aligned_perm@.bytes().subrange(
                                offset,
                                offset + PAGE_SIZE as int,
                            );
                            assert(b[k] === sub[k]);
                            assert(sub[k] === aligned_perm@.bytes()[offset + k]);
                        }
                    }
                }
            }
            osmem_add(
                &mut tmposmem,
                start_page,
                npages,
                OSMemPerm::ram(),
                false,
                Tracked(page_perms),
                Tracked(snpcore),
            );
        }
        new_strlit("remove one\n").leak_debug();
        range_mem = allocator.remove_one_range();
    }
    tmposmem
}

pub fn add_osmem_to_e820(e820: VBox<E820Table>, e820_count: usize, osmem: &Vec<OSMemEntry>) -> (ret:
    VBox<E820Table>)
    requires
        e820@.is_constant(),
        e820.snp().is_vmpl0_private(),
        e820_count + osmem@.len() <= E820Table::spec_len(),
        osmem_wf(osmem@),
    ensures
        ret.only_val_updated(e820),
        ret@.is_constant(),
{
    let mut i = 0;
    let ghost old_e820 = e820;
    let mut e820 = e820;
    while i < osmem.len()
        invariant
            e820_count + osmem@.len() <= E820Table::spec_len(),
            e820.only_val_updated(old_e820),
            e820@.is_constant(),
            e820.snp().is_vmpl0_private(),
            osmem_wf(osmem@),
    {
        let entry = &osmem[i];
        assert(osmem[i as int].wf());
        (new_strlit("update: "), e820_count + i).leak_debug();
        e820.box_update(
            ArrayUpdate {
                index: (e820_count + i),
                val: E820Entry {
                    addr: entry.start_page.to_addr().into(),
                    size: entry.npages.to_addr().into(),
                    memty: E820_TYPE_RAM.into(),
                },
            },
        );
        i = i + 1;
    }
    e820
}

pub fn add_osmem_to_mut_e820(e820: &mut E820Table, e820_count: usize, osmem: &Vec<OSMemEntry>)
    requires
        old(e820)@.is_constant(),
        e820_count + osmem@.len() <= E820Table::spec_len(),
        osmem_wf(osmem@),
    ensures
        e820@.is_constant(),
{
    let mut i = 0;
    let ghost old_e820 = *e820;
    while i < osmem.len()
        invariant
            e820_count + osmem@.len() <= E820Table::spec_len(),
            e820@.is_constant(),
            osmem_wf(osmem@),
    {
        let entry = &osmem[i];
        assert(osmem[i as int].wf());
        (new_strlit("update: "), e820_count + i).leak_debug();
        e820.set(
            e820_count + i,
            E820Entry {
                addr: entry.start_page.to_addr().into(),
                size: entry.npages.to_addr().into(),
                memty: E820_TYPE_RAM.into(),
            },
        );
        i = i + 1;
    }
}

pub fn osmem_add_ram_from_allocator(
    osmem: &mut OSMem,
    vmpl: u8,
    e820: VBox<E820Table>,
    e820_size: &mut usize,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
) -> (ret: Result<VBox<E820Table>, u8>)
    requires
        e820@.is_constant(),
        e820.snp().is_vmpl0_private(),
        0 <= *old(e820_size) <= e820@@.len(),
        osmem_wf(old(osmem)@),
        old(cs).inv(),
    ensures
        osmem_wf((osmem)@),
        0 <= *(e820_size) <= e820@@.len(),
        ret.is_Ok() ==> ret.get_Ok_0().only_val_updated(e820),
        ret.is_Ok() ==> ret.get_Ok_0()@.is_constant(),
        cs.inv(),
        cs.only_lock_reg_coremode_updated(*old(cs), set![], set![spec_ALLOCATOR_lockid()]),
{
    let tmposmem = create_osmem_from_allocator(vmpl, Tracked(cs));
    // Terminate if there are too many regions.
    let e820_count = *e820_size;
    if (E820Table::const_len() - e820_count) < tmposmem.len() {
        new_strlit("too many entries\n").leak_debug();
        return Err(SM_TERM_MEM as u8);
    }
    new_strlit("Install e820\n").leak_debug();
    let e820 = add_osmem_to_e820(e820, e820_count, &tmposmem);
    *e820_size = e820_count + tmposmem.len();
    new_strlit("append osmem\n").leak_debug();
    let reserved = 0;
    let mut tmposmem = tmposmem;
    osmem.append(&mut tmposmem);
    new_strlit("end of adjust\n").leak_debug();
    Ok(e820)
}

pub fn add_ram_from_allocator(
    vmpl: u8,
    e820: &mut E820Table,
    e820_size: &mut usize,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
) -> (ret: Result<OSMem, u8>)
    requires
        old(e820)@.is_constant(),
        0 <= *old(e820_size) <= old(e820)@.len(),
        old(cs).inv(),
    ensures
        ret.is_Ok() ==> osmem_wf(ret.get_Ok_0()@),
        0 <= *(e820_size) <= e820@.len(),
        ret.is_Ok() ==> e820@.is_constant(),
        cs.inv(),
        cs.only_lock_reg_coremode_updated(*old(cs), set![], set![spec_ALLOCATOR_lockid()]),
{
    let tmposmem = create_osmem_from_allocator(vmpl, Tracked(cs));
    // Terminate if there are too many regions.
    let e820_count = *e820_size;
    if (E820Table::const_len() - e820_count) < tmposmem.len() {
        new_strlit("too many entries\n").leak_debug();
        return Err(SM_TERM_MEM as u8);
    }
    new_strlit("Install e820\n").leak_debug();
    add_osmem_to_mut_e820(e820, e820_count, &tmposmem);
    *e820_size = e820_count + tmposmem.len();
    Ok(tmposmem)
}

pub fn create_osmem_from_allocator(vmpl: u8, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (osmem:
    Vec<OSMemEntry>)
    requires
        old(cs).inv(),
    ensures
        osmem_wf((osmem)@),
        cs.inv(),
        cs.only_lock_reg_coremode_updated(*old(cs), set![], set![spec_ALLOCATOR_lockid()]),
{
    let ghost oldcs = *cs;
    // reserved some memory for security module.
    // reserved will be automatically release in the end of the function.
    new_strlit("reserve memory\n").leak_debug();
    let reserved = VBox::<Array<u8, VERISMO_RSVD_MEM>>::new_aligned_uninit(PAGE_SIZE, Tracked(cs));
    let mut tmposmem = Vec::with_capacity(16);
    let ghost prevcs = *cs;
    // Acquire allocator to prevent usage of allocator, so that we can
    // safely assign remaining memory to vmpl2.
    let tracked mut alloc_lockperm = cs.lockperms.tracked_remove(spec_ALLOCATOR_lockid());
    let (alloc_ptr, Tracked(mut allocperm), Tracked(alloc_lockperm)) = ALLOCATOR().acquire(
        Tracked(alloc_lockperm),
        Tracked(&cs.snpcore.coreid),
    );
    let mut allocator = alloc_ptr.take(Tracked(&mut allocperm));
    proof {
        assert(alloc_lockperm@.invfn.inv(allocator));
        assert(VeriSMoAllocator::invfn()(allocator));
    }
    // Find all remaining memory pages
    let tmposmem = _osmem_add_ram_from_allocator(
        &mut allocator,
        tmposmem,
        Tracked(&mut cs.snpcore),
    );
    // Release allocator to allow use of allocato in the future.
    // Only a small amount of reserved memory is left in the allocator.
    proof {
        assert(VeriSMoAllocator::invfn()(allocator));
        assert(alloc_lockperm@.invfn.inv(allocator));
        assert(allocator@.inv());
    }
    new_strlit("ready to release memory\n").leak_debug();
    alloc_ptr.put(Tracked(&mut allocperm), allocator);
    ALLOCATOR().release(
        Tracked(&mut alloc_lockperm),
        Tracked(allocperm),
        Tracked(&cs.snpcore.coreid),
    );
    proof {
        cs.lockperms.tracked_insert(spec_ALLOCATOR_lockid(), alloc_lockperm);
        oldcs.lemma_update_prop(
            prevcs,
            *cs,
            set![],
            set![spec_ALLOCATOR_lockid()],
            set![],
            set![spec_ALLOCATOR_lockid()],
        );
    }
    tmposmem
}

pub fn _lock_kernel(
    osmem: &mut OSMem,
    range: &(usize, usize),
    Tracked(snpcore): Tracked<&mut SnpCore>,
) -> (ret: usize)
    requires
        osmem_wf(old(osmem)@),
        (range.0 as int).spec_valid_pn_with(range.1 as nat),
        old(snpcore).inv(),
    ensures
        osmem_wf(osmem@),
        snpcore.inv(),
        *snpcore === *old(snpcore),
{
    let mut start = range.0;
    let end = range.0 + range.1;
    while start < end
        invariant
            osmem_wf(osmem@),
            start <= end,
            (start as int).spec_valid_pn_with((end - start) as nat),
            snpcore.inv(),
            *snpcore === *old(snpcore),
        ensures
            osmem_wf(osmem@),
            (start as int).spec_valid_pn_with((end - start) as nat),
            snpcore.inv(),
            *snpcore === *old(snpcore),
    {
        if let Some(e) = osmem_check_and_get(osmem, start, OSMemPerm::ram()) {
            let (i, mut entry) = e;
            assert(entry.wf());
            // no need to check encrytion bit since rmpadjust will
            // throw error when it is a shared page.
            /*if entry.encrypted.reveal_value() != 1 {
                    new_strlit("Cannot set shared memory to kernel page\n").leak_debug();
                    break;
                }*/
            let next_start: usize = (entry.start_page.add(entry.npages)).into();
            let tmp_end = if end > next_start {
                next_start
            } else {
                end
            };
            let tmp_start = start;
            assert(tmp_end >= start);
            let tmp_npages = tmp_end - start;
            proof {
                assert(entry.wf());
            }
            let (left, mid, right) = osmem_entry_split(entry, tmp_start, tmp_npages);
            let Tracked(mut page_perms) = mid.page_perms;
            let attr = RmpAttr::empty().set_vmpl(RICHOS_VMPL as u64).set_perms(
                OSMemPerm::new(mid.osperm.into()).set_write(0).value as u64,
            ).set_vmsa(0);
            proof {
                assert forall|i|
                    tmp_start <= i < tmp_start
                        + tmp_npages implies #[trigger] page_perms.contains_key(i)
                    && spec_rmpadjmem_requires_at(page_perms[i], i, attr@) by {
                    assert(page_perms.contains_key(i));
                    assert(spec_contains_page_perm(page_perms, i, mid.spec_osperm()));
                    assert(page_perms[i]@.wf_range((i.to_addr(), PAGE_SIZE as nat)));
                }
                assert(page_perms.dom() =~~= Set::new(
                    |i| tmp_start <= i < (tmp_start + tmp_npages),
                ));
            }
            rmpadjmem(tmp_start, tmp_npages, attr, Tracked(snpcore), Tracked(&mut page_perms));
            if left.npages.reveal_value() > 0 {
                osmem.push(left);
            }
            if right.npages.reveal_value() > 0 {
                osmem.push(right);
            }
            start = tmp_end;
        } else {
            break ;
        }
    }
    return start;
}

pub fn lock_kernel(
    osmem: &mut OSMem,
    ranges: &Vec<(usize, usize)>,
    Tracked(snpcore): Tracked<&mut SnpCore>,
)
    requires
        osmem_wf(old(osmem)@),
        forall|i|
            0 <= i < ranges@.len() ==> (ranges@[i].0 as int).spec_valid_pn_with(
                ranges@[i].1 as nat,
            ),
        old(snpcore).inv(),
    ensures
        osmem_wf(osmem@),
        snpcore.inv(),
        *snpcore === *old(snpcore),
{
    let mut i = 0;
    while i < ranges.len()
        invariant
            osmem_wf(osmem@),
            forall|i|
                0 <= i < ranges@.len() ==> (ranges@[i].0 as int).spec_valid_pn_with(
                    ranges@[i].1 as nat,
                ),
            snpcore.inv(),
            *snpcore === *old(snpcore),
    {
        let range = &ranges[i];
        let end = _lock_kernel(osmem, range, Tracked(snpcore));
        if end < range.1 {
            vc_terminate(SM_TERM_RICHOS_ERR(10), Tracked(snpcore));
        }
    }
}

} // verus!
