use super::*;
use crate::arch::addr_s::*;
use crate::arch::entities::*;
use crate::tspec::*;

verus! {

impl<VT: AddrType, PT: AddrType> MemMap<VT, PT> {
    #[verifier(inline)]
    pub open spec fn spec_index(&self, vpage: SpecPage<VT>) -> Option<SpecPageTableEntry<PT>> {
        if self.db.dom().contains(vpage) {
            Option::Some(self.db.spec_index(vpage))
        } else {
            Option::None
        }
    }

    pub open spec fn is_valid(&self) -> bool {
        forall|page: SpecPage<VT>| #[trigger]
            page.is_valid() && self.translate(page).is_Some() ==> self.translate(
                page,
            ).get_Some_0().is_valid()
    }

    #[verifier(external_body)]
    pub broadcast proof fn axiom_is_valid(&self)
        ensures
            self.is_valid(),
    {
    }

    pub open spec fn is_encrypted(&self, vpage: SpecPage<VT>) -> Option<bool> {
        let entry = self.spec_index(vpage);
        if entry.is_Some() {
            Option::Some(entry.get_Some_0().is_encrypted())
        } else {
            Option::None
        }
    }

    pub open spec fn is_encrypted_and_some(&self, vpage: SpecPage<VT>) -> bool {
        self.translate(vpage).is_Some() && self.is_encrypted(vpage).get_Some_0()
    }

    pub open spec fn is_encrypted_or_none(&self, vpage: SpecPage<VT>) -> bool {
        self.translate(vpage).is_None() || self.is_encrypted(vpage).get_Some_0()
    }

    /// Simplified translation
    pub open spec fn translate(&self, vpage: SpecPage<VT>) -> Option<SpecPage<PT>> {
        let entry = self.spec_index(vpage);
        if entry.is_Some() {
            entry.get_Some_0().spec_translate_page(vpage)
        } else {
            Option::None
        }
    }

    /// Simplified translation
    pub open spec fn translate_addr(&self, addr: SpecAddr<VT>) -> Option<SpecAddr<PT>> {
        let page = addr.to_page();
        let ppage = self.translate(page);
        match ppage {
            Option::None => { Option::None },
            Option::Some(p) => { Option::Some(p.to_addr() + addr.to_offset()) },
        }
    }

    pub open spec fn translate_addr_seq(&self, addrs: SpecMem<VT>) -> SpecMem<PT> {
        if self.translate(addrs.to_page()).is_None() {
            SpecMem::from_range(SpecAddr::null(), 0)
        } else {
            addrs.convert(self.translate(addrs.to_page()).get_Some_0())
        }
    }

    pub open spec fn reverse(&self, page: SpecPage<PT>) -> Option<SpecPage<VT>> {
        if exists|gvn|
            (#[trigger] self.translate(gvn)).is_Some() && (self.translate(gvn).get_Some_0()
                =~= page) {
            let ret = choose|gvn|
                (#[trigger] self.translate(gvn)).is_Some() && (self.translate(gvn).get_Some_0()
                    =~= page);
            Option::Some(ret)
        } else {
            Option::None
        }
    }

    pub open spec fn reverse_trans_addr(&self, addr: SpecAddr<PT>) -> Option<SpecAddr<VT>> {
        let page = addr.to_page();
        let ppage = self.reverse(page);
        match ppage {
            Option::None => { Option::None },
            Option::Some(p) => { Option::Some(p.to_addr() + addr.to_offset()) },
        }
    }

    #[verifier(opaque)]
    /// Only used when proving model corrretness.
    /// Not used as SM's invariant.
    pub open spec fn is_one_to_one_map(&self) -> bool {
        &&& (forall|vpage: SpecPage<VT>|
            ((#[trigger] self.translate(vpage)).is_Some()) ==> (self.reverse(
                self.translate(vpage).get_Some_0(),
            ).is_Some() && self.reverse(self.translate(vpage).get_Some_0()).get_Some_0() =~= vpage))
        &&& (forall|ppage: SpecPage<PT>|
            ((#[trigger] self.reverse(ppage)).is_Some()) ==> (self.translate(
                self.reverse(ppage).get_Some_0(),
            ).is_Some() && self.translate(self.reverse(ppage).get_Some_0()).get_Some_0() =~= ppage))
    }

    #[verifier(opaque)]
    pub open spec fn is_identity_map(&self) -> bool {
        &&& (forall|vpage: SpecPage<VT>|
            ((#[trigger] self.translate(vpage)).is_Some()) ==> self.translate(
                vpage,
            ).get_Some_0().as_int() === vpage.as_int())
    }
}

impl MemMap<GuestVir, GuestPhy> {
    #[verifier(opaque)]
    pub open spec fn inv_encrypted_priv_mem(&self, memid: MemID) -> bool {
        &&& forall|gvn: GVN|
            gvn.is_valid() && self.need_c_bit(memid, gvn) ==> #[trigger] self.is_encrypted_or_none(
                gvn,
            )
    }

    pub open spec fn need_c_bit(&self, memid: MemID, gvn: GVN) -> bool {
        ||| memtype(
            memid,
            self.translate(gvn).get_Some_0(),
        ).need_c_bit()
        //||| rmp.has_gpn_memid(gvn, memid)

    }
}

} // verus!
