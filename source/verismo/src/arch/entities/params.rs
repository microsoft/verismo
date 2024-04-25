use super::*;
use crate::arch::addr_s::*;
use crate::tspec::*;

verus! {

pub struct EncGPA {
    pub memid: MemID,
    pub gpa: SpecMem<GuestPhy>,
    pub enc: bool,
}

impl EncGPA {
    pub open spec fn gpa_id(&self) -> GPAMemID {
        AddrMemID { range: self.gpa, memid: self.memid }
    }
}

} // verus!
verus! {

pub struct AddrMemID<AddrT> {
    pub range: SpecMem<AddrT>,
    pub memid: MemID,
}

impl AddrMemID<GuestPhy> {
    pub open spec fn memtype(&self) -> MemType {
        memtype(self.memid, self.range.to_page())
    }
}

} // verus!
verus! {

pub type GPAMemID = AddrMemID<GuestPhy>;

pub type GVAMemID = AddrMemID<GuestVir>;

pub struct PageID<AddrT> {
    pub page: SpecPage<AddrT>,
    pub memid: MemID,
}

impl PageID<GuestPhy> {
    pub open spec fn memtype(&self) -> MemType {
        memtype(self.memid, self.page)
    }
}

pub struct AddrID<AddrT> {
    pub addr: SpecAddr<AddrT>,
    pub memid: MemID,
}

} // verus!
