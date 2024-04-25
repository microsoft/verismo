use super::*;
use crate::arch::addr_s::*;
use crate::arch::entities::*;

verus! {

impl<AddrT: AddrType> MemOp<AddrT> {
    #[verifier(inline)]
    pub open spec fn is_PValidate(&self) -> bool {
        self.is_RmpOp() && self.get_RmpOp_0().is_Pvalidate()
    }

    pub open spec fn to_addr_memid(&self) -> AddrMemID<AddrT> {
        match *self {
            MemOp::Read(addr_id, _) => { addr_id },
            MemOp::Write(addr_id, _, bytes) => {
                AddrMemID { range: addr_id.addr.to_mem(bytes.len()), memid: addr_id.memid }
            },
            MemOp::RmpOp(rmpop) => {
                let PageID { memid, page } = rmpop.to_page_memid();
                AddrMemID { range: page.to_mem(), memid }
            },
            MemOp::InvlPage(addr_id) => { addr_id },
            MemOp::FlushAll(memid) => {
                AddrMemID { range: SpecMem::from_range(SpecAddr::null(), 0), memid }
            },
        }
    }

    #[verifier(inline)]
    pub open spec fn to_memid(&self) -> MemID {
        self.to_addr_memid().memid
    }

    #[verifier(inline)]
    pub open spec fn to_mem(&self) -> SpecMem<AddrT> {
        self.to_addr_memid().range
    }

    #[verifier(inline)]
    pub open spec fn to_page(&self) -> SpecPage<AddrT> {
        self.to_addr_memid().range.to_page()
    }

    #[verifier(inline)]
    pub open spec fn use_gmap(&self) -> bool {
        self.is_Read() || self.is_Write() || self.is_RmpOp()
    }

    pub open spec fn is_valid(&self) -> bool {
        self.to_mem().is_valid()
    }
}

} // verus!
