use super::*;
use crate::arch::addr_s::*;
use crate::arch::entities::*;

verus! {
    impl MemOp<GuestVir> {
        pub open spec fn translate_gpn(&self, gpmem: GPMem, enc: bool) -> MemOp<GuestPhy> {
            match *self {
                MemOp::Read(addr_id, _) => {
                    MemOp::Read(AddrMemID{memid: addr_id.memid, range: gpmem}, enc)
                },
                MemOp::Write(addr_id, _, data) =>  {
                    MemOp::Write(AddrID{memid: addr_id.memid, addr: gpmem.first()}, enc, data)
                },
                MemOp::RmpOp(rmpop) =>  {
                    MemOp::RmpOp(rmpop.set_gpn(gpmem.to_page()))
                },
                MemOp::InvlPage(gvn_id) => { MemOp::InvlPage(AddrMemID{memid: gvn_id.memid, range: gpmem}) },
                MemOp::FlushAll(memid) => { MemOp::FlushAll(memid) },
            }
        }
    }
}
