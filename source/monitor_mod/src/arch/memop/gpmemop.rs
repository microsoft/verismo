use super::*;
use crate::arch::addr_s::*;
use crate::arch::entities::*;

verus! {
    impl MemOp<GuestPhy> {
        pub open spec fn translate_spn(&self, spmem: SpecMem<SysPhy>) -> MemOp<SysPhy>
        {
            match *self {
                MemOp::Read(addr_id, enc) => {
                    MemOp::Read(AddrMemID{memid: addr_id.memid, range: spmem}, enc)
                },
                MemOp::Write(addr_id, enc, data) =>  {
                    MemOp::Write(AddrID{memid: addr_id.memid, addr: spmem.first()}, enc, data)
                },
                MemOp::RmpOp(rmpop) =>  {
                    MemOp::RmpOp(rmpop.set_spn(spmem.to_page()))
                },
                MemOp::InvlPage(gvn_id) => { MemOp::InvlPage(AddrMemID{memid: gvn_id.memid, range: spmem}) },
                MemOp::FlushAll(memid) => { MemOp::FlushAll(memid) },
            }
        }

        #[verifier(inline)]
        pub open spec fn to_enc(&self) -> bool {
            match *self {
                MemOp::Read(_, enc) => {
                    enc
                },
                MemOp::Write(_, enc, _) =>  {
                    enc
                },
                _ => {
                    false
                },
            }
        }
    }
}
