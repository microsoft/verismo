use super::db_u::*;
use super::perm_s::Perm;
use super::*;
use crate::arch::addr_s::*;
use crate::arch::entities::*;
use crate::tspec::*;

verus! {
    impl<AddrT: AddrType> RmpOp<AddrT> {
        pub open spec fn to_page_memid(&self) -> PageID<AddrT> {
            match *self {
                RmpOp::RmpAdjust(page_id, _) =>  page_id,
                RmpOp::Pvalidate(page_id, _) =>  page_id,
                RmpOp::RmpUpdate(page_id, _) => page_id,
            }
        }
    }

    impl RmpOp<GuestVir> {
        pub open spec fn set_gpn(&self, page: SpecPage<GuestPhy>) -> RmpOp<GuestPhy> {
            match *self {
                RmpOp::RmpAdjust(page_id, RmpAdjustParam{gpn, psize, vmsa, vmpl, perms}) =>   {
                    RmpOp::RmpAdjust(PageID{memid: page_id.memid, page}, RmpAdjustParam{gpn: page, psize, vmsa, vmpl, perms})
                },
                RmpOp::Pvalidate(page_id, PvalidateParam{gpn, val, psize}) =>  {
                    RmpOp::Pvalidate(PageID{memid: page_id.memid, page}, PvalidateParam{gpn: page, val, psize})
                },
                RmpOp::RmpUpdate(page_id, param) => {
                    RmpOp::RmpUpdate(PageID{memid: page_id.memid, page}, param)
                },
            }
        }
    }

    impl RmpOp<GuestPhy> {
        pub open spec fn gp_op_requires(&self, rmp: &RmpMap) -> bool {
            let sp_op = self.set_spn(spec_unused());
            &&& sp_op.sp_op_requires(rmp)
        }

        pub open spec fn inv(&self) -> bool {
            self.is_Pvalidate() ==>
            self.get_Pvalidate_1().gpn === self.to_page_memid().page

        }

        pub open spec fn set_spn(&self, page: SpecPage<SysPhy>) -> RmpOp<SysPhy> {
            match *self {
                RmpOp::RmpAdjust(page_id, param) =>   {
                    RmpOp::RmpAdjust(PageID{memid: page_id.memid, page}, param)
                },
                RmpOp::Pvalidate(page_id, param) =>  {
                    RmpOp::Pvalidate(PageID{memid: page_id.memid, page}, param)
                },
                RmpOp::RmpUpdate(page_id, param) => {
                    RmpOp::RmpUpdate(PageID{memid: page_id.memid, page}, param)
                },
            }
        }

        pub open spec fn get_gpn(&self) -> GPN {
            match *self {
                RmpOp::RmpAdjust(page_id, RmpAdjustParam{gpn, psize, vmsa, vmpl, perms}) =>   {
                    gpn
                },
                RmpOp::Pvalidate(page_id, PvalidateParam{gpn, val, psize}) =>  {
                    gpn
                },
                RmpOp::RmpUpdate(page_id, param) => {
                    page_id.page
                },
            }
        }
    }
    impl RmpOp<SysPhy> {
        pub open spec fn op_requires_stateless(&self) -> bool {
            match *self {
                RmpOp::RmpAdjust(PageID{page, memid}, RmpAdjustParam { gpn, psize, vmsa, vmpl, perms }) =>  {
                    //&&& !memtype(memid, gpn).need_c_bit()
                    &&& {
                        |||!perms.contains(Perm::Write)
                        |||!memtype(memid, gpn).is_sm_int()
                    }
                },
                RmpOp::Pvalidate(PageID{page, memid}, PvalidateParam { gpn, psize, val }) =>  {
                    true
                    //&&& !memtype(memid, gpn).need_c_bit()
                },
                RmpOp::RmpUpdate(page_id, param) => {
                    true
                },
            }
        }

        pub open spec fn sp_op_requires(&self, rmp: &RmpMap) -> bool {
            &&& self.op_requires_stateless()
            &&& match *self {
                RmpOp::Pvalidate(PageID{page, memid}, PvalidateParam { gpn, psize, val }) =>  {
                    !rmp_has_gpn_memid(rmp, gpn, memid) || !memid.to_vmpl().is_VMPL0()
                }
                _ => {true}
            }
        }
    }
}
