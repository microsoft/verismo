use super::*;

verus! {
    impl MemDB
    {
        pub open spec fn spec_g_page_table(&self, memid: MemID) -> GuestPTRam
        {
            spec_unused::<GuestPTRam>().spec_set_ram(self.spec_vram()).spec_set_l0_entry(self.spec_l0_entry())
        }

        pub open spec fn to_mem_map(&self, memid: MemID) -> MemMap<GuestVir, GuestPhy>
        {
            MemMap {
                db: self.spec_g_page_table(memid).to_mem_map(self.spec_sysmap()[memid], memid).db.union_prefer_right
                (self.spec_tlb().to_mem_map(memid).db)
            }
        }

        pub open spec fn to_spop(&self, memop: MemOp<GuestPhy>) -> MemOp<SysPhy>
        {
            let AddrMemID { range: gva, memid: op_memid } = memop.to_addr_memid();
            let sysmap = self.sysmap[op_memid];
            let spa = sysmap.translate_addr_seq(gva);
            memop.translate_spn(spa)
        }

        pub open spec fn to_gpop(&self, memop: MemOp<GuestVir>) -> MemOp<GuestPhy>
        {
            let gvmem = memop.to_mem();
            let op_memid = memop.to_memid();
            let guestmap = self.to_mem_map(op_memid);
            let gpmem = gvmem.convert(
                guestmap.translate(gvmem.to_page()).get_Some_0()
            );
            let enc = guestmap.is_encrypted(gvmem.to_page());
            memop.translate_gpn(gpmem, enc.get_Some_0())
        }


        pub open spec fn op(&self, memop: MemOp<GuestVir>) -> ResultWithErr<Self, MemError<MemOp<GuestVir>>>
        {
            let ret = match memop {
                MemOp::Read(_, _) => {
                    self.op_by_gpn_memtype(memop)
                },
                MemOp::Write(_, _, _) => {
                    //self.op_write(gva_memid, data)
                    self.op_by_gpn_memtype(memop)
                },
                MemOp::RmpOp(rmpop) => {
                    match rmpop {
                        RmpOp::RmpAdjust(_, _) => self.op_rmpadjust(memop),
                        RmpOp::Pvalidate(_, _) => self.op_pvalidate(memop),
                        RmpOp::RmpUpdate(_, _) => self.op_rmpupdate(memop),
                    }
                },
                MemOp::InvlPage(gva_memid) => self.op_invlpg(gva_memid),
                MemOp::FlushAll(memid) => self.op_flush(memid),
            };
            ret.replace_err(ret.to_err().with_param(memop))
        }

        pub open spec fn op_invlpg(&self, gva_memid: GVAMemID) -> ResultWithErr<Self, MemError<MemOp<GuestVir>>>
        {
            let gva = gva_memid.range;
            let memid = gva_memid.memid;
            let tlb_idx = TLBIdx(memid, gva[0].to_page());
            ResultWithErr::Ok(self.spec_set_tlb(self.spec_tlb().invlpg(tlb_idx)))
        }

        pub open spec fn op_flush(&self, memid: MemID) -> ResultWithErr<Self, MemError<MemOp<GuestVir>>>
        {
            ResultWithErr::Ok(self.spec_set_tlb(self.spec_tlb().flush_memid(memid)))
        }

        pub open spec fn op_read(&self, gva_memid: GVAMemID) -> ResultWithErr<Self, MemError<MemOp<GuestVir>>>
        {
            self.op_by_gpn_memtype(MemOp::Read(gva_memid, false))
        }

        pub open spec fn ret(&self, memop: MemOp<GuestVir>) -> ByteStream
        {
            let gpa_memop = self.to_gpop(memop);
            let op_memid = memop.to_memid();
            let sysmap = self.spec_sysmap()[op_memid];
            if self.op(memop).is_Error() {
                ByteStream::empty()
            } else {
                self.spec_vram().spec_ret_bytes(gpa_memop, sysmap)
            }
        }

        /// Access checks:
        ///     1. guest page table check (present)
        ///     2. sys page table check (see VRamDB)
        ///     3. rmp check (see VRamDB)
        pub open spec fn op_by_gpn_memtype(&self, memop: MemOp<GuestVir>) -> ResultWithErr<Self, MemError<MemOp<GuestVir>>>
        {
            let memid = memop.to_memid();
            let gva = memop.to_mem();
            let sysmap = self.spec_sysmap()[memid];
            let guestmap = self.to_mem_map(memid);
            let valid_gpa = guestmap.translate(gva.to_page()).is_Some();
            let tlb_idx = TLBIdx(memid, gva.to_page());
            let gpa_memop = self.to_gpop(memop);
            if !valid_gpa {
                ResultWithErr::Error(*self, MemError::PageFault(memop))
            } else {
                let entry = guestmap[gva.to_page()];
                let tmp = self.spec_set_tlb(self.tlb.load(tlb_idx, entry.get_Some_0()));
                // Update data related RAM or RMP
                match self.spec_vram().op(sysmap, gpa_memop)
                {
                    ResultWithErr::Ok(ret) => {
                        ResultWithErr::Ok(
                            tmp.spec_set_vram(ret)
                        )
                    },
                    ResultWithErr::Error(ret, err) => {
                        ResultWithErr::Error(
                            tmp.spec_set_vram(ret),
                            err.with_param(memop)
                        )
                    },
                }
            }
        }

        pub open spec fn op_pvalidate(&self, op: MemOp<GuestVir>) -> ResultWithErr<Self, MemError<MemOp<GuestVir>>>
        {
            if let MemOp::RmpOp(RmpOp::Pvalidate(gvn_memid, param)) = op {
                let memid = gvn_memid.memid;
                let gvn = gvn_memid.page;
                let psize = param.psize;

                if memid.is_Hv() || memid.to_vmpl() != VMPL::VMPL0 {
                    ResultWithErr::Error(*self, MemError::RmpOp(RmpFault::Unsupported, op))
                } else if (psize == PageSize::Size2m) && !gvn.valid_as_size(psize) {
                    ResultWithErr::Error(*self, MemError::RmpOp(RmpFault::Input, op))
                } else {
                    self.op_by_gpn_memtype(op)
                }
            } else {
                ResultWithErr::Ok(*self)
            }
        }

        pub open spec fn op_rmpadjust(&self, op: MemOp<GuestVir>) -> ResultWithErr<Self, MemError<MemOp<GuestVir>>>
        {
            if let MemOp::RmpOp(RmpOp::RmpAdjust(gvn_memid, param)) = op {
                let memid = gvn_memid.memid;
                let gvn = gvn_memid.page;
                let psize = param.psize;
                let vmpl = param.vmpl;
                if memid.is_Hv() {
                    ResultWithErr::Error(*self, MemError::RmpOp(RmpFault::Unsupported, op))
                } else if (psize == PageSize::Size2m) && !gvn.valid_as_size(psize) {
                    ResultWithErr::Error(*self, MemError::RmpOp(RmpFault::Input, op))
                } else if memid.to_vmpl() >= vmpl {
                    ResultWithErr::Error(*self, MemError::RmpOp(RmpFault::Perm, op))
                } else {
                    self.op_by_gpn_memtype(op)
                }
            } else {
                ResultWithErr::Ok(*self)
            }
        }

        pub open spec fn op_rmpupdate(&self, op: MemOp<GuestVir>) -> ResultWithErr<Self, MemError<MemOp<GuestVir>>>
        {
            if let MemOp::RmpOp(RmpOp::RmpUpdate(gvn_memid, param)) = op {
                let memid = gvn_memid.memid;
                let gvn = gvn_memid.page;
                if !memid.is_Hv() {
                    ResultWithErr::Error(*self, MemError::RmpOp(RmpFault::Unsupported, op))
                } else {
                    self.op_by_gpn_memtype(op)
                }
            } else {
                ResultWithErr::Ok(*self)
            }
        }
    }
}
