use super::*;
use crate::arch::rmp::perm_s::Perm;

verus! {

impl Model1Eq for VRamDB {
    open spec fn model1_eq(&self, other: &Self, memid: MemID) -> bool {
        let rmp = other.spec_rmp();
        let vmpl = memid.to_vmpl();
        &&& (forall|spa: SPA|
            (rmp.dom().contains(#[trigger] spa.to_page())
                && rmp[spa.to_page()].view().spec_validated() && (vmpl >= VMPL::VMPL0
                || !rmp[spa.to_page()].view().check_vmpl(VMPL::VMPL0, Perm::Write)) && (vmpl
                >= VMPL::VMPL1 || !rmp[spa.to_page()].view().check_vmpl(VMPL::VMPL1, Perm::Write))
                && (vmpl >= VMPL::VMPL2 || !rmp[spa.to_page()].view().check_vmpl(
                VMPL::VMPL2,
                Perm::Write,
            )) && (vmpl >= VMPL::VMPL3 || !rmp[spa.to_page()].view().check_vmpl(
                VMPL::VMPL3,
                Perm::Write,
            ))) ==> (#[trigger] self.spec_sram().spec_data()[spa.value()]
                === #[trigger] other.spec_sram().spec_data()[spa.value()]))
        &&& rmp_model_eq(&self.spec_rmp(), &other.spec_rmp())
        &&& (other.spec_sram().inv() ==> self.spec_sram().inv())
    }
}

impl Model2Eq for VRamDB {
    open spec fn model2_eq(&self, other: &Self) -> bool {
        &&& (forall|spa: SPA|
            (self.spec_rmp()[spa.to_page()].view().spec_validated()
                && other.spec_rmp()[spa.to_page()].view().spec_validated()) ==> (
            self.spec_sram().spec_data()[#[trigger] spa.value()]
                === other.spec_sram().spec_data()[spa.value()]))
        &&& rmp_model_eq(&self.spec_rmp(), &other.spec_rmp())
        &&& (other.spec_sram().inv() ==> self.spec_sram().inv())
    }
}

impl VRamDB {
    // write_requires_nosysma
    pub open spec fn pte_write_requires_nosysmap(
        &self,
        gpmem_id: GPAMemID,
        enc: bool,
        data: ByteStream,
    ) -> bool {
        let gpmem = gpmem_id.range;
        let memid = gpmem_id.memid;
        let old_pte: Option<GuestPTEntry> = self.get_enc_data_ok(gpmem_id);
        let new_pte = stream_to_data::<GuestPTEntry>(data);
        let target_gpn = new_pte@.spec_ppn();
        let ptesize = spec_size::<GuestPTEntry>() as int;
        // If it is the PTE and the target gpn need c bit
        let is_last_entry = new_pte@.is_present() || memtype(
            memid,
            gpmem.to_page(),
        ).get_PTE_0().is_L0();
        let need_c_bit = (memtype(memid, target_gpn).need_c_bit() && is_last_entry);
        &&& if old_pte.is_Some() && gpmem.len() > 0 {
            let old_pte = old_pte.get_Some_0();
            &&& enc
            &&& gpmem_id.range.is_aligned(ptesize)
            &&& memtype(memid, gpmem.to_page()).is_PTE()
            &&& gpmem_id.range.len() == ptesize
            &&& target_gpn === old_pte@.spec_ppn()
            &&& need_c_bit ==> new_pte@.is_encrypted()
        } else {
            true
        }
    }

    pub open spec fn gpwrite_requires(
        &self,
        memid: MemID,
        range: GPMem,
        enc: bool,
        data: ByteStream,
    ) -> bool {
        let memty = memtype(memid, range.to_page());
        if memty.need_c_bit() {
            &&& enc
            &&& if memty.is_PTE() {
                self.pte_write_requires_nosysmap(AddrMemID { range, memid }, true, data)
            } else {
                true
            }
        } else {
            true
        }
    }

    /// Restrict VMPL0's bahavior.
    /// For memory read/write,
    ///     if the memory range is private for VMPL0, enc = true
    /// For RMP change, restrict the pvalidate and rmpadjust ops.
    pub open spec fn gpmemop_requires(&self, op: MemOp<GuestPhy>, sysmap: SysMap) -> bool {
        let AddrMemID { range: addr, memid } = op.to_addr_memid();
        match op {
            MemOp::Read(AddrMemID { range: addr, memid }, enc) => {
                if memtype(memid, addr.to_page()).need_c_bit() {
                    enc
                } else {
                    true
                }
            },
            MemOp::Write(gpmem_id, enc, data) => { self.gpwrite_requires(memid, addr, enc, data) },
            MemOp::RmpOp(rmpop) => { rmpop.gp_op_requires(&self.spec_rmp()) },
            _ => { true },
        }
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.spec_sram().inv()
        &&& rmp_inv(&self.spec_rmp())
    }

    pub open spec fn inv_sw(&self, memid: MemID) -> bool {
        rmp_inv_sw(&self.spec_rmp(), memid)
    }

    pub open spec fn inv_memid_int(&self, memid: MemID) -> bool {
        rmp_inv_memid_int(&self.spec_rmp(), memid)
    }

    pub open spec fn write_read_requires_inner(
        &self,
        memid: MemID,
        enc: bool,
        gpa: GPMem,
        rgpa: GPMem,
        sysmap: SysMap,
    ) -> bool {
        let use_asid = if enc {
            memid.to_asid()
        } else {
            ASID_FOR_HV!()
        };
        let spa = sysmap.translate_addr_seq(gpa);
        let rspa = sysmap.translate_addr_seq(rgpa);
        let rmpcheck_w = rmp_check_access(
            &self.spec_rmp(),
            memid,
            enc,
            gpa,
            Perm::Write,
            spa.to_page(),
        );
        let rmpcheck_r = rmp_check_access(
            &self.spec_rmp(),
            memid,
            enc,
            gpa,
            Perm::Read,
            rspa.to_page(),
        );
        ||| rmpcheck_w.is_Error()
        ||| rmpcheck_r.is_Error()
        ||| self.spec_sram().disjoint_write_read_requires(use_asid, spa, rspa)
    }

    pub open spec fn get<T: VTypeCast<Seq<u8>>>(
        &self,
        gpmem_id: GPAMemID,
        enc: bool,
        sysmap: SysMap,
    ) -> T {
        stream_to_data(self.get_bytes(gpmem_id, enc, sysmap))
    }

    pub open spec fn get_enc_byte_ok(&self, memid: MemID, gpa: GPA) -> Option<Byte> {
        let spn = rmp_reverse(&self.spec_rmp(), memid, gpa.to_page());
        let spa = gpa.convert(spn);
        let ret = self.sram.read_one_byte(memid.to_asid(), spa);
        if rmp_has_gpn_memid(&self.spec_rmp(), gpa.to_page(), memid) {
            Option::Some(ret)
        } else {
            Option::None
        }
    }

    pub open spec fn get_enc_bytes_ok(&self, gpmem_id: GPAMemID) -> Option<ByteStream> {
        let gpmem = gpmem_id.range;
        let spa = rmp_reverse_mem(&self.spec_rmp(), gpmem_id.memid, gpmem);
        let ret = self.sram.read_bytes_by_asid(gpmem_id.memid.to_asid(), spa);
        if rmp_has_gpn_memid(&self.spec_rmp(), gpmem.to_page(), gpmem_id.memid) {
            Option::Some(ret)
        } else {
            Option::None
        }
    }

    pub open spec fn get_enc_data_ok<T: VTypeCast<Seq<u8>>>(&self, gpmem_id: GPAMemID) -> Option<
        T,
    > {
        let bytes = self.get_enc_bytes_ok(gpmem_id);
        if bytes.is_Some() {
            Option::Some(stream_to_data(bytes.get_Some_0()))
        } else {
            Option::None
        }
    }

    pub open spec fn get_byte(&self, memid: MemID, gpa: GPA, enc: bool, sysmap: SysMap) -> Option<
        Byte,
    > {
        let spa = sysmap.translate_addr(gpa);
        let use_asid = if enc {
            memid.to_asid()
        } else {
            ASID_FOR_HV!()
        };
        if spa.is_Some() {
            Option::Some(self.sram.read_one_byte(use_asid, spa.get_Some_0()))
        } else {
            Option::None
        }
    }

    pub open spec fn get_bytes(&self, gpmem_id: GPAMemID, enc: bool, sysmap: SysMap) -> ByteStream {
        let spmem = sysmap.translate_addr_seq(gpmem_id.range);
        let use_asid = if enc {
            gpmem_id.memid.to_asid()
        } else {
            ASID_FOR_HV!()
        };
        self.sram.read_bytes_by_asid(use_asid, spmem)
    }

    /// Only the VM itself can decrypt the data at the exact spa;
    pub open spec fn read_bytes(
        &self,
        gpmem_id: GPAMemID,
        enc: bool,
        sysmap: SysMap,
    ) -> ResultOrErr<ByteStream, MemError<()>> {
        recommends(gpmem_id.memid.is_Guest());
        let op = ();
        let gpa = gpmem_id.range;
        let memid = gpmem_id.memid;
        let rmp = self.rmp;
        let asid = memid.to_asid();
        let spn = sysmap.translate(gpa.to_page());
        let use_asid = if enc {
            asid
        } else {
            ASID_FOR_HV!()
        };
        if spn.is_Some() {
            let rmpcheck = rmp_check_access(&rmp, memid, enc, gpa, Perm::Read, spn.get_Some_0());
            if rmpcheck.is_Ok() {
                let data = self.get_bytes(gpmem_id, enc, sysmap);
                ResultOrErr::Ok(data)
            } else {
                ResultOrErr::Error(MemError::NestedPF(op))
            }
        } else {
            ResultOrErr::Error(MemError::NestedPF(op))
        }
    }

    pub open spec fn spec_ret_bytes(&self, memop: MemOp<GuestPhy>, sysmap: SysMap) -> ByteStream {
        match memop {
            MemOp::Read(gpmem_id, enc) => match self.read_bytes(gpmem_id, enc, sysmap) {
                ResultOrErr::Ok(_) => self.get_bytes(gpmem_id, enc, sysmap),
                ResultOrErr::Error(err) => ByteStream::empty(),
            },
            _ => ByteStream::empty(),
        }
    }

    pub open spec fn op_read(&self, gpmem_id: GPAMemID, enc: bool, sysmap: SysMap) -> ResultWithErr<
        Self,
        MemError<()>,
    > {
        recommends(gpmem_id.memid.is_Guest());
        match self.read_bytes(gpmem_id, enc, sysmap) {
            ResultOrErr::Ok(_) => ResultWithErr::Ok(*self),
            ResultOrErr::Error(err) => ResultWithErr::Error(*self, err),
        }
    }

    pub open spec fn op_write(
        &self,
        gpa_id: AddrID<GuestPhy>,
        enc: bool,
        data: ByteStream,
        sysmap: SysMap,
    ) -> ResultWithErr<Self, MemError<()>>
        recommends
            gpa_id.memid.is_Guest(),
    {
        let gpa = gpa_id.addr;
        let gpmem = gpa.to_mem(data.len());
        let memid = gpa_id.memid;
        let rmp = self.rmp;
        let asid = memid.to_asid();
        let spn = sysmap.translate(gpa.to_page());
        let spa_seq = sysmap.translate_addr_seq(gpmem);
        let use_asid = if enc {
            asid
        } else {
            ASID_FOR_HV!()
        };
        if spa_seq.is_valid() {
            let spn = spn.get_Some_0();
            let rmpcheck = rmp_check_access(&rmp, memid, enc, gpmem, Perm::Write, spn);
            if rmpcheck.is_Ok() {
                let new = self.spec_set_sram(self.spec_sram().write_raw(use_asid, spa_seq, data));
                ResultWithErr::Ok(new)
            } else {
                ResultWithErr::Error(*self, rmpcheck.get_Error_0().with_param(()))
            }
        } else {
            ResultWithErr::Error(*self, MemError::NestedPF(()))
        }
    }

    pub open spec fn rmp_op(&self, sysmap: SysMap, rmpop: RmpOp<GuestPhy>) -> ResultWithErr<
        Self,
        MemError<RmpOp<GuestPhy>>,
    > {
        let spn = sysmap.translate(rmpop.get_gpn());
        if spn.is_Some() {
            let spn = spn.get_Some_0();
            let spa_rmpop = rmpop.set_spn(spn);
            match rmp_op(&self.spec_rmp(), spa_rmpop) {
                ResultWithErr::Ok(newrmp) => ResultWithErr::Ok(self.spec_set_rmp(newrmp)),
                ResultWithErr::Error(_, err) => ResultWithErr::Error(*self, err.with_param(rmpop)),
            }
        } else {
            ResultWithErr::Error(*self, MemError::NestedPF(rmpop))
        }
    }

    #[verifier(opaque)]
    pub open spec fn op(&self, sysmap: SysMap, memop: MemOp<GuestPhy>) -> ResultWithErr<
        Self,
        MemError<MemOp<GuestPhy>>,
    > {
        match memop {
            MemOp::RmpOp(rmpop) => {
                let ret = self.rmp_op(sysmap, rmpop);
                ret.replace_err(ret.to_err().with_param(memop))
            },
            MemOp::Read(gpmem_id, enc) => {
                let ret = self.op_read(gpmem_id, enc, sysmap);
                ret.replace_err(ret.to_err().with_param(memop))
            },
            MemOp::Write(gpa_id, enc, data) => {
                let ret = self.op_write(gpa_id, enc, data, sysmap);
                ret.replace_err(ret.to_err().with_param(memop))
            },
            _ => { ResultWithErr::Ok(*self) },
        }
    }
}

} // verus!
