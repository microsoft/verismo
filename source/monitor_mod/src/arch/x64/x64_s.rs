use super::def_s::Archx64;
use super::*;

verus! {
    impl Archx64Op {
        pub open spec fn is_valid(&self) -> bool {
            match self {
                Archx64Op::MemOp(memop, _) => memop.is_valid(),
                _ => true,
            }
        }
        pub open spec fn start_cpu_with_vmsa(&self) -> Option<CPU> {
            match self {
                Archx64Op::MemOp(memop, _) => {
                    if let MemOp::RmpOp(RmpOp::RmpAdjust(_, params)) = memop {
                        if params.vmsa {
                            Option::Some(memop.to_page().as_int() as nat)
                        } else {
                            Option::None
                        }
                    } else {
                        Option::None
                    }
                }
                _ => {Option::None}
            }
        }

        pub open spec fn cpu_memid(&self) -> CpuMemID {
            match *self {
                Archx64Op::MemOp(memop, cpu) => CpuMemID(cpu, memop.to_memid()),
                Archx64Op::RegWrite(id, reg_name, _) => id,
                Archx64Op::RegRead(id, _) => id,
                Archx64Op::VMGExit(id) => id,
                Archx64Op::LoopHalt(id) => id,
            }
        }

        pub open spec fn cpu(&self) -> CPU {
            self.cpu_memid().cpu()
        }

        pub open spec fn to_memid(&self) -> MemID {
            self.cpu_memid().memid()
        }

        pub open spec fn memop(&self) -> MemOp<GuestVir> {
            self.get_MemOp_0()
        }
    }

    impl Archx64 {

        #[verifier(external_body)]
        #[verifier(broadcast_forall)]
        pub proof fn axiom_reg_dom(&self, cpumemid: CpuMemID)
        ensures
            self.spec_regdb().dom().contains(cpumemid)
        {}

        #[verifier(external_body)]
        #[verifier(broadcast_forall)]
        pub proof fn axiom_entities_dom(&self, memid: MemID)
        ensures
            self.spec_entities().dom().contains(memid)
        {}

        pub open spec fn spec_cpu(&self) -> CPU{
            current_cpu()
        }

        pub open spec fn is_run(&self, cpu_memid: CpuMemID) -> bool
        {
            let memid = cpu_memid.memid();
            let cpu = cpu_memid.cpu();
            self.spec_entities()[memid].dom().contains(cpu) &&
            self.spec_entities()[memid][cpu]
        }

        pub open spec fn is_stop(&self, cpu_memid: CpuMemID) -> bool
        {
            let memid = cpu_memid.memid();
            let cpu = cpu_memid.cpu();
            self.spec_entities()[memid].dom().contains(cpu) &&
            !self.spec_entities()[memid][cpu]
        }

        pub open spec fn has_stopped(&self, memid: MemID) -> bool
        {
            exists |cpu| self.spec_entities()[memid].dom().contains(cpu) &&
                        !#[trigger]self.spec_entities()[memid][cpu]
        }

        pub open spec fn no_concurrent_cpu(&self, cpu_memid: CpuMemID) -> bool
        {
            let memid = cpu_memid.memid();
            let cpus = self.spec_entities()[memid].dom();
            cpus=~~=(set![cpu_memid.cpu()])
        }

        pub open spec fn stop_cpu(&self, memid: MemID, cpu: CPU) -> Self {
            let memid_entries = self.spec_entities()[memid].insert(cpu, false);
            self.spec_set_entities(
                self.spec_entities().insert(memid, memid_entries))
        }

        pub open spec fn start_cpu(&self, memid: MemID, cpu: CPU) -> Self {
            let memid_entries = self.spec_entities()[memid].insert(cpu, true);
            if !self.is_stop(CpuMemID(cpu, memid)) {
                self
                    .spec_set_entities(
                    self.spec_entities().insert(memid, memid_entries))
            } else {
                *self
            }
        }

        /// TODO
        pub open spec fn spec_hv_update(&self, op: Archx64Op) -> Self {
            self.stop_cpu(op.to_memid(), op.cpu())
        }

        /// TODO
        pub open spec fn spec_vc_handle(&self, op: Archx64Op, err: NAECode) -> Self {
            self.stop_cpu(op.to_memid(), op.cpu())
        }

        /// TODO
        pub open spec fn spec_exception_handle(&self, op: Archx64Op, err: ExceptionCode) -> Self {
            self.stop_cpu(op.to_memid(), op.cpu())
        }

        /// TODO
        pub open spec fn spec_vmexit_handle(&self, op: Archx64Op, err: AECode) -> Archx64 {
            match err {
                AECode::VMGExit => {
                    *self
                }
                _ => {
                    self.stop_cpu(op.to_memid(), op.cpu())
                }
            }
        }

        #[verifier(inline)]
        pub open spec fn handle_mem_err_fn(err: MemError<MemOp<GuestVir>>) -> (bool, spec_fn(Self, Archx64Op) -> Self) {
            match err {
                MemError::NoRam(memop) => (true, |arch: Self, op: Archx64Op| arch.spec_vmexit_handle(op, AECode::Npf)),
                MemError::NotValidated(memop) => (true, |arch: Self, op: Archx64Op|arch.spec_vc_handle(op, NAECode::NotValidated(Archx64Op::MemOp(memop, op.cpu())))),
                MemError::NestedPF(memop) => (true, |arch: Self, op: Archx64Op|arch.spec_vmexit_handle(op, AECode::Npf)),
                MemError::PageFault(memop) => (true, |arch: Self, op: Archx64Op|arch.spec_exception_handle(op, ExceptionCode::PFault(Archx64Op::MemOp(memop, op.cpu())))),
                MemError::RmpOp(fault, memop) => if memop.is_RmpOp() {
                    match fault {
                        RmpFault::Unsupported => {
                            (true, |arch: Self, op: Archx64Op| arch.spec_exception_handle(op, ExceptionCode::GP(Archx64Op::MemOp(memop, op.cpu()))))
                        },
                        RmpFault::Size => {
                            (false, |arch: Self, op: Archx64Op|arch.op_write_reg(op.cpu_memid(), RegName::Rax, RMP_FAIL_SIZEMISMATCH))
                        },
                        RmpFault::Input => {
                            (false, |arch: Self, op: Archx64Op|arch.op_write_reg(op.cpu_memid(), RegName::Rax, RMP_FAIL_INPUT))
                        },
                        RmpFault::Perm => {
                            (false, |arch: Self, op: Archx64Op|arch.op_write_reg(op.cpu_memid(), RegName::Rax, RMP_FAIL_PERMISSION))
                        },
                        RmpFault::DoubleVal => {
                            (false, |arch: Self, op: Archx64Op| {
                            let rflags = arch.spec_regdb()[op.cpu_memid()][RegName::Rflags];
                            let update = bits_p::spec_bit_set(rflags as u64,
                                RflagBit::CF.as_int() as u64);
                            arch.op_write_reg(op.cpu_memid(), RegName::Rflags, update)
                            })
                        }
                    }
                } else {
                    // unreacheable
                    (true, |arch: Self, op: Archx64Op| arch.stop_cpu(op.to_memid(), op.cpu()))
                },
                MemError::Others(memop) => (true, |arch: Self, op: Archx64Op| arch.spec_exception_handle(op, ExceptionCode::GP(Archx64Op::MemOp(memop, op.cpu())))),
            }
        }

        /// Update the VM status
        /// * The update will trigger corresponding traps handler
        /// * When err is VMExit related, it calls the spec_vmexit_handle.
        pub open spec fn handle_mem_err(&self, op: Archx64Op, err: MemError<MemOp<GuestVir>>) -> Self {
            let cpu_memid = op.cpu_memid();
            Self::handle_mem_err_fn(err).1(*self, op)
        }

        pub open spec fn op(&self, op: Archx64Op) -> Archx64
        {
            if !self.is_run(op.cpu_memid()) {
                *self
            } else {
                match op {
                    Archx64Op::MemOp(memop, _) => {
                        let init = if let MemOp::RmpOp(rmpop) = memop {
                            self.op_write_reg(op.cpu_memid(), RegName::Rax, 0)
                                .op_write_reg(op.cpu_memid(), RegName::Rflags, 0)
                        } else {
                            *self
                        };
                        match init.spec_memdb().op(memop) {
                            ResultWithErr::Ok(newmem) => {
                                let new = init.spec_set_memdb(newmem);
                                let cpu = op.start_cpu_with_vmsa();
                                if cpu.is_Some() {
                                    new.start_cpu(op.to_memid(), cpu.get_Some_0())
                                } else {
                                    new
                                }
                            },
                            ResultWithErr::Error(newmem, err) => {
                                init.spec_set_memdb(newmem).handle_mem_err(op, err)
                            },
                        }
                    },
                    Archx64Op::RegWrite(_, name, val) => {
                        if op.cpu() === self.spec_cpu() {
                            self.op_write_reg(op.cpu_memid(), name, val)
                        } else {
                            *self
                        }
                    },
                    Archx64Op::RegRead(_, _) => {
                        *self
                    },
                    Archx64Op::LoopHalt(_) => {
                        self.stop_cpu(op.to_memid(), op.cpu())
                    },
                    Archx64Op::VMGExit(_) => {
                        if op.cpu() === self.spec_cpu() {
                            self.spec_vmexit_handle(op, AECode::VMGExit)
                        } else {
                            *self
                        }
                    }
                }
            }
        }

        /// TODO: link Cr3 with memdb::l0_entry
        pub open spec fn op_write_reg(&self, memid: CpuMemID, name: RegName, val: RegValType) -> Archx64  {
            self.spec_set_regdb(self.spec_regdb().insert(memid, self.spec_regdb()[memid].insert(name, val)))
        }

        pub open spec fn validation_ok(&self, cpumemid: CpuMemID) -> bool {
            &&& self.spec_regdb()[cpumemid][RegName::Rax] == 0
            &&& !spec_has_bit_set(self.spec_regdb()[cpumemid][RegName::Rflags], 0)
        }

        pub open spec fn rmpadjust_ok(&self, cpumemid: CpuMemID) -> bool {
            &&& self.spec_regdb()[cpumemid][RegName::Rax] == 0
        }

        pub open spec fn ret(&self, op: Archx64Op) -> Archx64Ret {
            match op {
                Archx64Op::MemOp(memop, _) => {
                    match memop {
                        MemOp::Read(_, _) => {
                            if self.op(op).is_run(op.cpu_memid()) {
                                Archx64Ret::ReadRet(self.spec_memdb().ret(memop))
                            } else {
                                Archx64Ret::ReadRet(ByteStream::empty())
                            }
                        },
                        _ => {
                            Archx64Ret::None
                        }
                    }
                },
                Archx64Op::RegRead(memid, name) => {
                    Archx64Ret::RegValue(self.spec_regdb()[memid].spec_index(name))
                },
                _ => {
                    Archx64Ret::None
                }
            }
        }
    }
}
