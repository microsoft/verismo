use super::*;

verus! {

impl Archx64 {
    pub proof fn proof_op_inv_reg(&self, memid: MemID, arch_op: Archx64Op)
        requires
            self.inv(memid),
            arch_op.to_memid().is_sm(memid) ==> arch_op.op_requires(memid, self),
        ensures
            self.op(arch_op).inv_regdb_any_cpu(memid),
    {
        let new = self.op(arch_op);
        assert forall|cpu| new.inv_regdb(cpu, memid) by {
            assert(self.inv_regdb(cpu, memid));
            assert(new.spec_regdb()[CpuMemID(cpu, memid)][RegName::Cr3]
                === self.spec_regdb()[CpuMemID(cpu, memid)][RegName::Cr3]);
            assert(new.spec_regdb()[CpuMemID(cpu, memid)][RegName::Cpl]
                === self.spec_regdb()[CpuMemID(cpu, memid)][RegName::Cpl]);
        }
    }

    pub proof fn proof_op_inv(&self, memid: MemID, arch_op: Archx64Op)
        requires
            self.inv(memid),
            memid.to_vmpl().is_VMPL0(),
            arch_op.is_valid(),
            arch_op.to_memid().is_sm(memid) ==> arch_op.op_requires(memid, self),
        ensures
            self.op(arch_op).inv(memid),
    {
        let new = self.op(arch_op);
        if arch_op.is_MemOp() {
            self.spec_memdb().proof_op_inv(memid, arch_op.memop());
        }
        self.proof_op_inv_reg(memid, arch_op);
        assert(new.spec_memdb().inv(memid));
        assert(new.inv_regdb_any_cpu(memid));
        assert(new.spec_entities()[memid].dom().contains(new.spec_cpu()));
    }

    pub proof fn proof_run_indicate_memop_is_ok(&self, memid: MemID, arch_op: Archx64Op)
        requires
            self.inv(memid),
            arch_op.is_MemOp(),
            arch_op.memop().is_Read() || arch_op.memop().is_Write(),
            self.op(arch_op).is_run(arch_op.cpu_memid()),
        ensures
            self.spec_memdb().op(arch_op.memop()).is_Ok() || self.spec_memdb().op(
                arch_op.memop(),
            ).get_Error_1().is_RmpOp(),
            self.spec_memdb().to_mem_map(arch_op.to_memid()).translate(
                arch_op.memop().to_mem().to_page(),
            ).is_Some(),
    {
        if !self.spec_memdb().to_mem_map(arch_op.to_memid()).translate(
            arch_op.memop().to_mem().to_page(),
        ).is_Some() {
            self.spec_memdb().lemma_op_error(arch_op.memop());
            assert(!self.op(arch_op).is_run(arch_op.cpu_memid()));
        }
    }

    pub proof fn lemma_invalid_gmap_error(&self, memid: MemID, arch_op: Archx64Op)
        requires
            self.inv(memid),
            arch_op.is_MemOp(),
            arch_op.memop().use_gmap(),
            self.spec_memdb().to_mem_map(arch_op.to_memid()).translate(
                arch_op.memop().to_page(),
            ).is_None(),
        ensures
            !self.op(arch_op).is_run(arch_op.cpu_memid()) || self.op(arch_op).spec_memdb()
                === self.spec_memdb() || arch_op.memop().is_RmpOp() && self.op(
                arch_op,
            ).spec_regdb()[arch_op.cpu_memid()][RegName::Rax] != 0,
    {
        self.spec_memdb().lemma_op_error(arch_op.memop());
    }

    pub proof fn proof_invalid_gmap_error(&self, memid: MemID, arch_op: Archx64Op)
        requires
            self.inv(memid),
            arch_op.is_MemOp(),
            arch_op.memop().use_gmap(),
            memid.to_vmpl().is_VMPL0(),
            arch_op.to_memid().is_sm(memid),
            self.spec_memdb().to_mem_map_ok(arch_op.to_memid()).translate(
                arch_op.memop().to_page(),
            ).is_None(),
        ensures
            !self.op(arch_op).is_run(arch_op.cpu_memid()) || self.op(arch_op).spec_memdb()
                === self.spec_memdb() || arch_op.memop().is_RmpOp() && self.op(
                arch_op,
            ).spec_regdb()[arch_op.cpu_memid()][RegName::Rax] != 0,
    {
        self.spec_memdb().lemma_mem_map_to_mem_map_ok(memid, arch_op.memop().to_page());
        self.lemma_invalid_gmap_error(memid, arch_op);
    }
}

} // verus!
