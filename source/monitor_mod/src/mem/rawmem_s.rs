use super::*;
use crate::registers::SnpCore;

verus! {

pub tracked struct SnpMemCoreConsole {
    pub memperm: RawMemPerms,
    pub cc: crate::snp::SnpCoreConsole,
}

impl SnpMemCoreConsole {
    pub open spec fn wf(&self) -> bool {
        &&& self.cc.wf()
        &&& self.memperm.wf()
    }

    pub open spec fn wf_core(&self, cpu: nat) -> bool {
        &&& self.wf()
        &&& self.cc.snpcore.cpu() == cpu
    }
}

} // verus!
