use verismo_macro::*;

use crate::arch::addr_s::*;
use crate::arch::entities::*;
use crate::arch::mem::MemDB;
use crate::arch::memop::MemOp;
use crate::arch::reg::*;
use crate::tspec::*;

verus! {

#[is_variant]
pub enum Archx64Op {
    MemOp(MemOp<GuestVir>, CPU),
    RegWrite(CpuMemID, RegName, RegValType),
    RegRead(CpuMemID, RegName),
    VMGExit(CpuMemID),
    LoopHalt(CpuMemID),
}

#[is_variant]
pub enum Archx64Ret {
    None,
    ReadRet(ByteStream),
    RegValue(RegValType),
}

pub spec fn current_cpu() -> CPU;

#[derive(SpecGetter, SpecSetter)]
pub struct Archx64 {
    pub memdb: MemDB,
    pub regdb: Map<CpuMemID, RegDB>,
    pub entities: Map<MemID, Map<CPU, bool>>,
}

#[is_variant]
pub enum AECode {
    Mc,
    Intr,
    Nmi,
    Smi,
    Init,
    VIntr,
    Pause,
    Hlt,
    Npf,
    Vmmcall,
    VMGExit,
    Busy,
    Others,
}

#[is_variant]
pub enum NAECode {
    Npf,
    Vmmcall,
    Halt,
    NotValidated(Archx64Op),
    // TODO(ziqiao): Model more exits
    Others,
}

#[is_variant]
pub enum ExceptionCode {
    PFault(Archx64Op),
    GP(Archx64Op),
}

} // verus!
