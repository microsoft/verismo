use super::*;
use crate::allocator::VeriSMoAllocator;
use crate::debug::Console;
use crate::lock::VSpinLock;
use crate::ptr::*;
use crate::security::richos_vmsa_invfn;
use crate::tspec::*;
use crate::tspec_e::*;

#[verifier::external]
mod trusted {
    use super::*;

    #[verifier::external]
    #[global_allocator]
    pub static _ALLOCATOR: VSpinLock<VeriSMoAllocator> = VSpinLock::new(VeriSMoAllocator::new());
}

#[verifier::external]
static _CONSOLE: VSpinLock<Console> = VSpinLock::new(Console);

use crate::pgtable_e::PtePerms;
#[verifier::external]
static _PT: VSpinLock<TrackedPTEPerms> = VSpinLock::new(TrackedPTEPerms {
    perms: Tracked::assume_new(),
});

use crate::security::TrackedSecretsOSAreaPerms;
#[verifier::external]
static _SECRET_PERM: VSpinLock<TrackedPTEPerms> = VSpinLock::new(TrackedPTEPerms {
    perms: Tracked::assume_new(),
});

use alloc::vec::Vec;

use crate::security::*;
#[verifier::external]
static _OSMEM: VSpinLock<Vec<OSMemEntry>> = VSpinLock::new(Vec::new());

use crate::snp::cpu::VmsaPage;
use crate::vbox::VBox;
#[verifier::external]
static _RICHOS_VMSA: VSpinLock<Vec<Option<VBox<VmsaPage>>>> = VSpinLock::new(Vec::new());

use trusted_hacl::SHA512Type;
#[verifier::external]
pub static _PCR: VSpinLock<Vec<SHA512Type>> = VSpinLock::new(Vec::new());

verus! {

pub closed spec fn g_range(id: Globals) -> (int, nat);

} // verus!
use self::trusted::_ALLOCATOR;
use crate::lock::MapRawLockTrait;
use crate::pgtable_e::TrackedPTEPerms;

verus! {

#[gen_shared_globals]
pub enum Globals {
    #[tname(_ALLOCATOR, VeriSMoAllocator, VeriSMoAllocator::invfn())]
    ALLOCATOR,
    #[tname(_CONSOLE, Console, Console::invfn())]
    CONSOLE,
    #[tname(_PT, TrackedPTEPerms, TrackedPTEPerms::invfn())]
    PT,
    #[tname(_SECRET_PERM, TrackedPTEPerms, TrackedPTEPerms::invfn())]
    SEC_PERM,
    #[tname(_OSMEM, Vec<OSMemEntry>, OSMemEntry::osmem_invfn())]
    OSMEM,
    #[tname(_RICHOS_VMSA, Vec<Option<VBox<VmsaPage>>>, richos_vmsa_invfn())]
    RICHOS_VMSA,
    #[tname(_PCR, Vec<SHA512Type>, crate::security::pcr::pcr_invfn())]
    PCR,
}

} // verus!
verus! {

pub open spec fn is_alloc_perm(alloc_perm: SnpPointsToData<VeriSMoAllocator>) -> bool {
    &&& alloc_perm.wf_const_default(spec_ALLOCATOR().ptrid())
    &&& alloc_perm.get_value()@.inv()
    &&& alloc_perm.get_value().is_constant()
}

} // verus!
verus! {

pub trait IsConsole {
    spec fn is_console(&self) -> bool;
}

impl IsConsole for SnpPointsToRaw {
    open spec fn is_console(&self) -> bool {
        &&& self@.wf_range(spec_CONSOLE().ptr_range())
        &&& self@.snp() === SwSnpMemAttr::spec_default()
    }
}

} // verus!
