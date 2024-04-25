use super::*;
use crate::arch::addr_s::PAGE_SIZE;
use crate::boot::params::{E820Entry, E820_TYPE_RSVD};
use crate::debug::VPrint;
use crate::registers::SnpCore;
use crate::snp::SnpCoreConsole;

pub const MAX_VALIDATED_E820: usize = 16;

verismo_simple! {
pub type ValidatedE820Table = [E820Entry; MAX_VALIDATED_E820];

#[repr(C, align(1))]
#[derive(SpecSetter, SpecGetter)]
pub struct MonitorParams {
    pub cpu_count: u64,     // CPU count,
    pub cpuid_page: u64,    // cpuid page gpa
    pub secret_page: u64,   // secret page gpa
    pub hv_param: u64,      // param page gpa
    pub validated_entries: u64,
    pub validated_e820: ValidatedE820Table,
    pub acpi: u64,
    pub acpi_size: u64,
    pub richos_start: u64,
    pub richos_size: u64,
    pub richos_cmdline: [u8; 256],
    pub richos_cmdline_len: u64,
}

#[cfg(debug_assertions)]
#[repr(C, align(1))]
#[derive(SpecSetter, VPrint, SpecGetter)]
pub struct SimpleMonitorParams {
    pub cpuid_page: u64,         // cpuid page gpa
    pub secret_page: u64, // secret page gpa
    pub hv_param: u64,            // param page gpa
    pub validated_entries: u64,
    pub acpi: u64,
    pub acpi_size: u64,
    pub richos_start: u64,
    pub richos_size: u64,
    pub richos_cmdline_len: u64,
}

impl MonitorParams {
    pub open spec fn e820(&self) -> Seq<E820Entry> {
        let e820 = self.validated_e820@;
        let n = self.validated_entries;
        e820.take(n.vspec_cast_to())
    }

    pub open spec fn mp_wf(&self) -> bool {
        &&& self.validated_entries <= self.validated_e820@.len()
        &&& (self.acpi@.val as int).spec_valid_addr_with(self.acpi_size@.val as nat)
        &&& (self.richos_start@.val  as int).spec_valid_addr_with(self.richos_size@.val as nat)
        &&& self.is_constant()
    }
}

verus! {

impl MonitorParams {
    pub fn check_valid(&self) -> (ret: bool)
        requires
            self.is_constant(),
        ensures
            ret == self.mp_wf(),
    {
        if (self.validated_entries.reveal_value() as usize) > self.validated_e820.len() {
            return false;
        }
        if !self.acpi.reveal_value().check_valid_addr(self.acpi_size.reveal_value()) {
            return false;
        }
        if !self.richos_start.reveal_value().check_valid_addr(self.richos_size.reveal_value()) {
            return false;
        }
        return true
    }
}

} // verus!
pub ghost struct MonitorParamPermsToData {
    pub mp: SnpPointsToBytes,
    pub hvparampage: SnpPointsToBytes,
    pub global_perms: MonitorParamGlobalPerms,
}

pub tracked struct MonitorParamPerms {
    pub mp: SnpPointsToRaw,
    pub hvparampage: SnpPointsToRaw,
    pub global_perms: MonitorParamGlobalPerms,
}

pub tracked struct MonitorParamGlobalPerms {
    pub cpuid: SnpPointsToRaw,
    pub secret: SnpPointsToRaw,
    pub richos: SnpPointsToRaw,
    pub acpi: Map<int, SnpPointsToRaw>,
}

pub open spec fn spec_is_default_page_perms(page_perms: Map<int, SnpPointsToRaw>, start_page: int, npages: nat) -> bool {
    forall |i| start_page <= i < (start_page + npages) ==>
        #[trigger]page_perms.contains_key(i) &&
        page_perms[i]@.wf_const_default((i.to_addr(), PAGE_SIZE as nat))
}

impl MonitorParamGlobalPerms {
    pub open spec fn wf_value(&self, mp_value: MonitorParams) -> bool {
        &&& mp_value.is_constant()
        &&& self.cpuid@.wf_const_default((mp_value.cpuid_page as int, PAGE_SIZE!() as nat))
        &&& self.richos@.wf_const_default((mp_value.richos_start as int, mp_value.richos_size as nat))
        &&& self.secret@.wf_secret_default((mp_value.secret_page as int, PAGE_SIZE!() as nat))
        &&& spec_is_default_page_perms(self.acpi, (mp_value.acpi as int)/PAGE_SIZE!(), (mp_value.acpi_size as nat)/(PAGE_SIZE!() as nat))
    }
}

impl MonitorParamPerms {
    pub open spec fn view(self) -> MonitorParamPermsToData{
        MonitorParamPermsToData {
            mp: self.mp@,
            hvparampage: self.hvparampage@,
            global_perms: self.global_perms,
        }
    }
}

impl MonitorParamPermsToData {
    pub open spec fn wf(&self) -> bool {
        &&& self.mp.wf_const_default(self.mp.range())
        &&& self.mp.size() === spec_size::<MonitorParams>()
        &&& self.wf_param_value()
    }

    pub open spec fn e820(&self) -> Seq<E820Entry> {
        let mp: SnpPointsToData<MonitorParams> = self.mp.vspec_cast_to();
        let mp_value = mp.value().get_Some_0();
        let e820 = mp_value.validated_e820@;
        let n = mp_value.validated_entries;
        e820.take(n.vspec_cast_to())
    }

    pub open spec fn wf_param_value(&self) -> bool {
        let mp: SnpPointsToData<MonitorParams> = self.mp.vspec_cast_to();
        let mp_value = mp.value().get_Some_0();
        let n = mp_value.validated_entries;
        &&& self.global_perms.wf_value(mp_value)
        &&& self.hvparampage.wf_const_default((mp_value.hv_param as int, PAGE_SIZE!() as nat))
    }

    pub open spec fn wf_at(&self, mp_ptr: SnpPPtr<MonitorParams>) -> bool {
        &&& self.mp.range() === (mp_ptr.range_id())
        &&& self.wf()
    }
}
}
