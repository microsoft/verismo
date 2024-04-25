mod e820_fmt;
mod e820_init;
mod e820_init_alloc;
mod init_e;
mod init_s;
mod mshv_alloc;
mod mshv_fmt;
mod mshv_init;

pub use init_e::*;
pub use init_s::*;

use super::*;
use crate::addr_e::*;
use crate::boot::monitor_params::{
    MonitorParamPerms, MonitorParamPermsToData, MonitorParams, ValidatedE820Table,
    MAX_VALIDATED_E820,
};
use crate::boot::mshyper::*;
use crate::boot::params::*;
use crate::debug::{SlicePrinter, VEarlyPrintAtLevel, VPrint};
use crate::global::*;
use crate::mem::{RawMemPerms, SnpMemCoreConsole};
use crate::ptr::*;
use crate::registers::SnpCore;
use crate::snp::ghcb::*;
use crate::snp::SnpCoreConsole;
use crate::tspec::*;
use crate::tspec_e::*;
use crate::*;

def_asm_addr_for! {bootstack = boot_stack}
def_asm_addr_for! {bootstack_end = boot_stack_end}
def_asm_addr_for! {verismo_start_addr = verismo_start}
def_asm_addr_for! {verismo_end_addr = _monitor_end}
def_asm_addr_for! {ap_entry_addr = ap_entry}
