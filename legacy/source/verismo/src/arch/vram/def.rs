use verismo_macro::*;

use crate::arch::addr_s::SPN;
use crate::arch::ramdb::RamDB;
use crate::arch::rmp::RmpEntry;
use crate::tspec::*;

verus! {

/// SEV-SNP only prevents software-based integrity attack.
/// Active DRAM corruption is not resolved.
///
/// There is no actually integrity check in hardware (integrity_check = false).
/// The integrity is achieved by restricting the HV's access to private memory;
/// We may prove that the when the attacker cannot physically replace memory,
/// the RMP enforcement with integrity_check = false achieves the equivalent result with integrity_check = true.
#[derive(SpecSetter, SpecGetter)]
pub struct VRamDB {
    pub sram: RamDB,
    pub rmp: Map<SPN, RmpEntry>,
}

} // verus!
