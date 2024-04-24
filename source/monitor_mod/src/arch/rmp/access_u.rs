use super::*;
use crate::arch::rmp::perm_s::*;

verus! {

impl RmpEntry {
    pub open spec fn view(&self) -> HiddenRmpEntryForPSP {
        self.spec_val()
    }
}

impl RmpEntry {
    pub open spec fn inv(&self) -> bool {
        self@.is_valid()
    }
}

} // verus!
