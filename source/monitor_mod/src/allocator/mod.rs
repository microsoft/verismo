mod bit_p;
mod buddy;
mod buddy_new;
mod linkedlist;
mod locked;
mod trusted;

pub use bit_p::*;
pub use buddy::BuddyAllocator;
pub use buddy_new::new_array_linked_list32;
pub use linkedlist::LinkedListAllocator;
use verismo_macro::*;

pub use self::trusted::*;
use crate::ptr::*;
use crate::tspec::map_lib::tracked_seq_insert;
use crate::tspec::*;
use crate::tspec_e::*;
use crate::*;

// Choose different allocator type;
pub type VeriSMoAllocator = LinkedListAllocator;
use crate::lock::*;

verus! {

pub open spec fn alloc_valid_ptr(size: usize, ret: (usize, Tracked<SnpPointsToRaw>)) -> bool {
    &&& ret.1@@.wf_const_default((ret.0 as int, size as nat))
}

pub open spec fn talloc_valid_ptr(size: usize, ret: (usize, Tracked<SnpPointsToRaw>)) -> bool {
    &&& ret.1@@.wf_const_default((ret.0 as int, size as nat))
}

pub open spec fn valid_free_ptr(size: usize_t, ret: (usize_t, Tracked<SnpPointsToRaw>)) -> bool {
    &&& ret.1@@.wf_freemem((ret.0 as int, size as nat))
}

} // verus!
