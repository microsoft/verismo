use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::resource::frac::FracGhost;

verus! {

#[verifier::external_body]
pub tracked struct VirtAddrPerm{
    no_copy: NoCopy,
}

#[verifier::external_body]
pub tracked struct PhysAddrPerm {
    no_copy: NoCopy,
}


#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub tracked struct PointsTo<T> {
    phantom: core::marker::PhantomData<T>,
    no_copy: NoCopy,
}

pub type AddressSpaceId = Loc;

pub enum MemType {
    Kernel,
    User(AddressSpaceId),
}

/// Verification-only pointer type, with a memory type tag.
pub struct OSPointer<T>(MemType, *mut T);

impl<T> OSPointer<T> {
    pub spec fn mem_type(&self) -> MemType {
        self.0
    }

    pub spec fn ptr(&self) -> *mut T {
        self.1
    }
}

pub ghost struct PointsToData<T> {
    // We may map multiple virtual addresses to the same physical address.
    pub ptr: Set<OSPointer<T>>,
    pub opt_value: MemContents<T>,
}

impl<T> View for PointsTo<T> {
    type V = PointsToData<T>;

    uninterp spec fn view(&self) -> Self::V;
}

impl<T> PointsTo<T> {
    pub proof fn tracked_add_virt_map(tracked &mut self, ghost ptr: OSPointer<T>, tracked cr3: &CpuState)
    {}
}

trait MMUModel<T> {
    spec fn mmu_page_table_entry_reachable(&self, value: T, next_value: T) -> bool;

    spec fn mmu_may_read(&self, value: T) -> bool;

    spec fn pt_root_pa(&self) -> int;

    spec fn entry_at<L: Level>(&self, vaddr: int, level: int) -> T;
}

struct PTPointsToState<T> {
    points_to: PointsTo<T>,
    value: FracGhost<T>, 
}

struct PTEntryConstant {
    paddr: int,
}

impl<T> InvariantPredicate for PTPointsToState<T> {
    spec fn inv(&self) -> bool {
        (self.points_to.value(), value@)
    }
}

struct PTPointsTo<T>{
    shared: FracGhost<AtomicInvariant<int, PTPointsToState<T>, PTPointsToState<T>>>,
    local: FracGhost<T>,
}

impl PTPointsTo {
    pub proof fn new() -> (pt: PTPointsTo)
        ensures
            pt@ == PTPointsToState::new(),
    {
        let inv = AtomicInvariant::new(PTPointsToState::new());
        PTPointsTo(inv)
    }
}
} // verus!
