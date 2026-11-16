//! CPU-local root-register bindings, separate from tree lifecycle and ownership.
use core::fmt;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::Deref;

use super::PageTable;
use crate::address::PhysAddr;
use crate::structs::{
    ArchPagingMeta, KernelPolicy, LevelSpec, PagingAllocator, PagingError, PagingOwnershipPolicy,
    WalkLevel,
};

/// Architecture operations for installing a paging root on the current CPU.
///
/// # Safety
/// A successful load must install exactly `root` at `L::LEVEL`. Reads must return
/// the clean physical root, without register flags or confidentiality tags.
/// An error must leave the register unchanged. Loads must order preceding
/// page-table writes before hardware uses the new root. Register operations
/// must not change a different CPU's register.
pub unsafe trait RootRegisterAccess: ArchPagingMeta {
    /// # Safety
    /// Paging must be enabled. The caller must have register-access privileges
    /// and remain on this CPU.
    unsafe fn read_root_pa() -> PhysAddr;

    /// # Safety
    /// The caller must satisfy the architecture's root-register preconditions,
    /// keep the required execution and allocator mappings accessible after the
    /// switch, and establish valid retained translations or invalidate them.
    /// `flags` must contain valid architecture-specific register flags, not
    /// address bits; implementations need not validate them.
    /// The current hardware paging mode must support `L::LEVEL` and the table's
    /// page size; implementations need not check the mode.
    unsafe fn store_root_pa<L: LevelSpec>(root: PhysAddr, flags: usize) -> Result<(), PagingError>;
}

/// Why activation or a CPU-local switch was rejected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActivationFailure {
    Paging(PagingError),
    /// The current CPU has a different physical root.
    NotCurrent,
}

/// A rejected operation, retaining all resources supplied by the caller.
pub struct ActivationError<T> {
    pub error: ActivationFailure,
    pub resources: T,
}

impl<T> fmt::Debug for ActivationError<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ActivationError")
            .field("error", &self.error)
            .finish_non_exhaustive()
    }
}

/// Owns a table bound to the current CPU's root register.
///
/// Shared-receiver updates remain available, but exclusive cleanup is not.
/// Dropping or forgetting this handle retains its table allocations and borrowed
/// shares; it neither restores a previous root nor reclaims an active table.
/// The handle is neither `Send` nor `Sync`. CPU affinity and privileged register
/// access remain the caller's responsibility.
/// Binding identity is the clean root address, not PCID or cache-control fields.
///
/// ```compile_fail
/// use paging::{
///     pagetable::{ActivePageTable, PageTable, RootRegisterAccess},
///     structs::{PagingAllocator, PagingOwnershipPolicy, WalkLevel},
/// };
///
/// fn exclusive<A, P, L, S>(active: &mut ActivePageTable<A, P, L, S>)
/// where A: RootRegisterAccess, P: PagingAllocator, L: WalkLevel, S: PagingOwnershipPolicy
/// {
///     let _: &mut PageTable<A, P, L, S> = &mut **active;
/// }
/// ```
///
/// ```compile_fail
/// use paging::{
///     pagetable::{ActivePageTable, RootRegisterAccess},
///     structs::{PagingAllocator, PagingOwnershipPolicy, WalkLevel},
/// };
///
/// fn requires_send<T: Send>(_: T) {}
/// fn migrate<A, P, L, S>(active: ActivePageTable<A, P, L, S>)
/// where A: RootRegisterAccess + Send,
///       P: PagingAllocator + Send, L: WalkLevel + Send, S: PagingOwnershipPolicy + Send
/// {
///     requires_send(active);
/// }
/// ```
///
/// ```compile_fail
/// use paging::{
///     pagetable::{ActivePageTable, RootRegisterAccess},
///     structs::{PagingAllocator, PagingOwnershipPolicy, WalkLevel},
/// };
///
/// fn requires_sync<T: Sync>(_: &T) {}
/// fn share_binding<A, P, L, S>(active: &ActivePageTable<A, P, L, S>)
/// where A: RootRegisterAccess + Sync,
///       P: PagingAllocator + Sync, L: WalkLevel + Sync, S: PagingOwnershipPolicy + Sync
/// {
///     requires_sync(active);
/// }
/// ```
#[must_use = "switch away explicitly or retain the hardware-active table"]
pub struct ActivePageTable<
    A: RootRegisterAccess,
    P: PagingAllocator,
    L: WalkLevel,
    S: PagingOwnershipPolicy,
> {
    table: ManuallyDrop<PageTable<A, P, L, S>>,
    cpu: PhantomData<*mut ()>,
}

/// Owns a table switched out on one CPU, not necessarily quiesced globally.
///
/// Dropping or forgetting this handle retains its allocations and borrowed
/// shares. Recovering a reclaimable controller requires explicit hardware
/// quiescence; switching one CPU away is not that proof.
///
/// ```compile_fail
/// use paging::{
///     pagetable::{PageTable, RetiredPageTable},
///     structs::{ArchPagingMeta, PagingAllocator, PagingOwnershipPolicy, WalkLevel},
/// };
///
/// fn reclaim<A, P, L, S>(retired: RetiredPageTable<A, P, L, S>) -> PageTable<A, P, L, S>
/// where A: ArchPagingMeta, P: PagingAllocator, L: WalkLevel, S: PagingOwnershipPolicy
/// {
///     retired.into_page_table()
/// }
/// ```
#[must_use = "establish hardware quiescence before recovering the controller"]
pub struct RetiredPageTable<
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: WalkLevel,
    S: PagingOwnershipPolicy,
> {
    table: ManuallyDrop<PageTable<A, P, L, S>>,
}

pub type SwitchResult<A, P, L, S, Next> = Result<
    (ActivePageTable<A, P, L, Next>, RetiredPageTable<A, P, L, S>),
    ActivationError<(ActivePageTable<A, P, L, S>, PageTable<A, P, L, Next>)>,
>;

impl<A, P, L> ActivePageTable<A, P, L, KernelPolicy>
where
    A: RootRegisterAccess,
    P: PagingAllocator,
    L: WalkLevel,
{
    /// Adopts the current CPU's root without changing its register or flags.
    ///
    /// Validates the existing tree using [`PageTable::from_root`]. Failure or
    /// validation unwinding leaves the hardware-active tree allocated.
    ///
    /// # Safety
    /// Paging must already be enabled. Satisfy [`RootRegisterAccess::read_root_pa`]
    /// and [`PageTable::from_root`]'s preconditions for the current root and `L`.
    /// Transfer ownership of its
    /// allocator-allocated root and all descendant tables to this binding;
    /// no other usable controller or competing CPU-local binding may remain.
    /// Pin execution to this CPU and exclude interleaved root-register changes
    /// while constructing or operating on the binding. Other hardware users
    /// must be excluded before reclaiming any retired pages.
    pub unsafe fn from_current_cpu() -> Result<Self, PagingError> {
        // SAFETY: the caller supplies register privileges and pins this CPU.
        let root = unsafe { A::read_root_pa() };
        // SAFETY: the caller transfers the current tree's ownership and accessibility.
        let table = unsafe { PageTable::from_root(root) }?;
        Ok(Self { table: ManuallyDrop::new(table), cpu: PhantomData })
    }
}

impl<A, P, L, S> ActivePageTable<A, P, L, S>
where
    A: RootRegisterAccess,
    P: PagingAllocator,
    L: WalkLevel,
    S: PagingOwnershipPolicy,
{
    /// Retains this hardware-active table and returns its clean root address.
    pub fn leak(self) -> PhysAddr {
        self.table.root_paddr()
    }

    /// Replaces this CPU's root and retains the old controller for synchronization.
    ///
    /// Ownership policies may differ; switching does not alter either policy.
    /// Validates the target's self-mappings before installing its root.
    /// On failure, `resources` contains `(self, next)` without freeing either.
    /// Register-hook unwinding retains both roots because the hardware
    /// register's state may be unknown.
    ///
    /// # Safety
    /// Remain on the CPU that owns this binding and satisfy
    /// [`RootRegisterAccess::store_root_pa`]'s target register and mapping
    /// preconditions. Do not create competing bindings for this CPU.
    /// Do not supply a target whose destruction on validation unwinding could
    /// reclaim hardware-used pages.
    /// Exclude interrupt or scheduler paths that could interleave register writes.
    /// This operation does not establish quiescence of other CPUs, stale global
    /// translations, PCIDs, or hardware page walks using the old tree.
    pub unsafe fn switch_to<Next: PagingOwnershipPolicy>(
        self,
        next: PageTable<A, P, L, Next>,
        flags: usize,
    ) -> SwitchResult<A, P, L, S, Next> {
        // SAFETY: the caller pins execution and provides register privileges.
        if unsafe { A::read_root_pa() } != self.table.root_paddr() {
            return Err(ActivationError {
                error: ActivationFailure::NotCurrent,
                resources: (self, next),
            });
        }
        if let Err(error) = next.validate_page_table() {
            return Err(ActivationError {
                error: ActivationFailure::Paging(error),
                resources: (self, next),
            });
        }
        let next = ManuallyDrop::new(next);
        // SAFETY: the caller supplies the hardware, affinity and mapping preconditions.
        match unsafe { A::store_root_pa::<L>(next.root_paddr(), flags) } {
            Ok(()) => Ok((
                ActivePageTable { table: next, cpu: PhantomData },
                RetiredPageTable { table: self.table },
            )),
            Err(error) => Err(ActivationError {
                error: ActivationFailure::Paging(error),
                resources: (self, ManuallyDrop::into_inner(next)),
            }),
        }
    }
}

impl<A, P, L, S> RetiredPageTable<A, P, L, S>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: WalkLevel,
    S: PagingOwnershipPolicy,
{
    /// Retains this switched-out table and returns its clean root address.
    pub fn leak(self) -> PhysAddr {
        self.table.root_paddr()
    }

    /// Recovers the controller after hardware exclusion has been established.
    ///
    /// # Safety
    /// No CPU or other hardware user may still use this root or pages that its
    /// policy permits reclaiming. Complete the required TLB and paging-structure
    /// cache invalidation, including retained PCID and global entries, and
    /// exclude outstanding page walks before allowing cleanup or destruction.
    pub unsafe fn into_page_table(self) -> PageTable<A, P, L, S> {
        ManuallyDrop::into_inner(self.table)
    }
}

impl<A, P, L, S> Deref for ActivePageTable<A, P, L, S>
where
    A: RootRegisterAccess,
    P: PagingAllocator,
    L: WalkLevel,
    S: PagingOwnershipPolicy,
{
    type Target = PageTable<A, P, L, S>;

    fn deref(&self) -> &Self::Target {
        &self.table
    }
}

impl<A, P, L, S> Deref for RetiredPageTable<A, P, L, S>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: WalkLevel,
    S: PagingOwnershipPolicy,
{
    type Target = PageTable<A, P, L, S>;

    fn deref(&self) -> &Self::Target {
        &self.table
    }
}
