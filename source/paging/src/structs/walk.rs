//! Walking a page table without holding any lock.
//!
//! One function per level, each calling the one below it, so the depth of the
//! walk is fixed when the crate is compiled rather than bounded by a proof.
//! Kernel code pays for stack in a way that ordinary code does not, and five
//! named frames are easier to account for than a recursion a reader has to
//! check the `decreases` clause of.
//!
//! A loop would be better still -- constant stack rather than five frames --
//! but it does not typecheck. The permission for a child page is *borrowed*
//! out of the ticket the parent's slot handed back, and `RWShared` cannot be
//! duplicated, so every ancestor's ticket has to outlive the descent beneath
//! it. That is a nesting of borrows, and only nested calls provide it. The
//! borrows are all `tracked` and so cost nothing at runtime; what is nested is
//! the proof, not the machine state.
//!
//! The four inner levels are written out rather than generated. They differ
//! only in which level they are and which walker they call, but a macro would
//! hide four stack frames behind one expansion, and the count of frames is the
//! reason the file is shaped this way at all.
//!
//! Nothing here takes a lock. A slot is read through `concurrent_rw`, which
//! gives a reader an *observation* rather than the current value: what it says
//! about a slot holding a table pointer stays true (`entry_step`), and what it
//! says about anything else may already be stale. That is the honest reading of
//! a lock-free walk, and it is enough for a walk that only wants to find where
//! an address is mapped.
use builtin_macros::{verus, verus_spec, verus_verify};
use common_proofs::tracked;
use concurrent_rw::RWWithPublishPayloadContract;
use vstd::prelude::*;
use vstd::raw_ptr::with_exposed_provenance;

#[cfg(verus_only)]
use crate::structs::address::lemma_phys_addr_from_bits;
use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::ArchPagingMeta;
#[cfg(verus_only)]
use crate::structs::arch_contract::{level_geometry_wf, slot_addr, spec_entry_index};
use crate::structs::concurrent_pt::PTPageSharedPerm;
use crate::structs::entry::PTEntry;
use crate::structs::geometry::entry_index_at;
use crate::structs::level::PageLevel;
use crate::structs::os_contract::OSPagingContract;
use crate::structs::ptpage::{entry_ptr, page_from_vaddr, PTPage};

/// Where a walk came to rest: the entry it stopped at, and enough about the
/// page holding it to go back and update it.
///
/// `page_ptr` and `index` are what an update needs -- the page's lock is looked
/// up by the page, and the slot is written by index -- and `level` is what says
/// how large a page the entry maps.
#[verus_verify]
pub struct WalkResult<A: ArchPagingMeta> {
    pub level: PageLevel,
    pub page_ptr: *mut PTPage<A>,
    pub index: usize,
    pub entry: PTEntry<A>,
}

/// Where `vaddr` comes to rest in the tree rooted at `page_ptr`.
///
/// `top_level` says how tall the tree is, and so which of the per-level walkers
/// below is the way in.
#[verus_spec(ret =>
    requires
        level_geometry_wf::<A>(),
        page@.wf(),
        page@.base == page_ptr@.addr,
    ensures
        ret.level.depth() <= top_level.depth(),
        ret.index == spec_entry_index::<A>(vaddr@, ret.level),
        ret.entry.is_table_spec(ret.level) ==> !ret.entry.escrows_spec(),
)]
pub fn walk<A: ArchPagingMeta, P: OSPagingContract<A>>(
    page_ptr: *mut PTPage<A>,
    top_level: PageLevel,
    page: Tracked<&PTPageSharedPerm<A>>,
    vaddr: VirtAddr,
) -> WalkResult<A> {
    match top_level {
        PageLevel::Level0 => walk_level0::<A, P>(page_ptr, page, vaddr),
        PageLevel::Level1 => walk_level1::<A, P>(page_ptr, page, vaddr),
        PageLevel::Level2 => walk_level2::<A, P>(page_ptr, page, vaddr),
        PageLevel::Level3 => walk_level3::<A, P>(page_ptr, page, vaddr),
        PageLevel::Level4 => walk_level4::<A, P>(page_ptr, page, vaddr),
    }
}

/// The leaf: whatever is in the slot is where the walk ends, because at level 0
/// the bit that would say "points at a table" is read by the hardware as PAT.
#[verus_spec(ret =>
    requires
        level_geometry_wf::<A>(),
        page@.wf(),
        page@.base == page_ptr@.addr,
    ensures
        ret.level == PageLevel::Level0,
        ret.index == spec_entry_index::<A>(vaddr@, ret.level),
        ret.entry.is_table_spec(ret.level) ==> !ret.entry.escrows_spec(),
)]
pub fn walk_level0<A: ArchPagingMeta, P: OSPagingContract<A>>(
    page_ptr: *mut PTPage<A>,
    page: Tracked<&PTPageSharedPerm<A>>,
    vaddr: VirtAddr,
) -> WalkResult<A> {
    let level = PageLevel::at::<0>();
    let index = entry_index_at::<A, 0>(vaddr);
    let ptr = entry_ptr::<A>(page_ptr, index, page);
    let (entry, _observed, _ticket) = PTEntry::read_published(
        ptr,
        tracked!(page.get().slots.tracked_borrow(index as int)),
        tracked!(None),
        tracked!(&()),
    );
    proof! {
        PageLevel::lemma_no_child_is_leaf(level);
        assert(!entry.is_table_spec(level));
    }
    WalkResult { level, page_ptr, index, entry }
}

/// Walks from a level-1 page, descending into `walk_level0`.
///
/// The ticket the read hands back is what the child's permission is borrowed
/// out of, so it has to still be in scope at the call below: a helper that
/// returned the child's permission would not borrow-check.
#[verus_spec(ret =>
    requires
        level_geometry_wf::<A>(),
        page@.wf(),
        page@.base == page_ptr@.addr,
    ensures
        ret.level.depth() <= PageLevel::Level1.depth(),
        ret.index == spec_entry_index::<A>(vaddr@, ret.level),
        ret.entry.is_table_spec(ret.level) ==> !ret.entry.escrows_spec(),
)]
pub fn walk_level1<A: ArchPagingMeta, P: OSPagingContract<A>>(
    page_ptr: *mut PTPage<A>,
    page: Tracked<&PTPageSharedPerm<A>>,
    vaddr: VirtAddr,
) -> WalkResult<A> {
    let level = PageLevel::at::<1>();
    let index = entry_index_at::<A, 1>(vaddr);
    let ptr = entry_ptr::<A>(page_ptr, index, page);
    let (entry, _observed, ticket) = PTEntry::read_published(
        ptr,
        tracked!(page.get().slots.tracked_borrow(index as int)),
        tracked!(None),
        tracked!(&()),
    );
    if !entry.is_table(level) || !entry.escrows() {
        proof! { assert(entry.is_table_spec(level) ==> !entry.escrows_spec()); }
        return WalkResult { level, page_ptr, index, entry };
    }
    proof_decl! {
        // `is_table` is `has_published_payload`, so the read promised a ticket,
        // and the ticket names the child page's tokens.
        let tracked slot_ticket = ticket.get().tracked_unwrap();
        let tracked child_perm = page.get().slots.tracked_borrow(
            index as int,
        ).borrow_published_payload(&slot_ticket).tracked_borrow();
    }
    proof! { lemma_phys_addr_from_bits(entry.page_frame_spec()); }
    let child_base = P::paddr_to_vaddr(PhysAddr::from(entry.page_frame()));
    let child_page = tracked!(child_perm);
    let child_ptr = page_from_vaddr::<A>(child_base, child_page);
    walk_level0::<A, P>(child_ptr, child_page, vaddr)
}

/// Walks from a level-2 page, descending into `walk_level1`.
///
/// The ticket the read hands back is what the child's permission is borrowed
/// out of, so it has to still be in scope at the call below: a helper that
/// returned the child's permission would not borrow-check.
#[verus_spec(ret =>
    requires
        level_geometry_wf::<A>(),
        page@.wf(),
        page@.base == page_ptr@.addr,
    ensures
        ret.level.depth() <= PageLevel::Level2.depth(),
        ret.index == spec_entry_index::<A>(vaddr@, ret.level),
        ret.entry.is_table_spec(ret.level) ==> !ret.entry.escrows_spec(),
)]
pub fn walk_level2<A: ArchPagingMeta, P: OSPagingContract<A>>(
    page_ptr: *mut PTPage<A>,
    page: Tracked<&PTPageSharedPerm<A>>,
    vaddr: VirtAddr,
) -> WalkResult<A> {
    let level = PageLevel::at::<2>();
    let index = entry_index_at::<A, 2>(vaddr);
    let ptr = entry_ptr::<A>(page_ptr, index, page);
    let (entry, _observed, ticket) = PTEntry::read_published(
        ptr,
        tracked!(page.get().slots.tracked_borrow(index as int)),
        tracked!(None),
        tracked!(&()),
    );
    if !entry.is_table(level) || !entry.escrows() {
        proof! { assert(entry.is_table_spec(level) ==> !entry.escrows_spec()); }
        return WalkResult { level, page_ptr, index, entry };
    }
    proof_decl! {
        // `is_table` is `has_published_payload`, so the read promised a ticket,
        // and the ticket names the child page's tokens.
        let tracked slot_ticket = ticket.get().tracked_unwrap();
        let tracked child_perm = page.get().slots.tracked_borrow(
            index as int,
        ).borrow_published_payload(&slot_ticket).tracked_borrow();
    }
    proof! { lemma_phys_addr_from_bits(entry.page_frame_spec()); }
    let child_base = P::paddr_to_vaddr(PhysAddr::from(entry.page_frame()));
    let child_page = tracked!(child_perm);
    let child_ptr = page_from_vaddr::<A>(child_base, child_page);
    walk_level1::<A, P>(child_ptr, child_page, vaddr)
}

/// Walks from a level-3 page, descending into `walk_level2`.
///
/// The ticket the read hands back is what the child's permission is borrowed
/// out of, so it has to still be in scope at the call below: a helper that
/// returned the child's permission would not borrow-check.
#[verus_spec(ret =>
    requires
        level_geometry_wf::<A>(),
        page@.wf(),
        page@.base == page_ptr@.addr,
    ensures
        ret.level.depth() <= PageLevel::Level3.depth(),
        ret.index == spec_entry_index::<A>(vaddr@, ret.level),
        ret.entry.is_table_spec(ret.level) ==> !ret.entry.escrows_spec(),
)]
pub fn walk_level3<A: ArchPagingMeta, P: OSPagingContract<A>>(
    page_ptr: *mut PTPage<A>,
    page: Tracked<&PTPageSharedPerm<A>>,
    vaddr: VirtAddr,
) -> WalkResult<A> {
    let level = PageLevel::at::<3>();
    let index = entry_index_at::<A, 3>(vaddr);
    let ptr = entry_ptr::<A>(page_ptr, index, page);
    let (entry, _observed, ticket) = PTEntry::read_published(
        ptr,
        tracked!(page.get().slots.tracked_borrow(index as int)),
        tracked!(None),
        tracked!(&()),
    );
    if !entry.is_table(level) || !entry.escrows() {
        proof! { assert(entry.is_table_spec(level) ==> !entry.escrows_spec()); }
        return WalkResult { level, page_ptr, index, entry };
    }
    proof_decl! {
        // `is_table` is `has_published_payload`, so the read promised a ticket,
        // and the ticket names the child page's tokens.
        let tracked slot_ticket = ticket.get().tracked_unwrap();
        let tracked child_perm = page.get().slots.tracked_borrow(
            index as int,
        ).borrow_published_payload(&slot_ticket).tracked_borrow();
    }
    proof! { lemma_phys_addr_from_bits(entry.page_frame_spec()); }
    let child_base = P::paddr_to_vaddr(PhysAddr::from(entry.page_frame()));
    let child_page = tracked!(child_perm);
    let child_ptr = page_from_vaddr::<A>(child_base, child_page);
    walk_level2::<A, P>(child_ptr, child_page, vaddr)
}

/// Walks from a level-4 page, descending into `walk_level3`.
///
/// The ticket the read hands back is what the child's permission is borrowed
/// out of, so it has to still be in scope at the call below: a helper that
/// returned the child's permission would not borrow-check.
#[verus_spec(ret =>
    requires
        level_geometry_wf::<A>(),
        page@.wf(),
        page@.base == page_ptr@.addr,
    ensures
        ret.level.depth() <= PageLevel::Level4.depth(),
        ret.index == spec_entry_index::<A>(vaddr@, ret.level),
        ret.entry.is_table_spec(ret.level) ==> !ret.entry.escrows_spec(),
)]
pub fn walk_level4<A: ArchPagingMeta, P: OSPagingContract<A>>(
    page_ptr: *mut PTPage<A>,
    page: Tracked<&PTPageSharedPerm<A>>,
    vaddr: VirtAddr,
) -> WalkResult<A> {
    let level = PageLevel::at::<4>();
    let index = entry_index_at::<A, 4>(vaddr);
    let ptr = entry_ptr::<A>(page_ptr, index, page);
    let (entry, _observed, ticket) = PTEntry::read_published(
        ptr,
        tracked!(page.get().slots.tracked_borrow(index as int)),
        tracked!(None),
        tracked!(&()),
    );
    if !entry.is_table(level) || !entry.escrows() {
        proof! { assert(entry.is_table_spec(level) ==> !entry.escrows_spec()); }
        return WalkResult { level, page_ptr, index, entry };
    }
    proof_decl! {
        // `is_table` is `has_published_payload`, so the read promised a ticket,
        // and the ticket names the child page's tokens.
        let tracked slot_ticket = ticket.get().tracked_unwrap();
        let tracked child_perm = page.get().slots.tracked_borrow(
            index as int,
        ).borrow_published_payload(&slot_ticket).tracked_borrow();
    }
    proof! { lemma_phys_addr_from_bits(entry.page_frame_spec()); }
    let child_base = P::paddr_to_vaddr(PhysAddr::from(entry.page_frame()));
    let child_page = tracked!(child_perm);
    let child_ptr = page_from_vaddr::<A>(child_base, child_page);
    walk_level3::<A, P>(child_ptr, child_page, vaddr)
}
