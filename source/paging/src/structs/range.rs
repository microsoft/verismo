//! Ranged operations: one pass over the tree for a whole range of addresses.
//!
//! Mapping a range one address at a time would walk from the root for every
//! page and take the leaf page's lock once per entry. Here the recursion
//! descends once per table page that the range touches, and at the level the
//! mapping is installed at, the page's lock is taken once for all the entries
//! of that page the range covers. That is the whole optimisation: the work per
//! page becomes a loop over entries rather than a walk.
//!
//! The range is cut at the boundaries of what each entry covers, so a recursive
//! call always gets a range that lies inside the page it is given -- which is
//! what makes the loop at the bottom a loop over that page's own slots.
//!
//! A range whose ends fall inside a larger mapping is handled by splitting it
//! (`structs::split`), but only when it really has to be: an entry the range
//! covers whole is changed where it stands, so unmapping a region built out of
//! huge pages does not take the tree apart and put it back together.
use concurrent_rw::{RWContract, RWWithPublishPayloadContract};
use vstd::prelude::*;

use crate::structs::address::lemma_phys_addr_from_bits;
use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{level_geometry_wf, ArchPagingMeta, GenericPageTableFlags};
use crate::structs::concurrent_pt::{PTPageSharedPerm, PTPageWritePerm};
use crate::structs::entry::PTEntry;
use crate::structs::geometry::{entry_index_bits, shift_at};
use crate::structs::level::PageLevel;
use crate::structs::map::create_and_link_child;
use crate::structs::os_contract::{PageLock, PagingError, PagingHandler};
use crate::structs::slot::slot_ptr;
use crate::structs::split::split_huge_at;
use crate::structs::update::{replace_leaf_slot, set_leaf_slot};

verus! {

/// What a ranged pass does to each entry it reaches at the target level.
#[derive(Clone, Copy)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum RangeOp<A: ArchPagingMeta> {
    /// Install a mapping of the contiguous physical range starting at `paddr`,
    /// failing if anything in the range already maps.
    Map { paddr: usize, flags: A::PTFlags },
    /// Clear every mapping in the range. Absent entries are left alone: a
    /// caller unmapping a region does not have to know which parts of it were
    /// mapped.
    Unmap,
    /// Replace the permissions of every mapping in the range, keeping frames.
    Protect { flags: A::PTFlags },
}

impl<A: ArchPagingMeta> RangeOp<A> {
    /// Whether reaching an entry that is not a table is an error rather than
    /// something to skip.
    ///
    /// Only mapping needs to grow the tree, so only mapping treats a missing
    /// table as work to do; the other two have nothing to do in a subtree that
    /// does not exist.
    pub open spec fn spec_creates(&self) -> bool {
        self is Map
    }

    #[verifier::when_used_as_spec(spec_creates)]
    pub fn creates(&self) -> (ret: bool)
        returns
            self.spec_creates(),
    {
        match self {
            RangeOp::Map { .. } => true,
            _ => false,
        }
    }
}

/// Applies `op` to every entry of `[vstart, vend)` at `target`, descending once
/// per table page the range touches.
///
/// `vstart` and `vend` are byte addresses, half-open. `base` is the page the
/// pass is currently in, and the range is always inside what that page covers,
/// which is what makes the loop below a loop over this page's slots.
pub fn range_at<A: ArchPagingMeta, H: PagingHandler>(
    base: VirtAddr,
    level: PageLevel,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
    vstart: usize,
    vend: usize,
    target: PageLevel,
    op: RangeOp<A>,
) -> (ret: Result<(), PagingError>)
    requires
        level_geometry_wf::<A>(),
        page.wf(),
        page.base == base@,
        op matches RangeOp::Map { paddr, .. } ==> paddr + (vend - vstart) <= usize::MAX,
        vstart <= vend,
    decreases level.spec_depth(), 1nat,
{
    if level.depth() == target.depth() {
        return leaf_range::<A, H>(base, level, Tracked(page), vstart, vend, op);
    }
    let shift = shift_at::<A>(level);
    assert((1usize << shift) != 0) by (bit_vector)
        requires
            shift < 64,
    ;
    let mask = sub(1usize << shift, 1);
    let mut cur = vstart;
    while cur < vend
        invariant
            level_geometry_wf::<A>(),
            page.wf(),
            page.base == base@,
            vstart <= cur,
            op matches RangeOp::Map { paddr, .. } ==> paddr + (vend - vstart) <= usize::MAX,
        decreases vend - cur,
    {
        let next = range_end(cur, vend, mask);
        let index = entry_index_bits::<A>(cur, level);
        match range_step::<A, H>(base, index, level, Tracked(page), cur, next, target, op) {
            Err(e) => {
                return Err(e);
            },
            Ok(()) => {},
        }
        cur = next;
    }
    Ok(())
}

/// One entry's worth of a ranged pass: descend into the child that covers
/// `[cur, next)`, creating it if the operation is one that grows the tree.
fn range_step<A: ArchPagingMeta, H: PagingHandler>(
    base: VirtAddr,
    index: usize,
    level: PageLevel,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
    cur: usize,
    next: usize,
    target: PageLevel,
    op: RangeOp<A>,
) -> (ret: Result<(), PagingError>)
    requires
        level_geometry_wf::<A>(),
        page.wf(),
        page.base == base@,
        index < PTEntry::<A>::count_per_page(),
        cur <= next,
        op matches RangeOp::Map { paddr, .. } ==> paddr + (next - cur) <= usize::MAX,
    decreases level.spec_depth(), 0nat,
{
    let child_level = match level.child() {
        None => {
            return Err(PagingError::InvalidLevel);
        },
        Some(child_level) => child_level,
    };
    let ptr = slot_ptr::<A>(base, index, Tracked(page));
    let tracked slot = page.slots.tracked_borrow(index as int);
    let (current, Tracked(_observed), Tracked(ticket)) = PTEntry::<A>::read_published(
        ptr,
        Tracked(slot),
        Tracked(None),
    );
    if current.is_table() {
        let tracked slot_ticket;
        let tracked child_page;
        proof {
            slot_ticket = ticket.tracked_unwrap();
            child_page = slot.borrow_published_payload(&slot_ticket).tracked_borrow();
            lemma_phys_addr_from_bits(current.page_frame_spec());
        }
        let child_base = H::paddr_to_vaddr::<A>(PhysAddr::from(current.page_frame()));
        return range_at::<A, H>(
            child_base,
            child_level,
            Tracked(child_page),
            cur,
            next,
            target,
            op,
        );
    }
    if current.present() {
        if op.creates() {
            // A mapping larger than the target already covers part of what the
            // caller asked to map; replacing it silently would strand it.
            return Err(PagingError::EntryAlreadyPresent);
        }
        let shift = shift_at::<A>(level);
        assert((1usize << shift) != 0) by (bit_vector)
            requires
                shift < 64,
        ;
        let mask = sub(1usize << shift, 1);
        if cur & mask == 0 && cur < next && sub(next, 1) == cur | mask {
            // The range covers this entry whole, so it can be changed where it
            // is -- no need to break it into pieces only to change all of them.
            let lock = H::page_lock(base);
            let Tracked(mut writers) = lock.lock::<A>(Tracked(page));
            let ret = leaf_step::<A>(base, index, Tracked(page), Tracked(&mut writers), 0, op);
            lock.unlock::<A>(Tracked(page), Tracked(writers));
            return ret;
        }
        // Only part of what this entry maps is in the range, so it has to
        // become a table before the parts can be told apart.

        let (child_base, child_ticket) = match split_huge_at::<A, H>(
            base,
            index,
            Tracked(page),
            child_level,
        ) {
            Err(e) => {
                return Err(e);
            },
            Ok(split) => split,
        };
        let tracked child_page = slot.borrow_published_payload(
            child_ticket.borrow(),
        ).tracked_borrow();
        return range_at::<A, H>(
            child_base,
            child_level,
            Tracked(child_page),
            cur,
            next,
            target,
            op,
        );
    }
    if !op.creates() {
        // Nothing is mapped here, and this operation only changes what is.
        return Ok(());
    }
    let (child_base, child_ticket) = match create_and_link_child::<A, H>(
        base,
        index,
        Tracked(page),
        child_level,
    ) {
        Err(e) => {
            return Err(e);
        },
        Ok(linked) => linked,
    };
    let tracked child_page = slot.borrow_published_payload(child_ticket.borrow()).tracked_borrow();
    range_at::<A, H>(child_base, child_level, Tracked(child_page), cur, next, target, op)
}

/// The entries of one table page that a range covers, under one acquisition of
/// that page's lock.
fn leaf_range<A: ArchPagingMeta, H: PagingHandler>(
    base: VirtAddr,
    level: PageLevel,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
    vstart: usize,
    vend: usize,
    op: RangeOp<A>,
) -> (ret: Result<(), PagingError>)
    requires
        level_geometry_wf::<A>(),
        page.wf(),
        page.base == base@,
        vstart <= vend,
        op matches RangeOp::Map { paddr, .. } ==> paddr + (vend - vstart) <= usize::MAX,
{
    let shift = shift_at::<A>(level);
    assert((1usize << shift) != 0) by (bit_vector)
        requires
            shift < 64,
    ;
    let mask = sub(1usize << shift, 1);
    let lock = H::page_lock(base);
    let Tracked(mut writers) = lock.lock::<A>(Tracked(page));
    let mut cur = vstart;
    let mut result = Ok(());
    while cur < vend
        invariant
            level_geometry_wf::<A>(),
            page.wf(),
            page.base == base@,
            vstart <= cur,
            writers.ids() =~= page.ids(),
            op matches RangeOp::Map { paddr, .. } ==> paddr + (vend - vstart) <= usize::MAX,
        decreases vend - cur,
    {
        let next = range_end(cur, vend, mask);
        let index = entry_index_bits::<A>(cur, level);
        let step = leaf_step::<A>(
            base,
            index,
            Tracked(page),
            Tracked(&mut writers),
            cur - vstart,
            op,
        );
        match step {
            Err(e) => {
                result = Err(e);
                break;
            },
            Ok(()) => {},
        }
        cur = next;
    }
    lock.unlock::<A>(Tracked(page), Tracked(writers));
    result
}

/// One entry of a ranged pass at the target level, with the page's writers
/// already in hand.
fn leaf_step<A: ArchPagingMeta>(
    base: VirtAddr,
    index: usize,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
    Tracked(writers): Tracked<&mut PTPageWritePerm<A>>,
    offset: usize,
    op: RangeOp<A>,
) -> (ret: Result<(), PagingError>)
    requires
        page.wf(),
        page.base == base@,
        old(writers).ids() =~= page.ids(),
        index < PTEntry::<A>::count_per_page(),
        op matches RangeOp::Map { paddr, .. } ==> paddr + offset <= usize::MAX,
    ensures
        final(writers).ids() =~= page.ids(),
{
    match op {
        RangeOp::Map { paddr, flags } => {
            let entry = leaf_entry::<A>(paddr + offset, flags);
            set_leaf_slot::<A>(base, index, Tracked(page), Tracked(writers), entry)
        },
        RangeOp::Unmap => {
            match replace_leaf_slot::<A>(
                base,
                index,
                Tracked(page),
                Tracked(writers),
                PTEntry::<A>::empty(),
            ) {
                Err(e) => Err(e),
                Ok(_) => Ok(()),
            }
        },
        RangeOp::Protect { flags } => {
            proof {
                crate::structs::concurrent_pt::lemma_ids_match::<A>(*writers, *page);
            }
            let ptr = slot_ptr::<A>(base, index, Tracked(page));
            let tracked reader = page.slots.tracked_borrow(index as int);
            let tracked writer = writers.slots.tracked_borrow(index as int);
            let (current, Tracked(_observed)) = PTEntry::<A>::read_exact(
                ptr,
                Tracked(reader),
                Tracked(writer),
            );
            if !current.present() {
                return Ok(());
            }
            let entry = leaf_entry::<A>(current.paddr_field(), flags);
            match replace_leaf_slot::<A>(base, index, Tracked(page), Tracked(writers), entry) {
                Err(e) => Err(e),
                Ok(_) => Ok(()),
            }
        },
    }
}

/// A leaf entry for `paddr`, keeping only the bits an entry can hold.
///
/// Masking rather than requiring an aligned address: the bits dropped are the
/// ones the hardware would not read anyway, and both tags live inside the
/// address field, so a tagged address survives.
pub fn leaf_entry<A: ArchPagingMeta>(paddr: usize, flags: A::PTFlags) -> (ret: PTEntry<A>)
    ensures
        !ret.is_table_spec(),
{
    let masked = paddr & A::address_mask();
    proof {
        let am = A::spec_address_mask();
        lemma_phys_addr_from_bits(paddr & am);
        assert((paddr & am) & !am == 0) by (bit_vector);
    }
    PTEntry::<A>::new_leaf(PhysAddr::from(masked), flags)
}

/// `flags` as an entry at `target` must carry them.
///
/// The size bit says "this entry maps a page" at every level but the leaf,
/// where the hardware reads it as PAT instead; so it is set or cleared here
/// rather than left to the caller, who would have to know that.
pub fn level_flags<A: ArchPagingMeta>(flags: A::PTFlags, target: PageLevel) -> (ret: A::PTFlags) {
    if target.is_leaf() {
        flags.without(A::PTFlags::HUGE)
    } else {
        flags.with(A::PTFlags::HUGE)
    }
}

/// Where the entry containing `cur` stops: the next boundary of a block of
/// `mask + 1` bytes, or `vend`, whichever comes first.
///
/// Computed as `cur | mask` -- the last byte of the block -- so that a range
/// reaching the top of the address space cannot overflow.
fn range_end(cur: usize, vend: usize, mask: usize) -> (ret: usize)
    requires
        cur < vend,
    ensures
        cur < ret <= vend,
{
    let last = cur | mask;
    assert(cur <= cur | mask) by (bit_vector);
    if last >= vend - 1 {
        vend
    } else {
        last + 1
    }
}

} // verus!
