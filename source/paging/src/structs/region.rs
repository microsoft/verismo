//! Mapping a region with the largest pages it can be made of.
//!
//! A caller that says "map these bytes there" should not have to say what page
//! size to use, and a caller that always says 4 KiB pays for it in entries and
//! in TLB pressure. This picks the size: the middle of the region is mapped
//! with `big` pages wherever both ends of a `big`-sized block lie inside it and
//! the physical address agrees with the virtual one about where those blocks
//! begin, and the pieces left over at either end are mapped with `small` ones.
//!
//! Three passes over the tree at most, and each is a `range_at`, so the work
//! per table page is still a loop over its slots rather than a walk per page.
use vstd::prelude::*;

use crate::structs::address::VirtAddr;
use crate::structs::arch_contract::{level_geometry_wf, ArchPagingMeta, GenericPageTableFlags};
use crate::structs::concurrent_pt::PTPageSharedPerm;
use crate::structs::geometry::shift_at;
use crate::structs::level::PageLevel;
use crate::structs::os_contract::{PagingError, PagingHandler};
use crate::structs::ptpage::PTPage;
use crate::structs::range::{level_flags, range_at, RangeOp};

verus! {

/// Maps `[vstart, vend)` to the physical range at `paddr`, using `big` pages
/// where the region allows and `small` ones elsewhere.
///
/// Fails, leaving what it has already written in place, on the first address
/// that already maps -- the same partial-failure behaviour a single ranged
/// pass has, for the same reason: undoing the writes would mean unmapping
/// addresses that another thread may have started using.
pub fn map_region<A: ArchPagingMeta, P: PagingHandler>(
    page_ptr: *mut PTPage<A>,
    level: PageLevel,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
    vstart: usize,
    vend: usize,
    paddr: usize,
    flags: A::PTFlags,
    big: PageLevel,
    small: PageLevel,
) -> (ret: Result<(), PagingError>)
    requires
        level_geometry_wf::<A>(),
        page.wf(),
        page.base == page_ptr@.addr,
        vstart <= vend,
        paddr + (vend - vstart) <= usize::MAX,
{
    let shift = shift_at::<A>(big);
    assert((1usize << shift) != 0) by (bit_vector)
        requires
            shift < 64,
    ;
    let size = 1usize << shift;
    let mask = sub(size, 1);
    let small_flags = level_flags::<A>(flags, small);
    let big_flags = level_flags::<A>(flags, big);
    let small_op = RangeOp::Map { paddr, flags: small_flags };
    if (vstart ^ paddr) & mask != 0 {
        // The two addresses do not agree on where a big block begins, so no
        // big page can map any part of this region.
        return range_at::<A, P>(page_ptr, level, Tracked(page), vstart, vend, small, small_op);
    }
    let head_end = block_start_after::<A>(vstart, vend, size, mask);
    let mid_end = block_start_at_or_before::<A>(head_end, vend, mask);
    match range_at::<A, P>(page_ptr, level, Tracked(page), vstart, head_end, small, small_op) {
        Err(e) => {
            return Err(e);
        },
        Ok(()) => {},
    }
    let mid_op = RangeOp::Map { paddr: paddr + (head_end - vstart), flags: big_flags };
    match range_at::<A, P>(page_ptr, level, Tracked(page), head_end, mid_end, big, mid_op) {
        Err(e) => {
            return Err(e);
        },
        Ok(()) => {},
    }
    let tail_op = RangeOp::Map { paddr: paddr + (mid_end - vstart), flags: small_flags };
    range_at::<A, P>(page_ptr, level, Tracked(page), mid_end, vend, small, tail_op)
}

/// Where the first whole block of `size` bytes inside `[vstart, vend)` begins,
/// or `vend` if the region holds none.
///
/// Rounding up can leave the address space, which is why this is a function
/// rather than an expression: at the very top of memory there is no next
/// block, and the answer is that the whole region is a leftover.
fn block_start_after<A: ArchPagingMeta>(
    vstart: usize,
    vend: usize,
    size: usize,
    mask: usize,
) -> (ret: usize)
    requires
        vstart <= vend,
        size == mask + 1,
    ensures
        vstart <= ret <= vend,
{
    let aligned = vstart & !mask;
    assert(vstart == (vstart & !mask) + (vstart & mask)) by (bit_vector);
    assert((vstart & mask) <= mask) by (bit_vector);
    if aligned == vstart {
        return vstart;
    }
    if aligned > usize::MAX - size {
        return vend;
    }
    let next = aligned + size;
    if next >= vend {
        vend
    } else {
        next
    }
}

/// Where the last whole block of `mask + 1` bytes ending at or before `vend`
/// begins, but never before `low`.
fn block_start_at_or_before<A: ArchPagingMeta>(low: usize, vend: usize, mask: usize) -> (ret: usize)
    requires
        low <= vend,
    ensures
        low <= ret <= vend,
{
    let aligned = vend & !mask;
    assert(vend & !mask <= vend) by (bit_vector);
    if aligned < low {
        low
    } else {
        aligned
    }
}

} // verus!
