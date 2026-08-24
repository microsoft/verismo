//! Breaking one large mapping into a table of smaller ones.
//!
//! A ranged unmap or reprotect whose ends fall inside a huge page cannot do its
//! job entry by entry: the entry it reaches covers more than the caller asked
//! about. Splitting replaces that entry with a table whose entries reproduce it
//! exactly -- same frames, same permissions, one level finer -- after which the
//! ranged pass carries on in the ordinary way.
//!
//! The swap is invisible to every other thread: the child is complete before
//! the pointer to it is stored, so at no point does any address translate
//! differently, or fail to translate. That is why this is the one update
//! allowed to overwrite a present entry.
//!
//! The page is allocated before the parent's lock is taken, and given back if
//! the entry turns out not to need splitting after all, so the allocator is
//! never called with a page-table lock held.
use concurrent_rw::PayloadTicket;
use vstd::prelude::*;

use crate::structs::address::lemma_phys_addr_from_bits;
use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{level_geometry_wf, ArchPagingMeta, GenericPageTableFlags};
use crate::structs::concurrent_pt::{PTPageSharedPerm, PTPageWritePerm};
use crate::structs::entry::PTEntry;
use crate::structs::geometry::{lemma_count_per_page_positive, shift_at};
use crate::structs::level::PageLevel;
use crate::structs::os_contract::{PageLock, PagingError, OSPagingContract};
use crate::structs::ptpage::{entry_ptr, page_from_vaddr, PTPage};
use crate::structs::range::leaf_entry;

use crate::structs::update::{read_slot_exact, set_leaf_slot, split_leaf_slot};

verus! {

/// Replaces the mapping in slot `index` of `page_ptr` with a `child_level` table
/// that maps the same bytes the same way, and hands back the way into it.
///
/// Fails, harmlessly, if the slot does not hold a mapping: another thread may
/// have unmapped or already split it between the walk that found it and this
/// call, and in both cases the caller's next look at the slot tells it what to
/// do.
pub fn split_huge_at<A: ArchPagingMeta, P: OSPagingContract<A>>(
    page_ptr: *mut PTPage<A>,
    index: usize,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
    child_level: PageLevel,
) -> (ret: Result<
    (*mut PTPage<A>, Tracked<PayloadTicket<Option<PTPageSharedPerm<A>>>>),
    PagingError,
>)
    requires
        level_geometry_wf::<A>(),
        page.wf(),
        page.base == page_ptr@.addr,
        index < PTEntry::<A>::count_per_page(),
    ensures
        ret matches Ok((child_ptr, ticket)) ==> {
            &&& ticket@.id() == page.slots[index as int].slot_id()
            &&& ticket@.version() == page.slots[index as int].slot_version()
            &&& ticket@.payload() is Some
            &&& ticket@.payload()->Some_0.wf()
            &&& ticket@.payload()->Some_0.base == child_ptr@.addr
        },
{
    let (paddr, Tracked(init)) = match P::allocate_table_page() {
        Err(e) => {
            return Err(e);
        },
        Ok(allocated) => allocated,
    };
    let child_base = P::paddr_to_vaddr(paddr);
    let lock = P::page_lock(page_ptr);
    let Tracked(mut writers) = lock.lock::<A>(Tracked(page));
    proof {
        crate::structs::concurrent_pt::lemma_ids_match::<A>(writers, *page);
    }
    let ptr = entry_ptr::<A>(page_ptr, index, Tracked(page));
    let tracked reader = page.slots.tracked_borrow(index as int);
    let current = read_slot_exact::<A>(ptr, Tracked(reader), Tracked(&writers), index);
    if current.is_table() || !current.present() {
        lock.unlock::<A>(Tracked(page), Tracked(writers));
        P::deallocate_table_page(paddr, Tracked(init));
        return Err(PagingError::NotLeafEntry);
    }
    let tracked child_page;
    let tracked mut child_writers;
    proof {
        A::lemma_pte_masks_wf();
        let tracked (readers, ws) = init.into_page(paddr@, child_level);
        child_page = readers;
        child_writers = ws;
    }
    let child_ptr = page_from_vaddr::<A>(child_base, Tracked(&child_page));
    fill_split_page::<A>(
        child_ptr,
        Tracked(&child_page),
        Tracked(&mut child_writers),
        child_level,
        current,
    );
    let child_lock = P::page_lock(child_ptr);
    child_lock.deposit::<A>(Tracked(&child_page), Tracked(child_writers));

    let tagged = PhysAddr::from(paddr.bits() | A::private_pte_mask());
    proof {
        let am = A::spec_address_mask();
        let pm = A::spec_private_mask();
        let p = paddr@;
        lemma_phys_addr_from_bits(p | pm);
        assert((p & !am == 0 && pm & !am == 0) ==> (p | pm) & !am == 0) by (bit_vector);
        assert((p & pm == 0) ==> (p | pm) & !pm == p) by (bit_vector);
    }
    let table_entry = PTEntry::<A>::new_table(tagged, A::PTFlags::parent_flags());
    let linked = split_leaf_slot::<A>(
        page_ptr,
        index,
        Tracked(page),
        Tracked(&mut writers),
        table_entry,
        Tracked(child_page),
    );
    lock.unlock::<A>(Tracked(page), Tracked(writers));
    match linked {
        Err(e) => Err(e),
        Ok(ticket) => Ok((child_ptr, ticket)),
    }
}

/// Writes into a page that nobody else can see yet the entries that together
/// map exactly what `current` mapped.
///
/// The frame of piece `i` is the old frame plus `i` blocks of the child level's
/// size, which is an `or` rather than an addition because a mapping is aligned
/// to what it maps. The permissions carry over untouched, tag bits and all;
/// only the size bit is recomputed, since it says "maps a page" at every level
/// but the leaf, where the hardware reads that bit as something else entirely.
fn fill_split_page<A: ArchPagingMeta>(
    child_ptr: *mut PTPage<A>,
    Tracked(child): Tracked<&PTPageSharedPerm<A>>,
    Tracked(writers): Tracked<&mut PTPageWritePerm<A>>,
    child_level: PageLevel,
    current: PTEntry<A>,
)
    requires
        level_geometry_wf::<A>(),
        child.wf(),
        child.base == child_ptr@.addr,
        old(writers).ids() =~= child.ids(),
    ensures
        final(writers).ids() =~= child.ids(),
{
    let shift = shift_at::<A>(child_level);
    let flags = current.flags();
    let piece_flags = if child_level.is_leaf() {
        flags.without(A::PTFlags::HUGE)
    } else {
        flags.with(A::PTFlags::HUGE)
    };
    let frame = current.paddr_field();
    proof {
        lemma_count_per_page_positive::<A>();
    }
    let count = A::entries_per_page();
    let mut i = 0;
    while i < count
        invariant
            child.wf(),
            child.base == child_ptr@.addr,
            writers.ids() =~= child.ids(),
            count == PTEntry::<A>::count_per_page(),
            shift < 64,
            i <= count,
        decreases count - i,
    {
        let entry = leaf_entry::<A>(frame | (i << shift), piece_flags);
        let _ = set_leaf_slot::<A>(child_ptr, i, Tracked(child), Tracked(writers), entry);
        i = i + 1;
    }
}

} // verus!
