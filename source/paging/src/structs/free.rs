//! Taking a page table apart.
//!
//! This is the operation the outer level of exclusion exists for. Everything
//! else here runs under `&self` and may overlap; freeing interior pages must
//! not, because a walker standing in a page that is being handed back to the
//! allocator would be reading freed memory. `&mut` on the handle is what rules
//! that out, and the tokens make it more than a convention: a page's readers
//! are consumed here, so no walk can be holding one.
//!
//! The tree is taken apart bottom-up. Tearing down a slot returns the tokens
//! escrowed in it -- the child page's readers -- and the child's writers come
//! back out of the child's own lock, which is where they were deposited when
//! the page was linked. With both halves in hand the page becomes plain
//! ownership of a frame again, and goes back to the allocator.
use concurrent_rw::{RWContract, WithPayload, WritePerm};
use vstd::prelude::*;
use vstd::raw_ptr::{with_exposed_provenance, IsExposed, PointsTo};

use crate::structs::address::lemma_phys_addr_from_bits;
use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{level_geometry_wf, slot_addr, ArchPagingMeta};
use crate::structs::concurrent_pt::{lemma_ids_match, PTPageSharedPerm, PTPageWritePerm};
use crate::structs::entry::PTEntry;
use crate::structs::level::PageLevel;
use crate::structs::os_contract::{PTPageInit, PageLock, OSPagingContract, SlotShared};
use crate::structs::ptpage::{page_from_vaddr, PTPage};

verus! {

/// Frees every table page below `page_ptr`, and returns its own frame as
/// plain ownership.
///
/// The page this is called on is *not* handed back: whoever knows its physical
/// address deallocates it, which for a child is the recursive step below and
/// for the root is the caller of [`GenericPageTable::free`].
///
/// `level` bounds the descent; it is not read off the pages, so a page whose
/// entries claim to point at tables below the leaf level is simply not
/// followed. Nothing this crate writes produces one.
pub fn free_page_tree<A: ArchPagingMeta, P: OSPagingContract<A>>(
    page_ptr: *mut PTPage<A>,
    level: PageLevel,
    Tracked(page): Tracked<PTPageSharedPerm<A>>,
    Tracked(writers): Tracked<PTPageWritePerm<A>>,
) -> (ret: Tracked<PTPageInit<A>>)
    requires
        level_geometry_wf::<A>(),
        page.wf(),
        page.base == page_ptr@.addr,
        writers.ids() =~= page.ids(),
    ensures
        ret@.wf_owned(),
        ret@.base == page.base,
    decreases level.spec_depth(), PTPage::<A>::count() + 1,
{
    proof {
        lemma_ids_match::<A>(writers, page);
    }
    let count = A::entries_per_page();
    let tracked PTPageSharedPerm { slots: readers, provenance, base: page_base, level: _ } =
        page;
    let tracked PTPageWritePerm { slots: writer_slots } = writers;
    let Tracked(points) = free_slots::<A, P>(
        page_ptr,
        level,
        count,
        Tracked(&provenance),
        Tracked(readers),
        Tracked(writer_slots),
    );
    Tracked(
        PTPageInit { base: page_base, provenance, slots: points, arch: core::marker::PhantomData },
    )
}

/// Tears down the last `count` slots of a page, freeing whatever they point at.
///
/// Written as a recursion rather than a loop so that the sequences it consumes
/// stay prefixes of the originals -- the same shape as `build_slots`, which it
/// undoes. The recursive call comes first so that the words come back in index
/// order.
fn free_slots<A: ArchPagingMeta, P: OSPagingContract<A>>(
    page_ptr: *mut PTPage<A>,
    level: PageLevel,
    count: usize,
    Tracked(provenance): Tracked<&IsExposed>,
    Tracked(readers): Tracked<Seq<SlotShared<A>>>,
    Tracked(writers): Tracked<Seq<WritePerm<PTEntry<A>>>>,
) -> (ret: Tracked<Seq<PointsTo<usize>>>)
    requires
        level_geometry_wf::<A>(),
        count == readers.len(),
        readers.len() == writers.len(),
        forall|i: int|
            0 <= i < readers.len() ==> {
                &&& (#[trigger] readers[i]).location()@.addr == slot_addr::<A>(page_ptr@.addr, i)
                &&& readers[i].location()@.provenance == provenance@
                &&& readers[i].id() == writers[i].id()
            },
    ensures
        ret@.len() == count,
        forall|i: int|
            0 <= i < ret@.len() ==> {
                &&& (#[trigger] ret@[i]).ptr()@.addr == slot_addr::<A>(page_ptr@.addr, i)
                &&& ret@[i].ptr()@.provenance == provenance@
                &&& ret@[i].is_init()
            },
    decreases level.spec_depth(), count,
{
    if count == 0 {
        return Tracked(Seq::tracked_empty());
    }
    let index = count - 1;
    let ghost i = index as int;
    let tracked mut readers = readers;
    let tracked mut writers = writers;
    let tracked reader = readers.tracked_pop();
    let tracked writer = writers.tracked_pop();
    let Tracked(mut points) = free_slots::<A, P>(
        page_ptr,
        level,
        index,
        Tracked(provenance),
        Tracked(readers),
        Tracked(writers),
    );
    let ptr = with_exposed_provenance(
        page_ptr.addr() + index * core::mem::size_of::<usize>(),
        Tracked(*provenance),
    );
    let (entry, Tracked(_observed)) = PTEntry::<A>::read_exact(
        ptr,
        Tracked(&reader),
        Tracked(&writer),
    );
    let tracked (word, payload) = PTEntry::<A>::teardown_rw(reader, writer);
    free_child::<A, P>(level, entry, Tracked(payload));
    proof {
        points.tracked_push(word);
    }
    Tracked(points)
}

/// Frees the page a torn-down entry pointed at, if it pointed at one.
///
/// The child's writers come out of the child's lock: that is where they were
/// left when the page was linked, and taking them back is what says no other
/// thread is in the middle of an update to it.
fn free_child<A: ArchPagingMeta, P: OSPagingContract<A>>(
    level: PageLevel,
    entry: PTEntry<A>,
    Tracked(payload): Tracked<Option<PTPageSharedPerm<A>>>,
)
    requires
        level_geometry_wf::<A>(),
        entry.wf_payload(payload),
    decreases level.spec_depth(), 0nat,
{
    if !entry.escrows() {
        return;
    }
    let child_level = match level.child() {
        None => {
            return;
        },
        Some(child_level) => child_level,
    };
    proof {
        lemma_phys_addr_from_bits(entry.page_frame_spec());
    }
    let paddr = PhysAddr::from(entry.page_frame());
    let child_base = P::paddr_to_vaddr(paddr);
    let tracked child = payload.tracked_unwrap();
    let child_ptr = page_from_vaddr::<A>(child_base, Tracked(&child));
    let child_lock = P::page_lock(child_ptr);
    let Tracked(child_writers) = child_lock.lock::<A>(Tracked(&child));
    let init = free_page_tree::<A, P>(
        child_ptr,
        child_level,
        Tracked(child),
        Tracked(child_writers),
    );
    P::deallocate_table_page(paddr, init);
}

} // verus!
