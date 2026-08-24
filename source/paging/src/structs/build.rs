//! Turning a freshly allocated frame into the tokens of a table page.
//!
//! The allocator hands over plain ownership of the frame's words; a table page
//! is those words under the `concurrent_rw` protocol instead, one reader and
//! one writer per slot. The trade happens once, here, and it is a proof: no
//! instruction runs.
//!
//! It is written as a recursion rather than a loop because proof code cannot
//! loop, and it consumes the words from the end so that the sequence it is
//! left with is always a prefix of the original.
use concurrent_rw::{RWContract, WritePerm};
use vstd::prelude::*;
use vstd::raw_ptr::PointsTo;

use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlagsSpec};
use crate::structs::concurrent_pt::{PTPageSharedPerm, PTPageWritePerm};
use crate::structs::entry::PTEntry;
use crate::structs::level::PageLevel;
use crate::structs::os_contract::{PTPageInit, SlotShared};

verus! {

/// Trades each word of a zeroed frame for the reader and writer halves of one
/// slot.
///
/// The two sequences come back matched entry by entry: same pointer, same
/// protocol location, which is what makes the page's readers and the page's
/// writers two halves of one thing.
pub proof fn build_slots<A: ArchPagingMeta>(tracked points: Seq<PointsTo<usize>>) -> (tracked ret: (
    Seq<SlotShared<A>>,
    Seq<WritePerm<PTEntry<A>>>,
))
    requires
        forall|i: int|
            0 <= i < points.len() ==> (#[trigger] points[i]).is_init() && points[i].value()
                == 0usize,
    ensures
        ret.0.len() == points.len(),
        ret.1.len() == points.len(),
        forall|i: int|
            0 <= i < points.len() ==> (#[trigger] ret.0[i]).location() == points[i].ptr()
                && ret.0[i].id() == ret.1[i].id(),
    decreases points.len(),
{
    let tracked mut points = points;
    if points.len() == 0 {
        (Seq::tracked_empty(), Seq::tracked_empty())
    } else {
        let ghost last_index = points.len() - 1;
        let tracked last = points.tracked_pop();
        let tracked (mut readers, mut writers) = build_slots::<A>(points);
        let ghost value = PTEntry::<A>::spec_from_bits(0);
        lemma_zero_entry_is_not_a_table::<A>();
        crate::specs::entry::lemma_entry_from_usize::<A>(0);
        let tracked (r, w, _observed) = PTEntry::<A>::build_rw(value, last, None);
        readers.tracked_push(r);
        writers.tracked_push(w);
        (readers, writers)
    }
}

/// The word a fresh frame is filled with is not a table pointer, so a slot
/// built from it escrows nothing and publishes nothing.
pub proof fn lemma_zero_entry_is_not_a_table<A: ArchPagingMeta>()
    ensures
        !PTEntry::<A>::spec_from_bits(0).escrows_spec(),
        !PTEntry::<A>::spec_from_bits(0).present_spec(),
{
    PTEntry::<A>::lemma_view_of_bits(0);
    assert(0usize & A::PTFlags::spec_present_bit() == 0) by (bit_vector);
    assert(0usize & A::PTFlags::spec_escrow_bit() == 0) by (bit_vector);
}

impl<A: ArchPagingMeta> PTPageInit<A> {
    /// Turns the frame into a table page at `level`, mapping the frame `frame`.
    ///
    /// The writers come back beside the readers rather than going straight into
    /// a lock: whoever built the page holds the only writers, and so may fill
    /// it in before anyone else can reach it. Depositing them in the page's
    /// lock is the last step of publishing, and belongs to the caller.
    pub proof fn into_page(tracked self, level: PageLevel) -> (tracked ret: (
        PTPageSharedPerm<A>,
        PTPageWritePerm<A>,
    ))
        requires
            self.wf(),
        ensures
            ret.0.wf(),
            ret.0.base == self.base,
            ret.0.level == level,
            ret.1.ids() =~= ret.0.ids(),
    {
        let tracked PTPageInit { base, provenance, slots, arch } = self;
        let tracked (readers, writers) = build_slots::<A>(slots);
        let tracked page = PTPageSharedPerm { slots: readers, provenance, base, level };
        let tracked write = PTPageWritePerm { slots: writers };
        assert(page.ids() =~= write.ids());
        (page, write)
    }
}

} // verus!
