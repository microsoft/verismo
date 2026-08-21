//! The tracked state of a page table: what owning a table page means, and what
//! a slot promises to a reader that is walking without a lock.
//!
//! A slot is one aligned machine word shared between the hardware walker, any
//! number of software walkers, and one writer at a time. That is exactly the
//! multiple-reader/single-writer setting `concurrent_rw` models, so a slot is a
//! `RWShared` (shareable, what a walk needs) plus a `WritePerm` (exclusive,
//! what an update needs), and a table page is a map of those, one per entry.
//!
//! The reader half of a child page rides *inside* the parent slot as the
//! protocol's payload: publishing a table entry publishes the child's readers
//! with it, so a walker that reads a table entry may borrow the child's tokens
//! without taking a lock. `entry_step` is what makes that sound — a slot that
//! holds a table pointer keeps it — and it is this file's `RWModel::reachable`.
use core::marker::PhantomData;

use concurrent_rw::{
    IsValidAtomicType, PublishPayload, RWModel, RWShared, Snapshot, WithPayload, WritePerm,
};
use vstd::prelude::*;
use vstd::set_lib::set_int_range;
use vstd::raw_ptr::Provenance;
use vstd::resource::Loc;

use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::entry::{entry_step, PageTableEntry};
use crate::structs::host_contract::PagingHostAddr;
use crate::structs::level::{InteriorLevel, Level0, Level1, Level2, Level3, Level4, PagingLevel};

verus! {

/// The value of one slot of a level-`L` table page.
///
/// A newtype rather than a bare [`PageTableEntry`] because the protocol keys
/// everything on the value type: the level fixes which depth `entry_step` is
/// taken at, and the host fixes what the slot escrows.
pub struct Slot<A: ArchPagingMeta, H: PagingHostAddr, L: PagingLevel> {
    pub entry: PageTableEntry<A>,
    pub dummy: PhantomData<(H, L)>,
}

impl<A: ArchPagingMeta, H: PagingHostAddr, L: PagingLevel> Slot<A, H, L> {
    pub open spec fn depth() -> nat {
        L::DEPTH as nat
    }

    pub open spec fn is_table(self) -> bool {
        self.entry.is_table_spec(Self::depth())
    }

    /// The frame a table slot points at, with the architecture's tags stripped.
    pub open spec fn child_frame(self) -> usize {
        self.entry.page_frame_spec()
    }
}

/// What a slot at this level hands to a reader that follows it.
///
/// The leaf level escrows nothing: its entries map frames, which the page table
/// does not own. Every interior level escrows the reader half of the child
/// table page, so a walk can descend on a `&` borrow alone.
pub trait ChildOf<A: ArchPagingMeta, H: PagingHostAddr>: PagingLevel {
    type Escrow;

    spec fn escrow_wf(child_frame: usize, escrow: Self::Escrow) -> bool;
}

/// Everything a parent slot escrows about the child table page it points at:
/// the shared reader tokens for the child's slots, and the host receipt naming
/// the lock that keeps their writer halves.
pub tracked struct ChildPage<A: ArchPagingMeta, H: PagingHostAddr, L: PagingLevel + ChildOf<A, H>> {
    pub tracked readers: TableReaders<A, H, L>,
    pub tracked deposit: H::Deposit,
}

impl<A: ArchPagingMeta, H: PagingHostAddr, L: PagingLevel + ChildOf<A, H>> ChildPage<A, H, L> {
    /// The child tokens really describe the page `child_frame` names: the same
    /// virtual page the host translates that frame to, and slot identities the
    /// host lock agrees with.
    pub open spec fn wf(self, child_frame: usize) -> bool {
        &&& self.readers.wf()
        &&& self.readers.base == H::spec_paddr_to_vaddr(child_frame)
        &&& H::deposit_page(self.deposit) == self.readers.base
        &&& H::deposit_slot_ids(self.deposit) == self.readers.ids
    }
}

impl<A: ArchPagingMeta, H: PagingHostAddr> ChildOf<A, H> for Level0 {
    type Escrow = ();

    open spec fn escrow_wf(child_frame: usize, escrow: ()) -> bool {
        true
    }
}

} // verus!

/// Generates the interior-level escrow: a level-`$lv` slot escrows the reader
/// half of a level-`$lower` page.
macro_rules! interior_escrow {
    ($lv:ident, $lower:ident) => {
        verus! {
        impl<A: ArchPagingMeta, H: PagingHostAddr> ChildOf<A, H> for $lv {
            type Escrow = ChildPage<A, H, $lower>;

            open spec fn escrow_wf(child_frame: usize, escrow: ChildPage<A, H, $lower>) -> bool {
                escrow.wf(child_frame)
            }
        }
        }
    };
}

interior_escrow!(Level1, Level0);

interior_escrow!(Level2, Level1);

interior_escrow!(Level3, Level2);

interior_escrow!(Level4, Level3);

verus! {

impl<A: ArchPagingMeta, H: PagingHostAddr, L: PagingLevel + ChildOf<A, H>> WithPayload for Slot<
    A,
    H,
    L,
> {
    type Payload = <L as ChildOf<A, H>>::Escrow;

    open spec fn wf_payload(self, payload: Self::Payload) -> bool {
        self.is_table() ==> L::escrow_wf(self.child_frame(), payload)
    }
}

impl<A: ArchPagingMeta, H: PagingHostAddr, L: PagingLevel + ChildOf<A, H>> IsValidAtomicType for Slot<
    A,
    H,
    L,
> {
    type AtomicType = usize;

    open spec fn spec_to_atomic(self) -> usize {
        self.entry.view()
    }

    open spec fn spec_from_atomic(atomic: usize) -> Self {
        Slot { entry: PageTableEntry::spec_from_bits(atomic), dummy: PhantomData }
    }

    proof fn lemma_atomic_roundtrip(self) {
        PageTableEntry::<A>::lemma_bits_roundtrip(self.entry);
    }

    fn to_atomic(self) -> usize {
        self.entry.bits()
    }

    fn from_atomic(atomic: usize) -> Self {
        Slot { entry: PageTableEntry::from_bits(atomic), dummy: PhantomData }
    }
}

impl<A: ArchPagingMeta, H: PagingHostAddr, L: PagingLevel + ChildOf<A, H>> RWModel for Slot<A, H, L> {
    /// PIN, as the protocol states it: a reader that saw a table pointer may
    /// act on it later, because no writer may take it back.
    open spec fn reachable(
        pair: Snapshot<Self, Self::Payload>,
        other: Snapshot<Self, Self::Payload>,
    ) -> bool {
        entry_step(pair.value().entry, other.value().entry, Self::depth())
    }

    /// A table slot has published its child: that is what lets a walk borrow
    /// the child's readers outside the invariant block that produced them.
    open spec fn has_published_payload(self) -> bool {
        self.is_table()
    }

    proof fn reachable_self(pair: Snapshot<Self, Self::Payload>) {
    }

    proof fn reachable_transitive(
        a: Snapshot<Self, Self::Payload>,
        b: Snapshot<Self, Self::Payload>,
        c: Snapshot<Self, Self::Payload>,
    ) {
    }
}

impl<A: ArchPagingMeta, H: PagingHostAddr, L: PagingLevel + ChildOf<A, H>> PublishPayload for Slot<
    A,
    H,
    L,
> {
    proof fn payload_stays_published(
        pair: Snapshot<Self, Self::Payload>,
        next: Snapshot<Self, Self::Payload>,
    ) {
    }
}

/// One token per slot of one table page, keyed by slot index.
///
/// Generic in the token so that the reader half and the writer half of a page
/// have the same shape: [`TableReaders`] is what a walk carries, and
/// [`TableWriters`] is what the host lock hands out to an update.
#[verifier::accept_recursive_types(Tok)]
pub tracked struct TablePerm<Tok> {
    pub tracked slots: Map<int, Tok>,
    pub ghost base: usize,
    pub ghost provenance: Provenance,
    pub ghost ids: Map<int, Loc>,
    pub ghost count: nat,
}

pub type TableReaders<A, H, L> = TablePerm<
    RWShared<Slot<A, H, L>, <L as ChildOf<A, H>>::Escrow>,
>;

pub type TableWriters<A, H, L> = TablePerm<WritePerm<Slot<A, H, L>>>;

impl<Tok> TablePerm<Tok> {
    pub open spec fn slot_addr(self, index: int) -> int {
        self.base as int + index * 8
    }

    pub open spec fn dom_wf(self) -> bool {
        &&& self.slots.dom() =~= set_int_range(0, self.count as int)
        &&& self.ids.dom() =~= self.slots.dom()
    }
}

impl<T: IsValidAtomicType, P> TablePerm<RWShared<T, P>> {
    /// Every slot of the page is owned, and slot `index` is the token for the
    /// word at `base + index * 8`.
    ///
    /// Stated generically in the payload rather than on the `TableReaders`
    /// alias: naming `ChildOf::Escrow` here would make this definition and the
    /// escrow's own well-formedness mutually recursive.
    pub open spec fn wf(self) -> bool {
        &&& self.dom_wf()
        &&& forall|index: int|
            #![trigger self.slots[index]]
            self.slots.dom().contains(index) ==> {
                &&& self.slots[index].ptr()@.addr == self.slot_addr(index)
                &&& self.slots[index].ptr()@.provenance == self.provenance
                &&& self.slots[index].id() == self.ids[index]
            }
    }
}

impl<T: RWModel> TablePerm<WritePerm<T>> {
    /// The writer half of a page: the update side of the same slots, matched to
    /// the reader half by slot identity.
    pub open spec fn wf(self) -> bool {
        &&& self.dom_wf()
        &&& forall|index: int|
            #![trigger self.slots[index]]
            self.slots.dom().contains(index) ==> self.slots[index].id() == self.ids[index]
    }
}

} // verus!
