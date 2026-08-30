//! Permissions to memory reached through a page table.
//!
//! [`GeneralPointsTo`] is the one primitive: a set of aliasing virtual pointers,
//! the value they reach, and where it physically is. [`PhysPointsTo`] restricts
//! it to memory named by its physical address.
//!
//! Ownership here is carried by *address tokens*: a [`VirtAddrTok`] per alias
//! and a [`PhysAddrTok`] per frame, each drawn from a single global address
//! space that hands every address out once. Owning the virtual range a pointer
//! spans and the physical range beneath it is what it means to own the memory.
//!
//! That last sentence is the part no model of memory indexed by address can
//! decide, so it is assumed, in exactly two places and in three modes:
//!
//! - [`GeneralPointsTo::borrow`], [`GeneralPointsTo::borrow_mut`] and
//!   [`GeneralPointsTo::into_points_to`] -- holding the tokens for an alias
//!   yields a vstd [`PointsTo`] for it, and every alias yields the same value,
//!   so a write through one is what the others then read. Three signatures of
//!   one assumption: shared, mutable, and by value.
//! - [`GeneralPointsTo::borrow_mut_via_pt`] -- a page walk that translates a
//!   pointer to where this memory is lets that pointer reach it, for as long as
//!   the walk is borrowed.
//!
//! The disjointness of two permissions, virtual and physical alike, is *derived*
//! from the address spaces rather than assumed.
use crate::UniqueAddress;
use crate::arch::x86_64::reg_contract::cr3_phys_addr;
use crate::entry::PTEntry;
use crate::level::PageLevel;
use crate::structs::frame::PhysFrame;
use crate::structs::page::Page;
use crate::structs::sizes::PageSize;
use vstd::math::min;
use vstd::arithmetic::power2::pow2;
use crate::structs::arch_contract::*;
use crate::ArchPagingMeta;
use machine_model::arch::Cr3;
use machine_model::register::RustRegisterPointsTo;
use vstd::prelude::*;
use vstd::raw_ptr::MemContents;
use vstd::layout::{align_of, size_of};
use vstd::raw_ptr::PointsTo;
use vstd::raw_ptr::PointsToRaw;
use vstd::raw_ptr::spec_cast_ptr_to_thin_ptr;
use vstd::raw_ptr::{PtrData, ptr_mut_from_data};
use vstd::resource::frac::FracGhost;
use vstd::resource::Loc;
use vstd::tokens::InstanceId;

verus! {
/// Offset of an address within its page.
pub open spec fn page_offset_of<A: ArchPagingMeta>(addr: int) -> int {
    addr % page_size::<A>() as int
}

/// Start of the page an address falls in.
pub open spec fn page_start_of<A: ArchPagingMeta>(addr: int) -> int {
    addr - page_offset_of::<A>(addr)
}

/// The `i`-th element of an array, as a pointer.
///
/// Address and provenance are what say which memory a pointer reaches, and an
/// array element is at a known offset within the same allocation, so the
/// element pointer keeps the array's provenance and moves the address.
pub open spec fn array_element_ptr<T, const N: usize>(p: *mut [T; N], i: int) -> *mut T {
    ptr_mut_from_data(
        PtrData {
            addr: (p@.addr + i * size_of::<T>()) as usize,
            provenance: p@.provenance,
            metadata: (),
        },
    )
}

/// **Assumption.** An array is its elements, laid out end to end.
///
/// Rust guarantees this -- `[T; N]` is `N` contiguous `T`s, aligned as a `T` --
/// but vstd's [`size_of`] and [`align_of`] are uninterpreted, so nothing in it
/// relates the two. This is a statement about layout, not about paging, and it
/// is the whole of what is assumed here.
pub broadcast axiom fn axiom_array_layout<T, const N: usize>()
    ensures
        #[trigger] size_of::<[T; N]>() == N * size_of::<T>(),
        align_of::<[T; N]>() == align_of::<T>(),
;

/// **Assumption.** A permission to an array is permission to each of its
/// elements, each keeping the value it had.
///
/// The counterpart of [`axiom_array_layout`] for ownership rather than for
/// addresses: vstd's [`PointsTo`] is opaque, and it offers no way to see an
/// array permission as its elements' -- [`PointsTo::into_raw`] insists the
/// memory be uninitialized, which is exactly the case this must not be limited
/// to.
pub axiom fn points_to_array_split<T, const N: usize>(tracked pt: PointsTo<[T; N]>) -> (tracked
    ret: Seq<PointsTo<T>>)
    requires
        pt.is_init(),
    ensures
        ret.len() == N,
        forall|i: int|
            #![trigger ret[i]]
            0 <= i < N ==> {
                &&& ret[i].ptr() == array_element_ptr(pt.ptr(), i)
                &&& ret[i].opt_value() == MemContents::Init(pt.value()[i])
            },
;

/// Data associated with a [`GeneralPointsTo`] permission.
///
/// One value for the whole pointer set, because the set is the set of aliases *of
/// the same memory*; a permission covering pointers that disagreed would not
/// describe one object.
///
/// `is_pt` and `frame_addrs` are the two ways this memory can be more than bytes:
/// the first says the MMU reads it, so writing it changes what other pointers
/// mean; the second says which physical memory it is pinned to, when that is
/// knowable at all.
pub ghost struct GeneralPointsToData<T, A: ArchPagingMeta> {
    /// Every virtual pointer that reaches this memory.
    pub ptrs: Set<*mut T>,
    /// The possibly-uninitialized value all of `ptrs` reach.
    pub opt_value: MemContents<T>,
    /// Whether the MMU reads this memory as part of a page table.
    pub is_pt: bool,
    /// The frames the memory is pinned to, in order, when the translation is
    /// fixed and the memory may be named physically -- page tables and IO
    /// memory. Empty when the backing memory is not the permission's to know:
    /// it may be swapped out and back, or copied on write, so any frame
    /// recorded here could go stale.
    ///
    /// The empty sequence is what "not pinned" means; there is no separate
    /// `None`, because a pinning that names no frames pins nothing.
    ///
    /// A *sequence*, because a `T` need not fit in one frame, and contiguous
    /// virtually does not mean contiguous physically. [`PhysFrame`]s rather
    /// than bare addresses, so that the alignment the translation depends on is
    /// carried by the type instead of restated as a clause every user has to
    /// remember.
    pub frame_addrs: Seq<PhysFrame<A::MinPageSize>>,
}

/// Ownership of a range of *virt* addresses, drawn from one global address
/// space so that two tokens naming the same address cannot both exist.
pub tracked struct VirtAddrTok(UniqueAddress);

impl VirtAddrTok {
    /// The single address space every virtual token is drawn from. Being one
    /// space is what makes two tokens comparable, and therefore disjoint.
    uninterp spec fn address_space() -> InstanceId;

    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        self.0.address_space() == Self::address_space()
    }

    closed spec fn dom(&self) -> Set<int> {
        self.0.dom()
    }

    pub closed spec fn is_range(&self, start: int, len: int) -> bool {
        self.0.is_range(start, len)
    }

    /// Two tokens own disjoint addresses -- the whole point of the space.
    proof fn is_disjoint(tracked &mut self, tracked other: &Self)
        ensures
            old(self).dom().disjoint(other.dom()),
            final(self).dom() == old(self).dom(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.0.prove_disjoint(&other.0);
    }

    /// Cut a contiguous range in two at `mid`.
    ///
    /// Owning a range is owning each of its addresses, so the halves are the
    /// same ownership described in more detail; nothing is created, which is
    /// why this is a proof and not one of the module's assumptions.
    pub proof fn split_range(tracked self, start: int, len: int, mid: int) -> (tracked res: (
        Self,
        Self,
    ))
        requires
            self.is_range(start, len),
            start <= mid <= start + len,
        ensures
            res.0.is_range(start, mid - start),
            res.1.is_range(mid, start + len - mid),
    {
        use_type_invariant(&self);
        let ghost range = Set::range(start, mid);
        assert(range.subset_of(self.0.dom()));
        let tracked (left, right) = self.0.split(range);
        assert(right.dom() =~= Set::range(mid, start + len));
        (VirtAddrTok(left), VirtAddrTok(right))
    }

    /// Put two adjacent ranges back together.
    pub proof fn join_range(tracked self, tracked other: Self, start: int, mid: int, end: int)
        -> (tracked res: Self)
        requires
            self.is_range(start, mid - start),
            other.is_range(mid, end - mid),
            start <= mid <= end,
        ensures
            res.is_range(start, end - start),
    {
        use_type_invariant(&self);
        use_type_invariant(&other);
        let tracked joined = self.0.join(other.0);
        assert(joined.dom() =~= Set::range(start, end));
        VirtAddrTok(joined)
    }
}

/// Ownership of a range of *physical* addresses, drawn from one global address
/// space so that two tokens naming the same address cannot both exist.
pub tracked struct PhysAddrTok(UniqueAddress);

impl PhysAddrTok {
    /// The single address space every physical token is drawn from. Being one
    /// space is what makes two tokens comparable, and therefore disjoint.
    uninterp spec fn address_space() -> InstanceId;

    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        self.0.address_space() == Self::address_space()
    }

    closed spec fn dom(&self) -> Set<int> {
        self.0.dom()
    }

    pub closed spec fn is_range(&self, start: int, len: int) -> bool {
        self.0.is_range(start, len)
    }

    /// Two tokens own disjoint addresses -- the whole point of the space.
    proof fn is_disjoint(tracked &mut self, tracked other: &Self)
        ensures
            old(self).dom().disjoint(other.dom()),
            final(self).dom() == old(self).dom(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.0.prove_disjoint(&other.0);
    }

    /// Cut a contiguous range in two at `mid`. See
    /// [`VirtAddrTok::split_range`].
    pub proof fn split_range(tracked self, start: int, len: int, mid: int) -> (tracked res: (
        Self,
        Self,
    ))
        requires
            self.is_range(start, len),
            start <= mid <= start + len,
        ensures
            res.0.is_range(start, mid - start),
            res.1.is_range(mid, start + len - mid),
    {
        use_type_invariant(&self);
        let ghost range = Set::range(start, mid);
        assert(range.subset_of(self.0.dom()));
        let tracked (left, right) = self.0.split(range);
        assert(right.dom() =~= Set::range(mid, start + len));
        (PhysAddrTok(left), PhysAddrTok(right))
    }

    /// Put two adjacent ranges back together.
    pub proof fn join_range(tracked self, tracked other: Self, start: int, mid: int, end: int)
        -> (tracked res: Self)
        requires
            self.is_range(start, mid - start),
            other.is_range(mid, end - mid),
            start <= mid <= end,
        ensures
            res.is_range(start, end - start),
    {
        use_type_invariant(&self);
        use_type_invariant(&other);
        let tracked joined = self.0.join(other.0);
        assert(joined.dom() =~= Set::range(start, end));
        PhysAddrTok(joined)
    }
}

/// One page's mapping record, as much of it as its holder owns.
///
/// The record for a page is a single ghost variable pinned to
/// [`Self::id_of_vpage`]; this is a share of it, and the type invariant is
/// that pin. Carrying the page alongside the share is what makes the invariant
/// statable, and it means nothing else has to restate it: any `Mapping` in hand
/// is already known to be a share of the right variable, so two of them for one
/// page necessarily [`agree`](Self::agree).
#[verifier::reject_recursive_types(A)]
pub tracked struct Mapping<A: ArchPagingMeta> {
    /// The page this records.
    ghost vpage: Page<A::MinPageSize>,
    /// A share of that page's record.
    tracked frame: FracGhost<Option<VirtMapping<A::MinPageSize>>>,
}

/// What a page is mapped to, as much as its owner is entitled to rely on.
///
/// Wrapped in an `Option` where it is recorded: `None` is a page that maps to
/// no frame at all.
pub enum VirtMapping<S: PageSize> {
    Fixed(PhysFrame<S>), // Type 1 - 4 mapping
    Dynamic, // Type 5 mapping, no COW, no Dedup, no page swap
}

impl<A: ArchPagingMeta> Mapping<A> {
    /// The identity of the ghost variable recording what the page starting at
    /// `vpage` maps to.
    pub uninterp spec fn id_of_vpage(vpage: int) -> Loc;

    /// The share of a page's record the page table keeps.
    pub spec const PAGE_TABLE_SHARE: real = 0.5real;

    /// The share of a page's record the permissions owning it divide up.
    pub spec const OWNER_TOTAL_SHARE: real = 0.5real;

    /// The share of a page's record that comes with owning `bytes` bytes of it.
    pub open spec fn share_of(bytes: int) -> real {
        Self::OWNER_TOTAL_SHARE * (bytes as real) / (page_size::<A>() as real)
    }

    /// A share is proportional to the bytes it comes with, so splitting the
    /// bytes splits the share.
    pub proof fn lemma_share_of_add(b1: int, b2: int)
        ensures
            Self::share_of(b1) + Self::share_of(b2) == Self::share_of(b1 + b2),
    {
        let ps = page_size::<A>() as real;
        assert((b1 + b2) as real == (b1 as real) + (b2 as real));
        assert(Self::OWNER_TOTAL_SHARE * ((b1 as real) + (b2 as real)) == Self::OWNER_TOTAL_SHARE
            * (b1 as real) + Self::OWNER_TOTAL_SHARE * (b2 as real));
        let x = Self::OWNER_TOTAL_SHARE * (b1 as real);
        let y = Self::OWNER_TOTAL_SHARE * (b2 as real);
        <A::MinPageSize as PageSize>::lemma_size_wf();
        assert(ps > 0.0real);
        assert((x + y) / ps == x / ps + y / ps) by (nonlinear_arith)
            requires
                ps > 0.0real,
        ;
    }

    /// Owning some of a page is owning some of its record, and owning more of
    /// it is owning more.
    pub proof fn lemma_share_of_pos(b1: int, b2: int)
        requires
            0 < b1 < b2 <= page_size::<A>(),
        ensures
            0.0real < Self::share_of(b1) < Self::share_of(b2),
    {
        <A::MinPageSize as PageSize>::lemma_size_wf();
        let ps = page_size::<A>() as real;
        let x = Self::OWNER_TOTAL_SHARE * (b1 as real);
        let y = Self::OWNER_TOTAL_SHARE * (b2 as real);
        assert(0.0real < x < y);
        assert(0.0real < x / ps < y / ps) by (nonlinear_arith)
            requires
                ps > 0.0real,
                0.0real < x < y,
        ;
    }

    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        self.frame.id() == Self::id_of_vpage(self.vpage@ as int)
    }

    /// The page this records.
    pub closed spec fn vpage(&self) -> Page<A::MinPageSize> {
        self.vpage
    }

    /// Where that page starts.
    pub open spec fn vpage_addr(&self) -> int {
        self.vpage()@ as int
    }

    /// What the page resolves to, or `None` where the record says nothing.
    pub closed spec fn frame(&self) -> Option<VirtMapping<A::MinPageSize>> {
        self.frame@
    }

    /// How much of the page's record this is. See [`Self::share_of`].
    pub closed spec fn share(&self) -> real {
        self.frame.frac()
    }

    /// Give away part of this share.
    ///
    /// The record itself is untouched -- both pieces still say the page maps
    /// where it did. All that moves is how much of it each piece is, which is
    /// what decides who may later change it.
    pub proof fn split(tracked &mut self, share: real) -> (tracked result: Self)
        requires
            0.0real < share < old(self).share(),
        ensures
            final(self).vpage() == old(self).vpage(),
            result.vpage() == old(self).vpage(),
            final(self).frame() == old(self).frame(),
            result.frame() == old(self).frame(),
            final(self).share() == old(self).share() - share,
            result.share() == share,
    {
        use_type_invariant(&*self);
        let tracked part = self.frame.split_to(share);
        Mapping { vpage: self.vpage, frame: part }
    }

    /// Take back a share of the same page's record.
    ///
    /// Hypothesised on the page, not on ids: [`Self::id_of_vpage`] makes the two
    /// the same variable, so there is nothing to check beyond their both being
    /// about this page.
    pub proof fn merge(tracked &mut self, tracked other: Self)
        requires
            old(self).vpage_addr() == other.vpage_addr(),
        ensures
            final(self).vpage() == old(self).vpage(),
            final(self).frame() == old(self).frame(),
            final(self).share() == old(self).share() + other.share(),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        self.frame.combine(other.frame);
    }

    /// Record that the page now maps to `frame`.
    ///
    /// Needs the owners' whole share *and* the table's: repointing a page is
    /// only sound when every byte of it is accounted for, so no permission is
    /// left holding memory there to be surprised. That is what the two share
    /// preconditions say, and together they are the whole variable.
    pub proof fn update_frame(
        tracked &mut self,
        tracked other: &mut Self,
        frame: Option<VirtMapping<A::MinPageSize>>,
    )
        requires
            old(self).share() == Self::OWNER_TOTAL_SHARE,
            old(other).share() == Self::PAGE_TABLE_SHARE,
            old(self).vpage_addr() == old(other).vpage_addr(),
        ensures
            final(self).vpage() == old(self).vpage(),
            final(other).vpage() == old(other).vpage(),
            final(self).share() == old(self).share(),
            final(other).share() == old(other).share(),
            final(self).frame() == frame,
            final(other).frame() == frame,
    {
        use_type_invariant(&*self);
        use_type_invariant(&*other);
        self.frame.update_with(&mut other.frame, frame);
    }

    /// Two shares of one page's record say the same thing.
    ///
    /// The hypothesis is about pages, not ids: the pin turns "same page" into
    /// "same variable", which is the whole reason it exists. Without it this
    /// would need an id equality that nothing on either side could supply.
    ///
    /// Stated on the start address rather than the [`Page`] value, because that
    /// is what a caller holding two permissions can compare -- and it is what
    /// the pin is a function of, so it is all the equality that is needed.
    pub proof fn agree(tracked &self, tracked other: &Self)
        requires
            self.vpage_addr() == other.vpage_addr(),
        ensures
            self.frame() == other.frame(),
    {
        use_type_invariant(self);
        use_type_invariant(other);
        self.frame.agree(&other.frame);
    }
}

/// The shape of a piece of memory, with nothing said about what it holds: how
/// many bytes, how far into its first page they begin, and which frames they
/// sit in.
///
/// Shared by [`GeneralPointsTo`] and [`GeneralPointsToRaw`], which differ only
/// in whether the bytes have a type yet. Everything the invariants say about
/// pages, tokens and records is a property of the shape, so it is stated once
/// here instead of once per permission -- two copies of an invariant this
/// delicate would drift, and a permission that disagreed with its twin about
/// which bytes it owns is exactly the unsoundness the tokens exist to prevent.
#[verifier::reject_recursive_types(A)]
pub ghost struct MemShape<A: ArchPagingMeta> {
    /// How many bytes the memory spans.
    pub size: nat,
    /// Where it starts inside its first page.
    pub offset: usize,
    /// How many pages it runs through.
    ///
    /// A field rather than a division of `size + offset`: it is pinned to that
    /// value by [`Self::wf`] multiplicatively, which is the form the solver can
    /// actually use, and it lets unpinned memory have pages without having
    /// frames to name them by.
    pub npages: nat,
    /// The frames it sits in, in order, when it is pinned; empty when it is not.
    pub frame_addrs: Seq<PhysFrame<A::MinPageSize>>,
}

impl<A: ArchPagingMeta> MemShape<A> {
    /// The number of pages this memory occupies.
    #[verifier::inline]
    pub open spec fn npages(&self) -> int {
        self.npages as int
    }

    /// Whether the frames backing this memory are its to name.
    #[verifier::inline]
    pub open spec fn pinned(&self) -> bool {
        self.frame_addrs.len() > 0
    }

    /// How many of this memory's bytes lie before the `i`-th page it occupies.
    ///
    /// Page `i` begins `i` pages after the start of page 0, which is `offset`
    /// bytes before the memory does; clamped at the start, since page 0 holds
    /// no bytes before the memory begins.
    pub open spec fn byte_start_of_page(&self, i: int) -> int {
        if i <= 0 {
            0
        } else {
            i * page_size::<A>() - self.offset
        }
    }

    /// Where this memory starts inside the `i`-th page it occupies: the offset
    /// in the first page, and the very start of every page after it.
    pub open spec fn offset_in_page(&self, i: int) -> int {
        if i == 0 {
            self.offset as int
        } else {
            0
        }
    }

    /// How many bytes of this memory lie in the `i`-th page it occupies: what
    /// lies before the next page, less what lies before this one, and never
    /// past the end.
    pub open spec fn bytes_in_page(&self, i: int) -> int {
        min(self.size as int, self.byte_start_of_page(i + 1)) - self.byte_start_of_page(i)
    }

    /// The page an alias at `addr` occupies at index `i`.
    pub open spec fn vpage_at(&self, addr: int, i: int) -> int {
        page_start_of::<A>(addr) + i * page_size::<A>()
    }

    /// The pages an alias at `addr` occupies.
    pub open spec fn vpages_of(&self, addr: int) -> Set<int> {
        Set::range(0, self.npages()).map(|i: int| self.vpage_at(addr, i))
    }

    /// The pages account for the bytes exactly: the offset fits in the first
    /// page, the pages are enough to hold everything, and dropping one would
    /// not be. Memory of no size occupies no page at all.
    ///
    /// Frames are either named for every page or for none: memory is pinned or
    /// it is not, and there is no state in between.
    pub open spec fn wf(&self) -> bool {
        &&& self.offset < page_size::<A>()
        &&& self.size == 0 <==> self.npages == 0
        &&& self.npages > 0 ==> {
            &&& self.size + self.offset <= self.npages * page_size::<A>()
            &&& (self.npages - 1) * page_size::<A>() < self.size + self.offset
        }
        &&& self.pinned() ==> self.frame_addrs.len() == self.npages
    }

    /// Each page holds a whole number of bytes and no more than a page's worth,
    /// and together they hold all of them.
    pub proof fn lemma_bytes_in_page(&self, i: int)
        requires
            self.wf(),
            0 <= i < self.npages(),
        ensures
            0 < self.bytes_in_page(i) <= page_size::<A>(),
            self.byte_start_of_page(i) + self.bytes_in_page(i) == min(
                self.size as int,
                self.byte_start_of_page(i + 1),
            ),
            i == self.npages() - 1 ==> self.byte_start_of_page(i) + self.bytes_in_page(i)
                == self.size,
            i < self.npages() - 1 ==> self.byte_start_of_page(i + 1) <= self.size,
    {
        let ps = page_size::<A>() as int;
        assert((i + 1) * ps == i * ps + ps) by (nonlinear_arith);
        if i > 0 {
            assert(i * ps >= 1 * ps) by (nonlinear_arith)
                requires
                    i >= 1,
                    ps > 0,
            ;
        }
        if i < self.npages() - 1 {
            assert((i + 1) * ps <= (self.npages() - 1) * ps) by (nonlinear_arith)
                requires
                    i + 1 <= self.npages() - 1,
                    ps > 0,
            ;
        }
    }

    /// Which of this memory's pages holds the byte at index `b`.
    pub open spec fn page_of_byte(&self, b: int) -> int {
        (b + self.offset) / page_size::<A>() as int
    }

    /// The shape of the first `at` bytes.
    pub open spec fn take(&self, at: nat) -> MemShape<A> {
        let np = self.page_of_byte(at - 1) + 1;
        MemShape {
            size: at,
            offset: self.offset,
            npages: np as nat,
            frame_addrs: if self.pinned() {
                self.frame_addrs.take(np)
            } else {
                Seq::empty()
            },
        }
    }

    /// The shape of everything from byte `at` on.
    ///
    /// It starts where the split lands, so its offset is that byte's offset in
    /// its page, and it runs from that page rather than from this memory's
    /// first: the page the split lands in belongs to both halves whenever the
    /// split is not page-aligned.
    pub open spec fn skip(&self, at: nat) -> MemShape<A> {
        let st = self.page_of_byte(at as int);
        MemShape {
            size: (self.size - at) as nat,
            offset: ((at + self.offset) % page_size::<A>() as int) as usize,
            npages: (self.npages() - st) as nat,
            frame_addrs: if self.pinned() {
                self.frame_addrs.skip(st)
            } else {
                Seq::empty()
            },
        }
    }

    /// Splitting a run of bytes leaves two runs of bytes.
    ///
    /// The page the split lands in is the only one the halves can disagree
    /// about, and they disagree about it only when the split is not
    /// page-aligned -- which is exactly when the left half needs one page more
    /// than the right half starts at.
    pub proof fn lemma_split(&self, at: nat)
        requires
            self.wf(),
            0 < at < self.size,
        ensures
            self.take(at).wf(),
            self.skip(at).wf(),
            ({
                let st = self.page_of_byte(at as int);
                let np = self.take(at).npages();
                &&& 0 <= st <= np <= self.npages()
                &&& np <= st + 1
                &&& at + self.offset == st * page_size::<A>() + self.skip(at).offset
                &&& self.skip(at).offset == 0 <==> np == st
                &&& self.take(at).pinned() == self.pinned()
                &&& self.skip(at).pinned() == self.pinned()
            }),
    {
        broadcast use {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod,
            vstd::arithmetic::div_mod::lemma_mod_bound,
        };

        let ps = page_size::<A>() as int;
        let st = self.page_of_byte(at as int);
        let stl = self.page_of_byte(at - 1);
        let np = stl + 1;
        let off2 = (at + self.offset) % ps;
        assert(at + self.offset == ps * st + off2);
        assert(at - 1 + self.offset == ps * stl + (at - 1 + self.offset) % ps);
        // The two page indices differ by at most one, since the byte indices do.
        assert(stl <= st) by (nonlinear_arith)
            requires
                at - 1 + self.offset == ps * stl + (at - 1 + self.offset) % ps,
                at + self.offset == ps * st + off2,
                0 <= off2 < ps,
                0 <= (at - 1 + self.offset) % ps < ps,
                ps > 0,
        ;
        assert(st <= stl + 1) by (nonlinear_arith)
            requires
                at - 1 + self.offset == ps * stl + (at - 1 + self.offset) % ps,
                at + self.offset == ps * st + off2,
                0 <= off2 < ps,
                0 <= (at - 1 + self.offset) % ps < ps,
                ps > 0,
        ;
        let r = (at - 1 + self.offset) % ps;
        assert(ps * (st - stl) == 1 + r - off2) by (nonlinear_arith)
            requires
                at - 1 + self.offset == ps * stl + r,
                at + self.offset == ps * st + off2,
        ;
        if st == stl {
            assert(ps * (st - stl) == 0) by (nonlinear_arith)
                requires
                    st == stl,
            ;
        } else {
            assert(st == stl + 1);
            assert(ps * (st - stl) == ps) by (nonlinear_arith)
                requires
                    st == stl + 1,
            ;
        }
        assert(off2 == 0 <==> np == st);
        // The left half needs exactly the pages up to the one holding byte
        // `at - 1`, and no fewer.
        assert(at + self.offset <= np * ps) by (nonlinear_arith)
            requires
                at - 1 + self.offset == ps * stl + r,
                0 <= r < ps,
                np == stl + 1,
                ps > 0,
        ;
        assert((np - 1) * ps < at + self.offset) by (nonlinear_arith)
            requires
                at - 1 + self.offset == ps * stl + r,
                0 <= r < ps,
                np == stl + 1,
                ps > 0,
        ;
        // The right half starts inside this memory, so it keeps at least one
        // page, and shifting both its size and its page count by the same
        // amount preserves the fit.
        assert(st < self.npages()) by (nonlinear_arith)
            requires
                at + self.offset == ps * st + off2,
                0 <= off2 < ps,
                at + self.offset < self.size + self.offset,
                self.size + self.offset <= self.npages() * ps,
                ps > 0,
        ;
        assert(self.size - at + off2 <= (self.npages() - st) * ps) by (nonlinear_arith)
            requires
                at + self.offset == ps * st + off2,
                self.size + self.offset <= self.npages() * ps,
                ps > 0,
        ;
        assert((self.npages() - st - 1) * ps < self.size - at + off2) by (nonlinear_arith)
            requires
                at + self.offset == ps * st + off2,
                (self.npages() - 1) * ps < self.size + self.offset,
                ps > 0,
        ;
        assert(np <= self.npages());
        assert(self.take(at).npages() == np);
        assert(self.skip(at).npages() == self.npages() - st);
        assert(self.skip(at).offset == off2);
        assert(at + self.offset == st * ps + off2) by (nonlinear_arith)
            requires
                at + self.offset == ps * st + off2,
        ;
        assert(self.take(at).pinned() == self.pinned());
        assert(self.skip(at).pinned() == self.pinned());
        if self.pinned() {
            assert(self.take(at).frame_addrs.len() == np);
            assert(self.skip(at).frame_addrs.len() == self.npages() - st);
        }
    }

    /// How many bytes the left half keeps in the page the split lands in.
    ///
    /// Zero exactly when the split is page-aligned, in which case that page
    /// belongs to the right half alone.
    pub open spec fn bytes_before_split(&self, at: nat) -> int {
        self.skip(at).offset - self.offset_in_page(self.page_of_byte(at as int))
    }

    /// The left half occupies the same pages this memory does, holding the same
    /// bytes in each, until the page the split lands in.
    pub proof fn lemma_take_page(&self, at: nat, i: int)
        requires
            self.wf(),
            0 < at < self.size,
            0 <= i < self.take(at).npages(),
        ensures
            self.take(at).byte_start_of_page(i) == self.byte_start_of_page(i),
            self.take(at).offset_in_page(i) == self.offset_in_page(i),
            i < self.take(at).npages() - 1 ==> self.take(at).bytes_in_page(i) == self.bytes_in_page(
                i,
            ),
            i == self.take(at).npages() - 1 ==> self.take(at).bytes_in_page(i)
                == self.bytes_before_split(at) + self.byte_start_of_page(
                self.page_of_byte(at as int),
            ) - self.byte_start_of_page(i),
    {
        broadcast use {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod,
            vstd::arithmetic::div_mod::lemma_mod_bound,
        };

        self.lemma_split(at);
        let ps = page_size::<A>() as int;
        let st = self.page_of_byte(at as int);
        let np = self.take(at).npages();
        assert(at + self.offset <= np * ps);
        if i < np - 1 {
            assert((i + 1) * ps <= (np - 1) * ps) by (nonlinear_arith)
                requires
                    i + 1 <= np - 1,
                    ps > 0,
            ;
            assert((np - 1) * ps <= at - 1 + self.offset) by (nonlinear_arith)
                requires
                    at - 1 + self.offset == ps * (np - 1) + (at - 1 + self.offset) % ps,
                    0 <= (at - 1 + self.offset) % ps < ps,
            ;
        } else {
            assert(i == np - 1);
            let off2 = self.skip(at).offset as int;
            assert(at + self.offset == st * ps + off2) by (nonlinear_arith)
                requires
                    at + self.offset == ps * st + off2,
            ;
            // The bytes before the split, measured from the start of the page
            // it lands in, are the bytes the left half keeps there.
            if st == 0 {
                assert(self.byte_start_of_page(st) == 0);
            } else {
                assert(self.byte_start_of_page(st) == st * ps - self.offset);
            }
            assert(at == self.bytes_before_split(at) + self.byte_start_of_page(st));
        }
    }

    /// The right half occupies the pages from the split on, holding the same
    /// bytes in each after the first, whose bytes are what the left half left
    /// behind.
    pub proof fn lemma_skip_page(&self, at: nat, j: int)
        requires
            self.wf(),
            0 < at < self.size,
            0 <= j < self.skip(at).npages(),
        ensures
            j > 0 ==> self.skip(at).byte_start_of_page(j) + at == self.byte_start_of_page(
                j + self.page_of_byte(at as int),
            ),
            self.skip(at).offset_in_page(j) == if j == 0 {
                self.skip(at).offset as int
            } else {
                0
            },
            j > 0 ==> self.skip(at).bytes_in_page(j) == self.bytes_in_page(
                j + self.page_of_byte(at as int),
            ),
            j == 0 ==> self.skip(at).bytes_in_page(0) == self.bytes_in_page(
                self.page_of_byte(at as int),
            ) - self.bytes_before_split(at),
    {
        broadcast use {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod,
            vstd::arithmetic::div_mod::lemma_mod_bound,
        };

        self.lemma_split(at);
        let ps = page_size::<A>() as int;
        let st = self.page_of_byte(at as int);
        let off2 = self.skip(at).offset as int;
        assert(at + self.offset == st * ps + off2);
        assert((j + st) * ps == j * ps + st * ps) by (nonlinear_arith);
        assert((j + 1 + st) * ps == (j + 1) * ps + st * ps) by (nonlinear_arith);
        assert((st + 1) * ps == st * ps + ps) by (nonlinear_arith);
        assert(1int * ps == ps) by (nonlinear_arith);
        if j > 0 {
            assert(self.skip(at).byte_start_of_page(j + 1) + at == self.byte_start_of_page(
                j + 1 + st,
            ));
        } else {
            assert(self.skip(at).byte_start_of_page(1) + at == self.byte_start_of_page(st + 1));
            if st == 0 {
                assert(self.byte_start_of_page(st) == 0);
            } else {
                assert(self.byte_start_of_page(st) == st * ps - self.offset);
            }
            assert(at == self.bytes_before_split(at) + self.byte_start_of_page(st));
        }
    }

    /// Splitting the bytes moves the split along with them: an alias of the
    /// right half starts `at` bytes further into the same page run.
    pub proof fn lemma_alias_offset_shift(&self, at: nat, addr: int)
        requires
            self.wf(),
            0 < at < self.size,
            page_offset_of::<A>(addr) == self.offset,
        ensures
            page_offset_of::<A>(addr + at) == self.skip(at).offset,
            page_start_of::<A>(addr + at) == page_start_of::<A>(addr) + self.page_of_byte(
                at as int,
            ) * page_size::<A>(),
    {
        self.lemma_split(at);
        let ps = page_size::<A>() as int;
        let off = self.offset as int;
        let a2 = at as int;
        vstd::arithmetic::div_mod::lemma_add_mod_noop(addr, a2, ps);
        vstd::arithmetic::div_mod::lemma_add_mod_noop(off, a2, ps);
        vstd::arithmetic::div_mod::lemma_small_mod(self.offset as nat, page_size::<A>() as nat);
    }

    /// Split the record shares one alias holds at byte `at`.
    ///
    /// Every page but the one the split lands in goes wholly to one side. That
    /// page's record is shared, and the share follows the bytes: each half is
    /// left owning exactly as much of the record as it owns of the page.
    pub proof fn split_records(
        &self,
        tracked records: Seq<Mapping<A>>,
        at: nat,
        addr: int,
    ) -> (tracked res: (Seq<Mapping<A>>, Seq<Mapping<A>>))
        requires
            self.wf(),
            0 < at < self.size,
            page_offset_of::<A>(addr) == self.offset,
            self.records_wf(records, addr, self.pinned()),
        ensures
            self.take(at).records_wf(res.0, addr, self.pinned()),
            self.skip(at).records_wf(res.1, addr + at, self.pinned()),
    {
        self.lemma_split(at);
        self.lemma_alias_offset_shift(at, addr);
        let ghost ps = page_size::<A>() as int;
        let ghost st = self.page_of_byte(at as int);
        let ghost np = self.take(at).npages();
        let ghost lbytes = self.bytes_before_split(at);
        let tracked mut left = records;
        let tracked mut right = left.tracked_split_at(st);
        if np == st + 1 {
            self.lemma_take_page(at, st);
            self.lemma_skip_page(at, 0);
            self.take(at).lemma_bytes_in_page(st);
            self.skip(at).lemma_bytes_in_page(0);
            self.lemma_bytes_in_page(st);
            let ghost rbytes = self.bytes_in_page(st) - lbytes;
            Mapping::<A>::lemma_share_of_add(lbytes, rbytes);
            Mapping::<A>::lemma_share_of_pos(rbytes, self.bytes_in_page(st));
            let tracked mut rec = right.tracked_pop_front();
            let tracked part = rec.split(Mapping::<A>::share_of(rbytes));
            left.tracked_push(rec);
            right.tracked_push_front(part);
        }
        assert(self.take(at).records_wf(left, addr, self.pinned())) by {
            assert forall|i: int| 0 <= i < np implies #[trigger] left[i].vpage_addr()
                == self.take(at).vpage_at(addr, i) && left[i].share() == Mapping::<A>::share_of(
                self.take(at).bytes_in_page(i),
            ) && left[i].frame().is_some() && (self.pinned() ==> left[i].frame() == Some(
                VirtMapping::Fixed(self.take(at).frame_addrs[i]),
            )) by {
                self.lemma_take_page(at, i);
                assert(records[i].vpage_addr() == self.vpage_at(addr, i));
            }
        }
        assert(self.skip(at).records_wf(right, addr + at, self.pinned())) by {
            assert forall|j: int| 0 <= j < self.skip(at).npages() implies #[trigger]
            right[j].vpage_addr() == self.skip(at).vpage_at(addr + at, j) && right[j].share()
                == Mapping::<A>::share_of(self.skip(at).bytes_in_page(j)) && right[j].frame().is_some()
                && (self.pinned() ==> right[j].frame() == Some(
                VirtMapping::Fixed(self.skip(at).frame_addrs[j]),
            )) by {
                self.lemma_skip_page(at, j);
                assert(records[j + st].vpage_addr() == self.vpage_at(addr, j + st));
                assert(self.skip(at).vpage_at(addr + at, j) == self.vpage_at(addr, j + st)) by {
                    assert((j + st) * ps == j * ps + st * ps) by (nonlinear_arith);
                }
            }
        }
        (left, right)
    }

    /// Split the physical tokens at byte `at`, the same way and for the same
    /// reason as [`Self::split_records`]. Unpinned memory holds none.
    pub proof fn split_phys(&self, tracked phys: Seq<PhysAddrTok>, at: nat) -> (tracked res: (
        Seq<PhysAddrTok>,
        Seq<PhysAddrTok>,
    ))
        requires
            self.wf(),
            0 < at < self.size,
            self.phys_wf(phys),
        ensures
            self.take(at).phys_wf(res.0),
            self.skip(at).phys_wf(res.1),
    {
        self.lemma_split(at);
        let ghost st = self.page_of_byte(at as int);
        let ghost np = self.take(at).npages();
        let ghost lbytes = self.bytes_before_split(at);
        let tracked mut left = phys;
        if !self.pinned() {
            let tracked right = left.tracked_split_at(0);
            return (left, right);
        }
        let tracked mut right = left.tracked_split_at(st);
        if np == st + 1 {
            self.lemma_take_page(at, st);
            self.lemma_skip_page(at, 0);
            let tracked tok = right.tracked_pop_front();
            let tracked (l, r) = tok.split_range(
                self.frame_addrs[st]@ + self.offset_in_page(st),
                self.bytes_in_page(st),
                self.frame_addrs[st]@ + self.skip(at).offset,
            );
            left.tracked_push(l);
            right.tracked_push_front(r);
        }
        assert(self.take(at).phys_wf(left)) by {
            assert forall|i: int|
                0 <= i < np implies (#[trigger] left[i]).is_range(
                self.take(at).frame_addrs[i]@ + self.take(at).offset_in_page(i),
                self.take(at).bytes_in_page(i),
            ) by {
                self.lemma_take_page(at, i);
                assert(phys[i].is_range(
                    self.frame_addrs[i]@ + self.offset_in_page(i),
                    self.bytes_in_page(i),
                ));
            }
        }
        assert(self.skip(at).phys_wf(right)) by {
            assert forall|j: int|
                0 <= j < self.skip(at).npages() implies (#[trigger] right[j]).is_range(
                self.skip(at).frame_addrs[j]@ + self.skip(at).offset_in_page(j),
                self.skip(at).bytes_in_page(j),
            ) by {
                self.lemma_skip_page(at, j);
                assert(phys[j + st].is_range(
                    self.frame_addrs[j + st]@ + self.offset_in_page(j + st),
                    self.bytes_in_page(j + st),
                ));
            }
        }
        (left, right)
    }

    /// One physical token per page, covering the bytes this memory owns in that
    /// page's frame. Unpinned memory names no frames and so holds no tokens.
    pub open spec fn phys_wf(&self, phys: Seq<PhysAddrTok>) -> bool {
        &&& phys.len() == self.frame_addrs.len()
        &&& forall|i: int|
            #![trigger phys[i], self.frame_addrs[i]]
            0 <= i < phys.len() ==> phys[i].is_range(
                self.frame_addrs[i]@ + self.offset_in_page(i),
                self.bytes_in_page(i),
            )
    }

    /// The virtual token for one alias: the range that alias spans.
    pub open spec fn alias_wf(&self, tok: VirtAddrTok, addr: int) -> bool {
        tok.is_range(addr, self.size as int)
    }

    /// The record shares one alias holds: a share of the record of every page it
    /// runs through, sized by the bytes it owns there.
    ///
    /// `pinned` is whether the frames are the permission's to name, and it is
    /// what decides how much the records must say -- an unpinned page is known
    /// to be mapped, a pinned one to be mapped to a named frame.
    pub open spec fn records_wf(&self, records: Seq<Mapping<A>>, addr: int, pinned: bool) -> bool {
        &&& records.len() == self.npages()
        &&& forall|i: int|
            #![trigger records[i]]
            0 <= i < self.npages() ==> {
                &&& records[i].vpage_addr() == self.vpage_at(addr, i)
                &&& records[i].share() == Mapping::<A>::share_of(self.bytes_in_page(i))
                // Holding a permission is holding memory that can be read and
                // written, which an unmapped page cannot be: a record of `None`
                // says the page reaches no frame at all.
                &&& records[i].frame().is_some()
                &&& pinned ==> records[i].frame() == Some(VirtMapping::Fixed(self.frame_addrs[i]))
            }
    }
}

/// Ownership of a run of bytes, with nothing said about what they hold or what
/// type they have: the address tokens for every way in, the tokens for the
/// physical memory beneath, and the record shares that keep the page table
/// honest about where that memory is.
///
/// The common part of [`GeneralPointsTo`] and [`GeneralPointsToRaw`], which add
/// only the permission that gives the bytes a value. Keyed by *address* rather
/// than by pointer, so that the same ownership can be described by the array
/// that spans it or by any of the elements inside -- which is what makes
/// [`Self::split_at`] statable at all, since the leftover of peeling an element
/// off an array has no Rust type to be keyed by.
#[verifier::reject_recursive_types(A)]
pub tracked struct MemOwn<A: ArchPagingMeta> {
    /// One address token per alias, keyed by the address the alias starts at.
    /// Owning the virtual range a pointer spans is what makes that pointer this
    /// permission's to use, and the tokens come from one address space, so no
    /// other permission can claim the same address.
    tracked virt: Map<int, VirtAddrTok>,
    /// One address token per page the memory occupies.
    tracked phys: Seq<PhysAddrTok>,
    /// A share of the record of every page every alias runs through, sized by
    /// how much of that page this permission owns. A share is enough to read
    /// what the page maps to, and not enough to change it, so the table cannot
    /// repoint a page while any permission into it is outstanding, and this
    /// permission cannot claim a mapping the table does not agree it installed.
    ///
    /// The ids are [`Mapping::id_of_vpage`], so no id has to travel with the
    /// permission for the two sides to be comparable.
    tracked mapping: Map<int, Seq<Mapping<A>>>,
    ghost size: nat,
    ghost offset: usize,
    ghost npages: nat,
    ghost frame_addrs: Seq<PhysFrame<A::MinPageSize>>,
    ghost is_pt: bool,
}

impl<A: ArchPagingMeta> MemOwn<A> {
    /// The addresses at which this memory can be reached.
    pub closed spec fn addrs(&self) -> Set<int> {
        self.virt.dom()
    }

    /// How far into its page this memory starts.
    ///
    /// A property of the memory rather than of any one alias: translation
    /// replaces only the page part of an address, so every alias sits at the
    /// same offset, and the invariant holds them to it.
    pub closed spec fn offset(&self) -> usize {
        self.offset
    }

    /// What this memory is, without its type.
    pub closed spec fn shape(&self) -> MemShape<A> {
        MemShape {
            size: self.size,
            offset: self.offset,
            npages: self.npages,
            frame_addrs: self.frame_addrs,
        }
    }

    pub closed spec fn size(&self) -> nat {
        self.size
    }

    pub closed spec fn frames(&self) -> Seq<PhysFrame<A::MinPageSize>> {
        self.frame_addrs
    }

    pub open spec fn has_pinned_phys_addr(&self) -> bool {
        self.frames().len() > 0
    }

    /// Whether the MMU reads this memory as part of a page table.
    pub closed spec fn is_pt(&self) -> bool {
        self.is_pt
    }

    #[verifier::type_invariant]
    pub closed spec fn wf(&self) -> bool {
        &&& self.shape().wf()
        &&& self.shape().phys_wf(self.phys)
        // Every alias starts at the same offset within its page, and that
        // offset is the shape's: aliases are the same bytes seen through
        // different translations, and translation does not move a byte within
        // its page.
        &&& forall|a: int| #[trigger]
            self.virt.dom().contains(a) ==> page_offset_of::<A>(a) == self.shape().offset
        &&& forall|a: int| #[trigger]
            self.virt.dom().contains(a) ==> self.shape().alias_wf(self.virt[a], a)
        &&& self.mapping.dom() =~= self.virt.dom()
        &&& forall|a: int| #[trigger]
            self.mapping.dom().contains(a) ==> self.shape().records_wf(
                self.mapping[a],
                a,
                self.has_pinned_phys_addr(),
            )
    }

    /// Every alias sits at the offset [`MemShape::offset`] records.
    pub proof fn lemma_aliases_share_page_offset(tracked &self)
        ensures
            forall|a: int| #[trigger]
                self.addrs().contains(a) ==> page_offset_of::<A>(a) == self.shape().offset,
    {
        use_type_invariant(self);
    }

    /// What the page table records as backing the `i`-th page of the alias at
    /// `a`.
    ///
    /// No id hypothesis and no instance to match: the record for a page is
    /// pinned to [`Mapping::id_of_vpage`], so this permission's share and the
    /// table's are shares of the same ghost variable by construction.
    pub closed spec fn record_at(&self, a: int, i: int) -> Option<VirtMapping<A::MinPageSize>>
        recommends
            self.addrs().contains(a),
            0 <= i < self.shape().npages(),
    {
        self.mapping[a][i].frame()
    }

    /// How many frame tokens this permission holds.
    pub closed spec fn phys_len(&self) -> nat {
        self.phys.len()
    }

    /// The physical addresses the `i`-th frame token owns.
    pub closed spec fn phys_dom(&self, i: int) -> Set<int> {
        self.phys[i].dom()
    }

    /// Every page this memory occupies is mapped to something.
    ///
    /// Owning a permission is owning memory that can be read and written, so a
    /// page it runs through cannot be one that reaches no frame. Exposes the
    /// part of the type invariant callers need, since the invariant itself is
    /// `closed`.
    pub proof fn lemma_record_is_mapped(tracked &self, a: int, i: int)
        requires
            self.addrs().contains(a),
            0 <= i < self.shape().npages(),
        ensures
            self.record_at(a, i).is_some(),
    {
        use_type_invariant(self);
    }

    /// Two permissions never share an alias: an alias is owned by holding the
    /// [`VirtAddrTok`] for the range it spans, and the virtual address space
    /// hands each address out once.
    ///
    /// No longer an appeal to vstd -- this is the address space's own guarantee,
    /// the virtual counterpart of [`Self::is_disjoint_pfn`], and it takes `self`
    /// by value for the same reason: refuting a shared alias needs a mutable
    /// borrow of a token, and a token borrowed out of `self.virt` would have to
    /// satisfy this permission's invariant for an arbitrary final value.
    ///
    /// Memory of no size spans no addresses and so is owned by nobody; the
    /// guarantee has nothing to say about it.
    pub proof fn is_disjoint(tracked self, tracked other: &Self) -> (tracked res: Self)
        requires
            self.size() != 0,
            other.size() != 0,
        ensures
            res == self,
            self.addrs().disjoint(other.addrs()),
    {
        broadcast use vstd::set_lib::range_set_properties;

        use_type_invariant(&self);
        use_type_invariant(other);
        let ghost old_self = self;
        let tracked MemOwn { mut virt, phys, mapping, size, offset, npages, frame_addrs, is_pt } = self;
        if !old_self.addrs().disjoint(other.addrs()) {
            let ghost a = choose|a: int|
                #![trigger other.addrs().contains(a)]
                old_self.addrs().contains(a) && other.addrs().contains(a);
            let tracked tok = virt.tracked_borrow_mut(a);
            let tracked other_tok = other.virt.tracked_borrow(a);
            tok.is_disjoint(other_tok);
            let ghost n = old_self.size() as int;
            assert(old_self.virt[a].dom() =~= Set::range(a, a + n));
            assert(other.virt[a].dom() =~= Set::range(a, a + other.size() as int));
            assert(Set::range(a, a + n).contains(a));
            assert(Set::range(a, a + other.size() as int).contains(a));
            assert(false);
        }
        MemOwn { virt, phys, mapping, size, offset, npages, frame_addrs, is_pt }
    }

    /// Two permissions never own the same physical byte: their frame tokens are
    /// drawn from one address space, and that space hands each address out once.
    ///
    /// Frame-level distinctness is deliberately *not* claimed -- two objects may
    /// share a frame at different offsets -- so the guarantee is stated on the
    /// address ranges themselves.
    ///
    /// Takes `self` by value rather than by `&mut`, because refuting a shared
    /// address needs a mutable borrow of a frame token, and a token borrowed out
    /// of `self.phys` would have to satisfy this permission's invariant for an
    /// arbitrary final value. Unpacking first puts the tokens in a plain `Seq`,
    /// which carries no invariant, and the invariant is re-established on the
    /// way out from the tokens' preserved domains.
    pub proof fn is_disjoint_pfn(tracked self, tracked other: &Self) -> (tracked res: Self)
        ensures
            res == self,
            forall|i: int, j: int|
                #![trigger self.phys_dom(i), other.phys_dom(j)]
                0 <= i < self.phys_len() && 0 <= j < other.phys_len()
                    ==> self.phys_dom(i).disjoint(other.phys_dom(j)),
    {
        use_type_invariant(&self);
        use_type_invariant(other);
        let ghost old_self = self;
        let tracked MemOwn { virt, mut phys, mapping, size, offset, npages, frame_addrs, is_pt } = self;
        if !(forall|i: int, j: int|
            #![trigger old_self.phys_dom(i), other.phys_dom(j)]
            0 <= i < old_self.phys_len() && 0 <= j < other.phys_len()
                ==> old_self.phys_dom(i).disjoint(other.phys_dom(j))) {
            let (i, j) = choose|i: int, j: int|
                #![trigger old_self.phys_dom(i), other.phys_dom(j)]
                0 <= i < old_self.phys_len() && 0 <= j < other.phys_len()
                    && !old_self.phys_dom(i).disjoint(other.phys_dom(j));
            let tracked tok = phys.tracked_borrow_mut(i);
            let tracked other_tok = other.phys.tracked_borrow(j);
            tok.is_disjoint(other_tok);
        }
        MemOwn { virt, phys, mapping, size, offset, npages, frame_addrs, is_pt }
    }
}

/// A more **General** memory permission that supports
/// shared mapping.
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub tracked struct GeneralPointsTo<T, A: ArchPagingMeta> {
    /// The bytes this permission owns, and every way in to them.
    tracked own: MemOwn<A>,
    /// Every pointer that reaches those bytes.
    ///
    /// Kept alongside the addresses because a pointer is more than an address:
    /// two pointers to one address may carry different provenance, and it is
    /// the pointer, not the address, that exec code writes through.
    ghost ptrs: Set<*mut T>,
    /// The vstd permission for one of the aliases, and the *only* source of
    /// this permission's value.
    ///
    /// A ghost `MemContents` field would be a claim about memory that any proof
    /// in this module could rewrite, since nothing constrains it; holding the
    /// resource instead means the value changes only when vstd's own write
    /// primitive changes it. Which alias it names does not matter -- they reach
    /// the same bytes -- so the other aliases are served by retargeting it
    /// ([`Self::borrow`], [`Self::borrow_mut`]).
    ///
    /// `None` exactly when no pointer reaches this memory at all: an unmapped
    /// frame has no virtual address for a `PointsTo` to name, and no contents
    /// its owner may assume anything about.
    tracked inner: Option<PointsTo<T>>,
}

#[verifier::reject_recursive_types(A)]
pub tracked struct PageWalkPath<'a, A: ArchPagingMeta> {
    ghost vaddr: usize,
    ghost max_level: PageLevel,
    tracked cr3: &'a RustRegisterPointsTo<Cr3>,
    // 0-> root table, 1-> next level, ...
    tracked entries: Seq<&'a GeneralPointsTo<PTEntry<A>, A>>,
}

impl<'a, A: ArchPagingMeta> PageWalkPath<'a, A> {
    spec fn root_pa(&self) -> usize {
        cr3_phys_addr::<A>(self.cr3.value())
    }

    /// Level the walk reads at depth `index`: the root's level, one level
    /// shallower for each step already taken.
    spec fn level_at(&self, index: int) -> PageLevel {
        PageLevel::from_nat((self.max_level.spec_depth() as int - index) as nat)
    }

    /// Base address of the table page the walk reads at depth `index`: the root
    /// for the first step, and afterwards the frame the *previous* entry points
    /// at.
    spec fn entry_pa_at(&self, index: int) -> usize {
        if index == 0 {
            self.root_pa()
        } else {
            self.entries[index - 1].value().page_frame_spec()
        }
    }

    /// Physical address of the word the walk reads at depth `index`.
    spec fn entry_slot_pa_at(&self, index: int) -> int {
        slot_addr::<A>(
            self.entry_pa_at(index),
            spec_entry_index::<A>(self.vaddr, self.level_at(index)) as int,
        )
    }

    /// Level the walk came to rest at.
    spec fn leaf_level(&self) -> PageLevel {
        self.level_at(self.entries.len() - 1)
    }

    spec fn is_leaf(&self) -> bool {
        self.entries.last().value().is_leaf_spec(self.leaf_level())
    }

    /// Offset the address falls at within the page the walk maps. Taken at the
    /// level the walk stopped, so a huge-page leaf keeps the bits a leaf-level
    /// page would have consumed on the way down.
    spec fn leaf_page_offset(&self) -> nat {
        self.vaddr as nat % pow2(level_shift::<A>(self.leaf_level().depth() as nat))
    }

    /// The physical address the walk maps `vaddr` to -- the address itself, not
    /// the frame containing it, so that a caller cannot silently drop the
    /// in-page offset.
    spec fn translate_to_phys_addr(&self) -> Option<usize> {
        if self.is_leaf() {
            Some(
                (self.entries.last().value().page_frame_spec() + self.leaf_page_offset()) as usize,
            )
        } else {
            None
        }
    }

    /// Whether this walk is a proof that `vaddr` translates to `pa`. Carries
    /// [`Self::inv`], so holding one is holding a well-formed walk.
    pub closed spec fn can_translate_to_phys_addr(&self, vaddr: usize, pa: usize) -> bool {
        &&& self.inv()
        &&& self.vaddr == vaddr
        &&& self.translate_to_phys_addr() == Some(pa)
    }

    spec fn inv(&self) -> bool {
        // A walk that read nothing is not a walk.
        &&& self.entries.len() > 0
        &&& self.max_level.spec_depth() as int + 1 >= self.entries.len() as int
        &&& forall|i: int|
            #![trigger self.entries[i]]
            0 <= i < self.entries.len() ==> {
                &&& self.entries[i].is_pt()
                &&& self.entries[i].is_init()
                // Which table page the entry lives in, and which slot of it.
                // The slot is what a recursive map makes load-bearing: the same
                // word answers to several virtual addresses, so only its
                // physical position identifies it.
                &&& self.entries[i].pinned_to_frame(self.entry_pa_at(i))
                &&& self.entries[i].is_at_phys_addr(self.entry_slot_pa_at(i))
            }
    }
}

impl<T, A: ArchPagingMeta> View for GeneralPointsTo<T, A> {
    type V = GeneralPointsToData<T, A>;

    closed spec fn view(&self) -> Self::V {
        GeneralPointsToData {
            ptrs: self.ptrs,
            opt_value: self.opt_value(),
            is_pt: self.own.is_pt(),
            frame_addrs: self.own.frames(),
        }
    }
}

impl<T, A: ArchPagingMeta> GeneralPointsTo<T, A> {
    /// The bytes this permission owns, and every way in to them.
    pub closed spec fn own(&self) -> MemOwn<A> {
        self.own
    }

    /// What this memory is, without its type: the shape both permissions share.
    pub closed spec fn shape(&self) -> MemShape<A> {
        self.own.shape()
    }

    /// The number of pages this memory occupies, one frame each.
    pub closed spec fn npages(&self) -> int {
        self.shape().npages()
    }

    /// Where this memory starts inside the `i`-th page it occupies: the offset
    /// in the first page, and the very start of every page after it.
    pub closed spec fn offset_in_page(&self, i: int) -> int {
        self.shape().offset_in_page(i)
    }

    /// How many bytes of this memory lie in the `i`-th page it occupies.
    pub closed spec fn bytes_in_page(&self, i: int) -> int {
        self.shape().bytes_in_page(i)
    }

    /// The page the alias `p` occupies at index `i`.
    pub closed spec fn vpage_at(&self, p: *mut T, i: int) -> int {
        self.shape().vpage_at(p@.addr as int, i)
    }

    /// The pages the alias `p` occupies.
    pub closed spec fn vpages_of(&self, p: *mut T) -> Set<int> {
        self.shape().vpages_of(p@.addr as int)
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        // The bytes are exactly those the pointers reach: an address is owned
        // if and only if some pointer of this permission starts there.
        &&& self.own.size() == size_of::<T>()
        &&& self.own.addrs() =~= self.ptrs.map(|p: *mut T| p@.addr as int)
        // The value is held, not asserted: memory that any pointer reaches is
        // memory whose vstd permission this one keeps, and the permission names
        // one of those pointers.
        &&& match self.inner {
            Some(pt) => self.ptrs.contains(pt.ptr()),
            None => self.ptrs =~= Set::empty(),
        }
    }

    #[verifier::inline]
    pub open spec fn ptrs(&self) -> Set<*mut T> {
        self@.ptrs
    }

    #[verifier::inline]
    pub open spec fn covers(&self, ptr: *mut T) -> bool {
        self@.ptrs.contains(ptr)
    }

    /// The value every alias reaches, read out of the permission this one
    /// holds. Memory nothing reaches has no readable contents.
    pub closed spec fn opt_value(&self) -> MemContents<T> {
        match self.inner {
            Some(pt) => pt.opt_value(),
            None => MemContents::Uninit,
        }
    }

    /// Whether the MMU reads this memory as part of a page table.
    #[verifier::inline]
    pub open spec fn is_pt(&self) -> bool {
        self@.is_pt && self.has_pinned_phys_addr()
    }

    /// What the page table records as backing `vpage`.
    ///
    /// Always `Some`: see [`Self::lemma_record_is_mapped`].
    ///
    /// No id hypothesis and no instance to match: the record for a page is
    /// pinned to [`Mapping::id_of_vpage`], so this permission's share and the
    /// table's are shares of the same ghost variable by construction.
    pub closed spec fn record_at(&self, p: *mut T, i: int) -> Option<
        VirtMapping<A::MinPageSize>,
    >
        recommends
            self.covers(p),
            0 <= i < self.npages(),
    {
        self.own.record_at(p@.addr as int, i)
    }

    /// Every page this memory occupies is mapped to something.
    ///
    /// Owning a permission is owning memory that can be read and written, so a
    /// page it runs through cannot be one that reaches no frame. Exposes the
    /// part of the type invariant callers need, since the invariant itself is
    /// `closed`.
    pub proof fn lemma_record_is_mapped(tracked &self, p: *mut T, i: int)
        requires
            self.covers(p),
            0 <= i < self.npages(),
        ensures
            self.record_at(p, i).is_some(),
    {
        use_type_invariant(self);
        assert(self.own.addrs().contains(p@.addr as int));
        self.own.lemma_record_is_mapped(p@.addr as int, i);
    }

    #[verifier::inline]
    pub open spec fn has_pinned_phys_addr(&self) -> bool {
        self@.frame_addrs.len() > 0
    }

    /// The frames backing this memory, in order.
    #[verifier::inline]
    pub open spec fn frames(&self) -> Seq<PhysFrame<A::MinPageSize>> {
        self@.frame_addrs
    }

    /// Whether this memory starts in the frame at `pa`.
    #[verifier::inline]
    pub open spec fn pinned_to_frame(&self, pa: usize) -> bool {
        &&& self.frames().len() > 0
        &&& self.frames()[0]@ == pa
    }

    /// Every alias sits at the same offset within its page: they are the same
    /// bytes, and translation replaces only the page part of an address. So the
    /// offset is a property of the memory, not of any one pointer, and does not
    /// have to be recorded separately.
    ///
    /// A lemma rather than a hypothesis: the offset is fixed by the type
    /// invariant, so no caller has to carry it around.
    pub proof fn lemma_aliases_share_page_offset(tracked &self)
        ensures
            forall|p: *mut T| #[trigger]
                self.covers(p) ==> page_offset_of::<A>(p@.addr as int) == self.shape().offset,
    {
        use_type_invariant(self);
        let tracked own = &self.own;
        own.lemma_aliases_share_page_offset();
        assert forall|p: *mut T| #[trigger] self.covers(p) implies page_offset_of::<A>(
            p@.addr as int,
        ) == self.shape().offset by {
            assert(self.own.addrs().contains(p@.addr as int));
        }
    }

    /// Whether `pa` is where this memory is: in its first frame, at the offset
    /// its aliases sit at.
    ///
    /// Stated as a predicate rather than as a `phys_addr()` function because
    /// unmapped memory has no alias to read the offset from -- it is somewhere
    /// in its frames and nothing narrows it further -- and a function would have
    /// to invent an answer there.
    pub open spec fn is_at_phys_addr(&self, pa: int) -> bool {
        &&& self.frames().len() > 0
        &&& self.frames()[0]@ == pa - page_offset_of::<A>(pa)
        &&& forall|p: *mut T| #[trigger]
            self@.ptrs.contains(p) ==> page_offset_of::<A>(p@.addr as int) == page_offset_of::<A>(
                pa,
            )
    }

    #[verifier::inline]
    pub open spec fn is_init(&self) -> bool {
        self.opt_value().is_init()
    }

    #[verifier::inline]
    pub open spec fn is_uninit(&self) -> bool {
        self.opt_value().is_uninit()
    }

    /// The value the pointers reach. Meaningless unless the memory is initialized.
    #[verifier::inline]
    pub open spec fn value(&self) -> T
        recommends
            self.is_init(),
    {
        self.opt_value().value()
    }

    /// Everything a borrow must leave alone.
    ///
    /// A borrow is a window on the value, not an opportunity to come back as a
    /// permission to *different* memory. The axioms below hand out a `&mut` to
    /// vstd, and whatever an axiom does not state is assumed arbitrary, so this
    /// is what stops a borrow from returning with fresh address tokens -- which
    /// would let two permissions claim one frame, and the address space's
    /// hand-each-address-out-once guarantee prove `false`.
    pub closed spec fn same_except_value(&self, other: &Self) -> bool {
        &&& self.own == other.own
        &&& self.ptrs == other.ptrs
        &&& self.inner is Some <==> other.inner is Some
    }

    /// **Assumption.** Holding the address tokens for an alias is holding the
    /// memory it reaches, so a vstd permission for it can be handed out.
    ///
    /// This cannot be derived: vstd's memory is indexed by address and knows
    /// nothing of an MMU, so nothing in it says that owning a virtual range and
    /// the physical range beneath it owns any bytes at all.
    pub axiom fn borrow(tracked &self, ptr: *mut T) -> (tracked ret: &PointsTo<T>)
        requires
            self.covers(ptr),
        ensures
            ret.ptr() == ptr,
            ret.opt_value() == self.opt_value(),
    ;

    /// **Assumption.** [`Self::borrow`] in mutable form, which is also where
    /// aliasing gets its meaning: every alias yields the *same* value, so a
    /// write through this one is what all the others then read.
    ///
    /// Stated on a mutable borrow rather than as a separate "resynchronize"
    /// step so that exec code can keep writing through an ordinary
    /// `&mut PointsTo`.
    pub axiom fn borrow_mut(tracked &mut self, ptr: *mut T) -> (tracked ret: &mut PointsTo<T>)
        requires
            self.covers(ptr),
        ensures
            ret.ptr() == ptr,
            ret.opt_value() == old(self).opt_value(),
            final(ret).opt_value() == final(self).opt_value(),
            final(self).same_except_value(old(self)),
    ;

    /// Two permissions never share an alias: an alias is owned by holding the
    /// [`VirtAddrTok`] for the range it spans, and the virtual address space
    /// hands each address out once.
    ///
    /// No longer an appeal to vstd -- this is the address space's own guarantee,
    /// the virtual counterpart of [`Self::is_disjoint_pfn`], and it takes `self`
    /// by value for the same reason: refuting a shared alias needs a mutable
    /// borrow of a token, and a token borrowed out of `self.virt` would have to
    /// satisfy this permission's invariant for an arbitrary final value.
    ///
    /// A zero-sized `T` spans no addresses and so is owned by nobody; the
    /// guarantee has nothing to say about it.
    pub proof fn is_disjoint(tracked self, tracked other: &Self) -> (tracked res: Self)
        requires
            size_of::<T>() != 0,
        ensures
            res == self,
            self.ptrs().disjoint(other.ptrs()),
    {
        use_type_invariant(&self);
        use_type_invariant(other);
        let ghost old_self = self;
        let tracked GeneralPointsTo { own, ptrs, inner } = self;
        let tracked own = own.is_disjoint(&other.own);
        assert forall|p: *mut T| #[trigger] old_self.ptrs().contains(p) implies !other.ptrs().contains(
            p,
        ) by {
            assert(old_self.own.addrs().contains(p@.addr as int));
            assert(other.own.addrs().contains(p@.addr as int) ==> false);
        }
        assert(old_self.ptrs().disjoint(other.ptrs()));
        GeneralPointsTo { own, ptrs, inner }
    }

    /// How many frame tokens this permission holds.
    pub closed spec fn phys_len(&self) -> nat {
        self.own.phys_len()
    }

    /// The physical addresses the `i`-th frame token owns.
    pub closed spec fn phys_dom(&self, i: int) -> Set<int> {
        self.own.phys_dom(i)
    }

    /// Two permissions never own the same physical byte: their frame tokens are
    /// drawn from one address space, and that space hands each address out once.
    ///
    /// Frame-level distinctness is deliberately *not* claimed -- two objects may
    /// share a frame at different offsets -- so the guarantee is stated on the
    /// address ranges themselves.
    ///
    /// Takes `self` by value rather than by `&mut`, because refuting a shared
    /// address needs a mutable borrow of a frame token, and a token borrowed out
    /// of `self.phys` would have to satisfy this permission's invariant for an
    /// arbitrary final value. Unpacking first puts the tokens in a plain `Seq`,
    /// which carries no invariant, and the invariant is re-established on the
    /// way out from the tokens' preserved domains.
    pub proof fn is_disjoint_pfn(tracked self, tracked other: &Self) -> (tracked res: Self)
        ensures
            res == self,
            forall|i: int, j: int|
                #![trigger self.phys_dom(i), other.phys_dom(j)]
                0 <= i < self.phys_len() && 0 <= j < other.phys_len()
                    ==> self.phys_dom(i).disjoint(other.phys_dom(j)),
    {
        use_type_invariant(&self);
        let tracked GeneralPointsTo { own, ptrs, inner } = self;
        let tracked own = own.is_disjoint_pfn(&other.own);
        GeneralPointsTo { own, ptrs, inner }
    }

    /// Borrow through a *translation* rather than through the alias set: the
    /// walk proves `ptr` reaches this memory, which is how a pointer the
    /// permission has never seen -- a recursive-map alias, say -- can still be
    /// used to write it.
    ///
    /// **Assumption.** This is the module's second and last model of the MMU:
    /// the walk is a proof about the *page tables*, and only the hardware turns
    /// that into a statement about which bytes a pointer reaches.
    ///
    /// `pa` is the address of the object, not of its frame. That is what makes
    /// the pairing sound: two objects in one frame have the same frame and
    /// different addresses, so a frame-level match would let a caller reach the
    /// wrong word through a correct walk.
    ///
    /// The alias is *not* added to [`Self::ptrs`]: it lasts exactly as long as
    /// the borrow of `walk`, and the walk borrows every entry permission along
    /// the path, so the mapping cannot be torn down while the alias is in use.
    /// A durable alias would have to be justified by something the permission
    /// keeps hold of -- otherwise unmapping `ptr` would leave a permission
    /// claiming a pointer that no longer reaches it -- and nesting the entry
    /// permissions cannot supply that, because a self-mapped root's permission
    /// would have to contain itself.
    pub axiom fn borrow_mut_via_pt(
        tracked &mut self,
        pa: usize,
        ptr: *mut T,
        tracked walk: &PageWalkPath<A>,
    ) -> (tracked ret: &mut PointsTo<T>)
        requires
            old(self).is_at_phys_addr(pa as int),
            walk.can_translate_to_phys_addr(ptr@.addr, pa),
        ensures
            ret.ptr() == ptr,
            ret.opt_value() == old(self).opt_value(),
            final(ret).opt_value() == final(self).opt_value(),
            final(self).same_except_value(old(self)),
    ;

    /// **Assumption.** [`Self::borrow`] by value: keeping one alias, and giving
    /// up every token in exchange for a plain vstd permission to it.
    pub axiom fn into_points_to(tracked self, ptr: *mut T) -> (tracked ret: PointsTo<T>)
        requires
            self.covers(ptr),
        ensures
            ret.ptr() == ptr,
            ret.opt_value() == self.opt_value(),
    ;
}

/// The same alias seen as a pointer to a different type: address and provenance
/// are what say which memory a pointer reaches, and retyping changes neither.
pub open spec fn retype_ptr<S, D>(p: *mut S) -> *mut D {
    spec_cast_ptr_to_thin_ptr::<S, D>(p)
}

/// [`GeneralPointsTo`] before it has a type: the same ownership of the same
/// bytes, with a size where the type would be.
///
/// Its `inner` is a [`PointsToRaw`], which grants no access to anything --
/// reading uninitialized memory is undefined behaviour, so vstd's raw
/// permission deliberately supports neither a read nor a write, and holding one
/// gives no pointer that `ptr_read`/`ptr_write` will accept. Memory in this
/// form is *owned but not yet usable*, which is what a frame just handed to the
/// OS is, and [`Self::into_typed`] is the only way out.
#[verifier::reject_recursive_types(A)]
pub tracked struct GeneralPointsToRaw<A: ArchPagingMeta> {
    /// The bytes this permission owns, and every way in to them.
    tracked own: MemOwn<A>,
    /// Every untyped pointer that reaches those bytes.
    ghost ptrs: Set<*mut u8>,
    /// The raw permission for one of the aliases, and the reason this is
    /// ownership at all rather than a claim about bytes nobody holds.
    tracked inner: Option<PointsToRaw>,
}

impl<A: ArchPagingMeta> GeneralPointsToRaw<A> {
    /// The bytes this permission owns, and every way in to them.
    pub closed spec fn own(&self) -> MemOwn<A> {
        self.own
    }

    /// What this memory is: the shape it shares with [`GeneralPointsTo`].
    pub closed spec fn shape(&self) -> MemShape<A> {
        self.own.shape()
    }

    /// Every untyped pointer that reaches this memory.
    pub closed spec fn ptrs(&self) -> Set<*mut u8> {
        self.ptrs
    }

    pub open spec fn covers(&self, ptr: *mut u8) -> bool {
        self.ptrs().contains(ptr)
    }

    /// How many bytes this memory spans.
    pub closed spec fn size(&self) -> nat {
        self.own.size()
    }

    /// The frames backing this memory, in order.
    pub closed spec fn frames(&self) -> Seq<PhysFrame<A::MinPageSize>> {
        self.own.frames()
    }

    pub open spec fn has_pinned_phys_addr(&self) -> bool {
        self.frames().len() > 0
    }

    /// Whether the MMU reads this memory as part of a page table.
    pub closed spec fn is_pt(&self) -> bool {
        self.own.is_pt()
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        &&& self.own.addrs() =~= self.ptrs.map(|p: *mut u8| p@.addr as int)
        // The bytes are held, not asserted, exactly as in the typed permission;
        // the raw permission spans one alias's range and carries that alias's
        // provenance, so retyping it lands back on a pointer this permission
        // owns.
        &&& match self.inner {
            Some(raw) => exists|p: *mut u8|
                #![trigger self.ptrs.contains(p)]
                self.ptrs.contains(p) && raw.is_range(p@.addr as int, self.own.size() as int)
                    && raw.provenance() == p@.provenance,
            None => self.ptrs =~= Set::empty(),
        }
    }

    /// Give the bytes a type.
    ///
    /// Nothing about the *memory* changes -- the same tokens, the same frames,
    /// the same records, the same addresses -- so this is a proof, not an
    /// assumption. What changes is that the permission now names a `T` and can
    /// therefore be read and written, which is why the size and alignment
    /// obligations sit here: they are what makes a `T` at these addresses a
    /// meaningful object rather than a reinterpretation of somebody's bytes.
    ///
    /// The result is uninitialized, because raw memory has no value to inherit.
    pub proof fn into_typed<T>(tracked self) -> (tracked ret: GeneralPointsTo<T, A>)
        requires
            size_of::<T>() == self.size(),
            size_of::<T>() != 0,
            forall|p: *mut u8| #[trigger]
                self.ptrs().contains(p) ==> p@.addr as int % align_of::<T>() as int == 0,
        ensures
            ret.ptrs() =~= self.ptrs().map(|p: *mut u8| retype_ptr::<u8, T>(p)),
            ret.own() == self.own(),
            ret.is_uninit(),
    {
        broadcast use vstd::raw_ptr::group_raw_ptr_axioms;

        use_type_invariant(&self);
        let ghost old_self = self;
        let tracked GeneralPointsToRaw { own, ptrs, inner } = self;
        let ghost new_ptrs = ptrs.map(|p: *mut u8| retype_ptr::<u8, T>(p));
        let ghost new_addrs = new_ptrs.map(|q: *mut T| q@.addr as int);
        let ghost old_addrs = ptrs.map(|p: *mut u8| p@.addr as int);
        assert(new_addrs =~= old_addrs) by {
            assert forall|a: int| #[trigger] new_addrs.contains(a) implies old_addrs.contains(a) by {
                let q = choose|q: *mut T| new_ptrs.contains(q) && q@.addr as int == a;
                let p = choose|p: *mut u8| ptrs.contains(p) && retype_ptr::<u8, T>(p) == q;
                assert(old_addrs.contains(p@.addr as int));
            }
            assert forall|a: int| #[trigger] old_addrs.contains(a) implies new_addrs.contains(a) by {
                let p = choose|p: *mut u8| ptrs.contains(p) && p@.addr as int == a;
                assert(new_ptrs.contains(retype_ptr::<u8, T>(p)));
                assert(new_addrs.contains(a));
            }
        }
        let tracked inner = match inner {
            Some(raw) => {
                let ghost p = choose|p: *mut u8|
                    #![trigger old_self.ptrs.contains(p)]
                    old_self.ptrs.contains(p) && raw.is_range(p@.addr as int, own.size() as int)
                        && raw.provenance() == p@.provenance;
                assert(old_self.ptrs().contains(p));
                let tracked pt = raw.into_typed::<T>(p@.addr);
                assert(pt.ptr() == retype_ptr::<u8, T>(p));
                assert(new_ptrs.contains(pt.ptr()));
                Some(pt)
            },
            None => None,
        };
        GeneralPointsTo { own, ptrs: new_ptrs, inner }
    }
}

/// Permission to memory named by **where it is**, not by how to reach it.
///
/// The restriction of [`GeneralPointsTo`] to memory that is pinned: the frame
/// backing it cannot change, so its physical address is a stable name for it.
/// That is the only name some memory has -- a frame the OS owns but has not
/// mapped is reachable through no pointer at all, and [`Self::ptrs`] is empty
/// for it.
///
/// Where [`GeneralPointsTo`] knows every way *in* to memory whose location may
/// move, this knows where the memory *is* however many ways in there turn out
/// to be.
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub tracked struct PhysPointsTo<T, A: ArchPagingMeta> {
    inner: GeneralPointsTo<T, A>,
}

impl<T, A: ArchPagingMeta> View for PhysPointsTo<T, A> {
    type V = GeneralPointsToData<T, A>;

    closed spec fn view(&self) -> Self::V {
        self.inner@
    }
}

impl<T, A: ArchPagingMeta> PhysPointsTo<T, A> {
    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        self.inner.has_pinned_phys_addr()
    }

    /// The frames this memory sits in, in order.
    #[verifier::inline]
    pub open spec fn frames(&self) -> Seq<PhysFrame<A::MinPageSize>> {
        self@.frame_addrs
    }

    /// The frame this memory starts in.
    #[verifier::inline]
    pub open spec fn start_frame(&self) -> PhysFrame<A::MinPageSize>
        recommends
            self.frames().len() > 0,
    {
        self.frames()[0]
    }

    #[verifier::inline]
    pub open spec fn pinned_to_frame(&self, pa: usize) -> bool {
        &&& self.frames().len() > 0
        &&& self.frames()[0]@ == pa
    }

    /// Whether `pa` is where this memory is. See
    /// [`GeneralPointsTo::is_at_phys_addr`] for why this is a predicate and not
    /// an address-valued function.
    #[verifier::inline]
    pub open spec fn is_at_phys_addr(&self, pa: int) -> bool {
        &&& self.frames().len() > 0
        &&& self.frames()[0]@ == pa - page_offset_of::<A>(pa)
        &&& forall|p: *mut T| #[trigger]
            self@.ptrs.contains(p) ==> page_offset_of::<A>(p@.addr as int) == page_offset_of::<A>(
                pa,
            )
    }

    /// Every virtual pointer that reaches this memory. Empty when nothing maps
    /// it yet.
    #[verifier::inline]
    pub open spec fn ptrs(&self) -> Set<*mut T> {
        self@.ptrs
    }

    /// Whether no virtual address translates here.
    #[verifier::inline]
    pub open spec fn is_unmapped(&self) -> bool {
        self@.ptrs === Set::empty()
    }

    #[verifier::inline]
    pub open spec fn covers(&self, ptr: *mut T) -> bool {
        self@.ptrs.contains(ptr)
    }

    /// Whether the MMU reads this memory as part of a page table.
    #[verifier::inline]
    pub open spec fn is_pt(&self) -> bool {
        self@.is_pt
    }

    #[verifier::inline]
    pub open spec fn opt_value(&self) -> MemContents<T> {
        self@.opt_value
    }

    #[verifier::inline]
    pub open spec fn is_init(&self) -> bool {
        self.opt_value().is_init()
    }

    #[verifier::inline]
    pub open spec fn is_uninit(&self) -> bool {
        self.opt_value().is_uninit()
    }

    #[verifier::inline]
    pub open spec fn value(&self) -> T
        recommends
            self.is_init(),
    {
        self.opt_value().value()
    }

    /// Pinned memory is physical memory. The precondition is the whole
    /// difference between the two permissions.
    pub proof fn new(tracked inner: GeneralPointsTo<T, A>) -> (tracked ret: PhysPointsTo<T, A>)
        requires
            inner.has_pinned_phys_addr(),
        ensures
            ret@ == inner@,
    {
        PhysPointsTo { inner }
    }

    /// Forget that the memory is pinned.
    pub proof fn into_general(tracked self) -> (tracked ret: GeneralPointsTo<T, A>)
        ensures
            ret@ == self@,
    {
        self.inner
    }

    /// Read the underlying permission without giving up the pinning.
    pub proof fn borrow_general(tracked &self) -> (tracked ret: &GeneralPointsTo<T, A>)
        ensures
            ret@ == self@,
    {
        &self.inner
    }
}

} // verus!
