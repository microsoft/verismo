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
    /// The frames it sits in, in order, when it is pinned; empty when it is not.
    pub frame_addrs: Seq<PhysFrame<A::MinPageSize>>,
}

impl<A: ArchPagingMeta> MemShape<A> {
    /// The number of pages this memory occupies, one frame each.
    pub open spec fn npages(&self) -> int {
        self.frame_addrs.len() as int
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

    /// How many bytes of this memory lie in the `i`-th page it occupies.
    ///
    /// A single page holds all of it. Otherwise the first page holds whatever
    /// follows the offset, the last holds the remainder, and the pages between
    /// are full.
    pub open spec fn bytes_in_page(&self, i: int) -> int {
        let first = page_size::<A>() - self.offset;
        if self.npages() == 1 {
            self.size as int
        } else if i == 0 {
            first
        } else if i < self.npages() - 1 {
            page_size::<A>() as int
        } else {
            self.size - first - (i - 1) * page_size::<A>()
        }
    }

    /// The page an alias at `addr` occupies at index `i`.
    pub open spec fn vpage_at(&self, addr: int, i: int) -> int {
        page_start_of::<A>(addr) + i * page_size::<A>()
    }

    /// The pages an alias at `addr` occupies.
    pub open spec fn vpages_of(&self, addr: int) -> Set<int> {
        Set::range(0, self.npages()).map(|i: int| self.vpage_at(addr, i))
    }

    /// The bytes account for themselves: each page holds a whole number of them
    /// and no more than a page's worth, and the first page has room for the
    /// offset.
    pub open spec fn wf(&self) -> bool {
        &&& self.offset < page_size::<A>()
        &&& forall|i: int| 0 <= i < self.npages() ==> 0 <= #[trigger] self.bytes_in_page(i)
            <= page_size::<A>()
    }

    /// One physical token per page, covering the bytes this memory owns in that
    /// page's frame.
    pub open spec fn phys_wf(&self, phys: Seq<PhysAddrTok>) -> bool {
        &&& phys.len() == self.frame_addrs.len()
        &&& forall|i: int|
            #![trigger phys[i], self.frame_addrs[i]]
            0 <= i < self.npages() ==> phys[i].is_range(
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

/// A more **General** memory permission that supports
/// shared mapping.
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub tracked struct GeneralPointsTo<T, A: ArchPagingMeta> {
    /// One address token per alias. Owning the virtual range a pointer spans
    /// is what makes that pointer this permission's to use, and the tokens come
    /// from one address space, so no other permission can claim the same
    /// address.
    tracked virt: Map<*mut T, VirtAddrTok>,
    /// One address token per frame the memory occupies.
    tracked phys: Seq<PhysAddrTok>,
    /// A share of the record for each virtual page an alias starts in, sized by
    /// how much of that page this permission owns. A share is enough to read
    /// what the page maps to, and not enough to change it, so the table cannot
    /// repoint a page while any permission into it is outstanding, and this
    /// permission cannot claim a mapping the table does not agree it installed.
    ///
    /// Keyed by page, and the ids are [`Mapping::id_of_vpage`], so no id has to
    /// travel with the permission for the two sides to be comparable.
    tracked mapping: Map<*mut T, Seq<Mapping<A>>>,
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
    ghost frame_addrs: Seq<PhysFrame<A::MinPageSize>>,
    ghost offset: usize,
    ghost is_pt: bool,
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
            ptrs: self.virt.dom(),
            opt_value: self.opt_value(),
            is_pt: self.is_pt,
            frame_addrs: self.frame_addrs,
        }
    }
}

impl<T, A: ArchPagingMeta> GeneralPointsTo<T, A> {
    /// What this memory is, without its type: the shape both permissions share.
    pub closed spec fn shape(&self) -> MemShape<A> {
        MemShape { size: size_of::<T>(), offset: self.offset, frame_addrs: self.frame_addrs }
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
        &&& self.shape().wf()
        &&& self.shape().phys_wf(self.phys)
        &&& self.aliases_share_page_offset()
        &&& forall|p: *mut T| #[trigger]
            self.virt.dom().contains(p) ==> self.shape().alias_wf(self.virt[p], p@.addr as int)
        // The value is held, not asserted: memory that any pointer reaches is
        // memory whose vstd permission this one keeps, and the permission names
        // one of those pointers.
        &&& match self.inner {
            Some(pt) => self.virt.dom().contains(pt.ptr()),
            None => self.virt.dom() =~= Set::empty(),
        }
        // One record per page per alias, keyed by alias rather than by page, so
        // two aliases running through one page hold a share each and the shares
        // add up on their own.
        &&& self.mapping.dom() =~= self.virt.dom()
        &&& forall|p: *mut T| #[trigger]
            self.mapping.dom().contains(p) ==> self.shape().records_wf(
                self.mapping[p],
                p@.addr as int,
                self.has_pinned_phys_addr(),
            )
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
        self.mapping[p][i].frame()
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
    pub open spec fn aliases_share_page_offset(&self) -> bool {
        forall|p: *mut T, q: *mut T|
            #![trigger self@.ptrs.contains(p), self@.ptrs.contains(q)]
            self@.ptrs.contains(p) && self@.ptrs.contains(q) ==> page_offset_of::<A>(p@.addr as int)
                == page_offset_of::<A>(q@.addr as int)
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
        &&& self.virt == other.virt
        &&& self.phys == other.phys
        &&& self.mapping == other.mapping
        &&& self.frame_addrs == other.frame_addrs
        &&& self.offset == other.offset
        &&& self.is_pt == other.is_pt
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
        broadcast use vstd::set_lib::range_set_properties;

        use_type_invariant(&self);
        use_type_invariant(other);
        let ghost old_self = self;
        let tracked GeneralPointsTo {
            mut virt,
            phys,
            mapping,
            inner,
            frame_addrs,
            offset,
            is_pt,
        } = self;
        if !old_self.ptrs().disjoint(other.ptrs()) {
            let ghost p = choose|p: *mut T|
                #![trigger other.ptrs().contains(p)]
                old_self.ptrs().contains(p) && other.ptrs().contains(p);
            let tracked tok = virt.tracked_borrow_mut(p);
            let tracked other_tok = other.virt.tracked_borrow(p);
            tok.is_disjoint(other_tok);
            let ghost addr = p@.addr as int;
            let ghost n = size_of::<T>() as int;
            assert(old_self.virt[p].dom() =~= Set::range(addr, addr + n));
            assert(other.virt[p].dom() =~= Set::range(addr, addr + n));
            assert(Set::range(addr, addr + n).contains(addr));
            assert(false);
        }
        GeneralPointsTo { virt, phys, mapping, inner, frame_addrs, offset, is_pt }
    }

    /// How many frame tokens this permission holds.
    pub closed spec fn phys_len(&self) -> nat {
        self.phys.len()
    }

    /// The physical addresses the `i`-th frame token owns.
    pub closed spec fn phys_dom(&self, i: int) -> Set<int> {
        self.phys[i].dom()
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
            res@ == self@,
            res.phys_len() == self.phys_len(),
            forall|i: int| #[trigger] res.phys_dom(i) == self.phys_dom(i),
            forall|i: int, j: int|
                #![trigger self.phys_dom(i), other.phys_dom(j)]
                0 <= i < self.phys_len() && 0 <= j < other.phys_len()
                    ==> self.phys_dom(i).disjoint(other.phys_dom(j)),
    {
        use_type_invariant(&self);
        use_type_invariant(other);
        let ghost old_self = self;
        let tracked GeneralPointsTo { virt, mut phys, mapping, inner, frame_addrs, offset, is_pt } = self;
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
        GeneralPointsTo { virt, phys, mapping, inner, frame_addrs, offset, is_pt }
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
    /// One address token per alias, keyed by the untyped pointer.
    tracked virt: Map<*mut u8, VirtAddrTok>,
    /// One address token per frame the memory occupies.
    tracked phys: Seq<PhysAddrTok>,
    /// A share of the record of every page each alias runs through.
    tracked mapping: Map<*mut u8, Seq<Mapping<A>>>,
    /// The raw permission for one of the aliases, and the reason this is
    /// ownership at all rather than a claim about bytes nobody holds.
    tracked inner: Option<PointsToRaw>,
    ghost size: nat,
    ghost frame_addrs: Seq<PhysFrame<A::MinPageSize>>,
    ghost offset: usize,
    ghost is_pt: bool,
}

impl<A: ArchPagingMeta> GeneralPointsToRaw<A> {
    /// What this memory is: the shape it shares with [`GeneralPointsTo`].
    pub closed spec fn shape(&self) -> MemShape<A> {
        MemShape { size: self.size, offset: self.offset, frame_addrs: self.frame_addrs }
    }

    /// Every untyped pointer that reaches this memory.
    pub closed spec fn ptrs(&self) -> Set<*mut u8> {
        self.virt.dom()
    }

    pub open spec fn covers(&self, ptr: *mut u8) -> bool {
        self.ptrs().contains(ptr)
    }

    /// How many bytes this memory spans.
    pub closed spec fn size(&self) -> nat {
        self.size
    }

    /// The frames backing this memory, in order.
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

    /// Every alias sits at the same offset within its page. See
    /// [`GeneralPointsTo::aliases_share_page_offset`].
    pub open spec fn aliases_share_page_offset(&self) -> bool {
        forall|p: *mut u8, q: *mut u8|
            #![trigger self.ptrs().contains(p), self.ptrs().contains(q)]
            self.ptrs().contains(p) && self.ptrs().contains(q) ==> page_offset_of::<A>(
                p@.addr as int,
            ) == page_offset_of::<A>(q@.addr as int)
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        &&& self.shape().wf()
        &&& self.shape().phys_wf(self.phys)
        &&& self.aliases_share_page_offset()
        &&& forall|p: *mut u8| #[trigger]
            self.virt.dom().contains(p) ==> self.shape().alias_wf(self.virt[p], p@.addr as int)
        // The bytes are held, not asserted, exactly as in the typed permission;
        // the raw permission spans one alias's range and carries that alias's
        // provenance, so retyping it lands back on a pointer this permission
        // owns.
        &&& match self.inner {
            Some(raw) => exists|p: *mut u8|
                #![trigger self.virt.dom().contains(p)]
                self.virt.dom().contains(p) && raw.is_range(p@.addr as int, self.size as int)
                    && raw.provenance() == p@.provenance,
            None => self.virt.dom() =~= Set::empty(),
        }
        &&& self.mapping.dom() =~= self.virt.dom()
        &&& forall|p: *mut u8| #[trigger]
            self.mapping.dom().contains(p) ==> self.shape().records_wf(
                self.mapping[p],
                p@.addr as int,
                self.has_pinned_phys_addr(),
            )
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
                self.ptrs().contains(p) ==> p@.addr as int % align_of::<T>() as int
                    == 0,
        ensures
            ret.ptrs() =~= self.ptrs().map(|p: *mut u8| retype_ptr::<u8, T>(p)),
            ret.frames() == self.frames(),
            ret@.is_pt == self.is_pt(),
            ret.is_uninit(),
    {
        broadcast use vstd::raw_ptr::group_raw_ptr_axioms;

        use_type_invariant(&self);
        let ghost old_self = self;
        let tracked GeneralPointsToRaw {
            virt,
            phys,
            mapping,
            inner,
            size,
            frame_addrs,
            offset,
            is_pt,
        } = self;
        let ghost key_map = Map::<*mut T, *mut u8>::new(
            virt.dom().map(|p: *mut u8| retype_ptr::<u8, T>(p)),
            |q: *mut T| retype_ptr::<T, u8>(q),
        );
        assert forall|q: *mut T| #[trigger] old_self.ptrs().contains(retype_ptr::<T, u8>(q)) implies
        retype_ptr::<u8, T>(retype_ptr::<T, u8>(q)) == q by {}
        let tracked virt = Map::tracked_map_keys(virt, key_map);
        let tracked mapping = Map::tracked_map_keys(mapping, key_map);
        let tracked inner = match inner {
            Some(raw) => {
                let ghost p = choose|p: *mut u8|
                    #![trigger old_self.ptrs().contains(p)]
                    old_self.ptrs().contains(p) && raw.is_range(p@.addr as int, size as int)
                        && raw.provenance() == p@.provenance;
                assert(old_self.ptrs().contains(p));
                Some(raw.into_typed::<T>(p@.addr))
            },
            None => None,
        };
        GeneralPointsTo { virt, phys, mapping, inner, frame_addrs, offset, is_pt }
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
