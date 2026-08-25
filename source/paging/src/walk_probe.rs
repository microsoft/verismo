//! A model of content, physical frames, page tables, and virtual aliases, as a tokenized state
//! machine -- with the page table modelled as a *tree*, walked from a frame, exactly as hardware
//! walks it.
// The state machine macro names its module after the machine, so the module inherits a type's
// casing. vstd does the same for its own machines.
#![allow(non_snake_case)]
use core::marker::PhantomData;

use vstd::arithmetic::div_mod::{lemma_div_by_multiple, lemma_fundamental_div_mod};
use vstd::arithmetic::mul::lemma_mul_is_commutative;
use vstd::arithmetic::power::pow;
use vstd::prelude::*;

use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlagsSpec};
use crate::structs::entry::{lemma_pgtbl_idx_step, pgtbl_idx, PTEntry};
use crate::structs::level::PageLevel;
use crate::structs::ptpage::PTPage;
use crate::structs::sizes::PageSize;
use verus_state_machines_macros::tokenized_state_machine;

verus! {

/// The identity of an object: the base id of a run of words allocated together.
#[derive(PartialEq, Eq, Structural)]
pub struct ObjId(pub nat);

/// The identity of one machine word, inside some object.
#[derive(PartialEq, Eq, Structural)]
pub struct WordId(pub nat);

/// A physical frame number.
#[derive(PartialEq, Eq, Structural)]
pub struct FrameId(pub nat);

/// The base virtual address of page number `vpage`.
pub open spec fn page_base<A: ArchPagingMeta>(vpage: nat) -> nat {
    vpage * (<A::MinPageSize as PageSize>::SIZE as nat)
}

/// Id of the word an entry occupies.
pub open spec fn entry_id<A: ArchPagingMeta>(table: ObjId, vpage: nat, level: PageLevel) -> WordId {
    WordId((table.0 + pgtbl_idx::<A>(page_base::<A>(vpage), level) as nat) as nat)
}

/// The part of physical memory a page-table walk reads: word contents, writable or frozen, and
/// which objects live in each frame.
pub struct PhyMemView<A: ArchPagingMeta> {
    pub data: Map<WordId, usize>,
    pub frozen: Map<WordId, usize>,
    pub frame_to_objs: Map<FrameId, Set<ObjId>>,
    pub marker: PhantomData<A>,
}

impl<A: ArchPagingMeta> PhyMemView<A> {
    /// A word, wherever it lives. Content is writable or frozen, never both.
    pub open spec fn word_at(&self, c: WordId) -> usize {
        if self.data.dom().contains(c) {
            self.data[c]
        } else {
            self.frozen[c]
        }
    }

    /// The object living in a frame. A walk lands on a frame but must go on reading words. Well
    /// defined only because page table pages are their frame's sole residents.
    pub open spec fn resident(&self, frame: FrameId) -> ObjId {
        self.frame_to_objs[frame].choose()
    }

    /// Id of the entry a walk of `vpage` reads while standing in `frame` at `level`.
    pub open spec fn path_id(
        &self,
        frame: FrameId,
        vpage: nat,
        level: PageLevel,
    ) -> WordId {
        entry_id::<A>(self.resident(frame), vpage, level)
    }

    /// Where a walk of `vpage` comes to rest, starting from the page `frame` at `level`: the page it
    /// ends up standing in, and the level that page sits at.
    ///
    /// A function of memory alone, and keyed on the level rather than on the page, so a frame that
    /// is reached at two levels -- a self-mapped table -- gets a separate answer at each. The walk
    /// stops where `spec_child` runs out, because below the leaf there is nothing to descend into:
    /// the hardware reads bit 7 of a level 0 entry as PAT rather than PS, so an entry that looks
    /// like a table pointer there is a mapping.
    pub open spec fn walk_leaf_ptbl(
        &self,
        frame: FrameId,
        level: PageLevel,
        vpage: nat,
    ) -> (FrameId, PageLevel)
        decreases level.depth(),
    {
        let e = PTEntry::<A>::spec_from_bits(self.word_at(self.path_id(frame, vpage, level)));
        match level.spec_child() {
            Option::None => (frame, level),
            Option::Some(child) => if e.is_table_spec(level) {
                self.walk_leaf_ptbl(FrameId(e.page_frame_spec() as nat), child, vpage)
            } else {
                (frame, level)
            },
        }
    }

    /// The entry a walk of `vpage` comes to rest on, and the level it rested at.
    ///
    /// The level is part of the answer because it is what the entry's bits mean: the same word is a
    /// huge page at one level and a table pointer at another.
    pub open spec fn walk_leaf_entry(
        &self,
        frame: FrameId,
        level: PageLevel,
        vpage: nat,
    ) -> (PTEntry<A>, PageLevel) {
        let rest = self.walk_leaf_ptbl(frame, level, vpage);
        (
            PTEntry::<A>::spec_from_bits(self.word_at(self.path_id(rest.0, vpage, rest.1))),
            rest.1,
        )
    }

    /// Whether `c` is one of the entries a walk of `vpage` reads, starting from `frame` at `level`.
    /// Changing anything else cannot change where `vpage` leads, which is what [`lemma_translate_local`]
    /// states and every transition leans on.
    pub open spec fn on_walk_path(
        &self,
        frame: FrameId,
        level: PageLevel,
        vpage: nat,
        c: WordId,
    ) -> bool
        decreases level.depth(),
    {
        let id = self.path_id(frame, vpage, level);
        let e = PTEntry::<A>::spec_from_bits(self.word_at(id));
        ||| c == id
        ||| match level.spec_child() {
            Option::None => false,
            Option::Some(child) => e.is_table_spec(level) && self.on_walk_path(
                FrameId(e.page_frame_spec() as nat),
                child,
                vpage,
                c,
            ),
        }
    }

    /// Whether the walk stands in `f` at some point on its way down from `frame` at `level`.
    pub open spec fn walk_visits(
        &self,
        frame: FrameId,
        level: PageLevel,
        vpage: nat,
        f: FrameId,
    ) -> bool
        decreases level.depth(),
    {
        let e = PTEntry::<A>::spec_from_bits(self.word_at(self.path_id(frame, vpage, level)));
        ||| f == frame
        ||| match level.spec_child() {
            Option::None => false,
            Option::Some(child) => e.is_table_spec(level) && self.walk_visits(
                FrameId(e.page_frame_spec() as nat),
                child,
                vpage,
                f,
            ),
        }
    }

    /// The frame `vpage` translates to: the whole walk, from `cr3` down to where it comes to rest.
    /// Consults nothing but memory, so agreeing with it is a real obligation on the words stored.
    pub open spec fn translate(
        &self,
        cr3: FrameId,
        top: PageLevel,
        vpage: nat,
    ) -> Option<FrameId> {
        let rest = self.walk_leaf_entry(cr3, top, vpage);
        let e = rest.0;
        let l = rest.1;
        if e.is_leaf_spec(l) {
            Some(FrameId((e.page_frame_spec() as nat + leaf_offset::<A>(vpage, l)) as nat))
        } else {
            Option::None
        }
    }

    /// Where a walk of `vpage` comes to rest: the entry it stops on, and the level it read that
    /// entry at. Total, because a walk always rests somewhere -- at worst on the entry the root
    /// page holds for `vpage`.
    ///
    /// The level belongs here for the same reason it belongs in [`walk_leaf_entry`]: it is what
    /// the entry's bits mean, and what decides how much of `vpage` the entry maps.
    pub open spec fn resting_slot(
        &self,
        cr3: FrameId,
        top: PageLevel,
        vpage: nat,
    ) -> (WordId, PageLevel) {
        let rest = self.walk_leaf_ptbl(cr3, top, vpage);
        (self.path_id(rest.0, vpage, rest.1), rest.1)
    }

    /// Whether a walk of `vpage` from `frame` at `level` runs over a bare table skeleton: it
    /// stays inside `frames` and maps nothing.
    ///
    /// Keyed on the walk rather than stated entry by entry, because whether an entry maps a page
    /// is not a property of the entry alone -- the same word is a table pointer at one level and
    /// a mapping at another, so only the level a walk reads it at decides.
    pub open spec fn skeleton_walk(
        &self,
        frames: Set<FrameId>,
        frame: FrameId,
        level: PageLevel,
        vpage: nat,
    ) -> bool
        decreases level.depth(),
    {
        let e = PTEntry::<A>::spec_from_bits(self.word_at(self.path_id(frame, vpage, level)));
        &&& !e.is_leaf_spec(level)
        &&& match level.spec_child() {
            Option::None => true,
            Option::Some(child) => e.is_table_spec(level) ==> {
                &&& frames.contains(FrameId(e.page_frame_spec() as nat))
                &&& self.skeleton_walk(frames, FrameId(e.page_frame_spec() as nat), child, vpage)
            },
        }
    }
}

/// Pages covered by a leaf at `level` are consecutive frames starting at the entry's frame.
pub open spec fn leaf_offset<A: ArchPagingMeta>(vpage: nat, level: PageLevel) -> nat 
recommends
    PTPage::<A>::count() > 0
{
    (vpage % (pow(PTPage::<A>::count() as int, level.depth() as nat) as nat)) as nat
}

/// Word an absent entry holds.
pub open spec fn absent_word() -> usize {
    0
}

/// Word an entry mapping `frame` holds.
pub open spec fn leaf_word<A: ArchPagingMeta>(frame: usize) -> usize {
    (frame & A::spec_address_mask()) | A::PTFlags::spec_present_bit()
}

/// Word an entry pointing at the table page in `frame` holds.
pub open spec fn table_word<A: ArchPagingMeta>(frame: usize) -> usize {
    (frame & A::spec_address_mask()) | A::PTFlags::spec_present_bit()
        | A::PTFlags::spec_escrow_bit()
}

/// A frame an entry can name: aligned into the address field and untagged, so decoding recovers it.
pub open spec fn encodable<A: ArchPagingMeta>(frame: usize) -> bool {
    &&& frame & !A::spec_address_mask() == 0
    &&& frame & A::spec_private_mask() == 0
}

pub proof fn lemma_absent_word<A: ArchPagingMeta>()
    ensures
        !PTEntry::<A>::spec_from_bits(absent_word()).present_spec(),
{
    A::PTFlags::lemma_flag_bits_wf();
    PTEntry::<A>::lemma_view_of_bits(absent_word());
    let pb = A::PTFlags::spec_present_bit();
    assert(0usize & pb == 0) by (bit_vector);
}

pub proof fn lemma_leaf_word<A: ArchPagingMeta>(frame: usize)
    requires
        encodable::<A>(frame),
    ensures
        PTEntry::<A>::spec_from_bits(leaf_word::<A>(frame)).is_leaf_spec(PageLevel::from_nat(0)),
        PTEntry::<A>::spec_from_bits(leaf_word::<A>(frame)).page_frame_spec() == frame,
{
    PageLevel::lemma_leaf_cases(PageLevel::from_nat(0));
    A::lemma_pte_masks_wf();
    A::PTFlags::lemma_flag_bits_wf();
    let am = A::spec_address_mask();
    let pm = A::spec_private_mask();
    let pb = A::PTFlags::spec_present_bit();
    let eb = A::PTFlags::spec_escrow_bit();
    let w = leaf_word::<A>(frame);
    PTEntry::<A>::lemma_view_of_bits(w);
    assert((am & pb == 0 && am & eb == 0 && eb & pb == 0 && pb != 0 && frame & !am == 0 && frame
        & pm == 0 && w == (frame & am) | pb) ==> (w & pb != 0 && w & eb == 0 && w & am & !pm
        == frame)) by (bit_vector);
}

pub proof fn lemma_table_word<A: ArchPagingMeta>(frame: usize, level: PageLevel)
    requires
        encodable::<A>(frame),
        level.depth() > 0,
    ensures
        PTEntry::<A>::spec_from_bits(table_word::<A>(frame)).is_table_spec(level),
        PTEntry::<A>::spec_from_bits(table_word::<A>(frame)).page_frame_spec() == frame,
{
    PageLevel::lemma_nonzero_not_leaf(level);
    PageLevel::lemma_leaf_cases(level);
    assert(!level.is_leaf());
    A::lemma_pte_masks_wf();
    A::PTFlags::lemma_flag_bits_wf();
    let am = A::spec_address_mask();
    let pm = A::spec_private_mask();
    let pb = A::PTFlags::spec_present_bit();
    let hb = A::PTFlags::spec_huge_bit();
    let eb = A::PTFlags::spec_escrow_bit();
    let w = table_word::<A>(frame);
    PTEntry::<A>::lemma_view_of_bits(w);
    assert((am & pb == 0 && am & hb == 0 && am & eb == 0 && pb & hb == 0 && eb & hb == 0 && pb != 0
        && eb != 0 && frame & !am == 0 && frame & pm == 0 && w == (frame & am) | pb | eb) ==> (w & pb
        != 0 && w & hb == 0 && w & eb != 0 && w & am & !pm == frame)) by (bit_vector);
}

pub proof fn lemma_page_base_div<A: ArchPagingMeta>(vpage: nat)
    ensures
        page_base::<A>(vpage) / (<A::MinPageSize as PageSize>::SIZE as nat) == vpage,
{
    <A::MinPageSize as PageSize>::lemma_size_wf();
    let page_size = <A::MinPageSize as PageSize>::SIZE as nat;
    lemma_mul_is_commutative(vpage as int, page_size as int);
    lemma_div_by_multiple(vpage as int, page_size as int);
}

pub proof fn lemma_pgtbl_idx_page_base_step<A: ArchPagingMeta>(vpage: nat, level: PageLevel)
    requires
        level.spec_child() is Some,
    ensures
        pgtbl_idx::<A>(page_base::<A>(vpage), level) == pgtbl_idx::<A>(
            page_base::<A>(vpage / PTPage::<A>::count()),
            level.spec_child().unwrap(),
        ),
{
    lemma_pgtbl_idx_step::<A>(page_base::<A>(vpage), level);
    lemma_page_base_div::<A>(vpage);
}

/// An entry always lies inside its table page.
pub proof fn lemma_pgtbl_idx_bounded<A: ArchPagingMeta>(vpage: nat, level: PageLevel)
    ensures
        (pgtbl_idx::<A>(page_base::<A>(vpage), level) as nat) < PTPage::<A>::count(),
    decreases level.depth(),
{
    PTPage::<A>::lemma_count_positive();
    lemma_page_base_div::<A>(vpage);
    if let Some(child) = level.spec_child() {
        PageLevel::lemma_child_decreases(level);
        lemma_pgtbl_idx_page_base_step::<A>(vpage, level);
        lemma_pgtbl_idx_bounded::<A>(vpage / PTPage::<A>::count(), child);
    }
}

/// Two pages the walk cannot tell apart at any level are the same page, so an entry belongs to
/// exactly one page.
pub proof fn lemma_pgtbl_idx_injective<A: ArchPagingMeta>(vpage1: nat, vpage2: nat, levels: nat)
    requires
        levels <= 5,
        vpage1 < pow(PTPage::<A>::count() as int, levels as nat),
        vpage2 < pow(PTPage::<A>::count() as int, levels as nat),
        forall|l: PageLevel| #![trigger pgtbl_idx::<A>(page_base::<A>(vpage1), l)] #![trigger pgtbl_idx::<A>(page_base::<A>(vpage2), l)] (l.depth() as nat) < levels ==> (pgtbl_idx::<A>(page_base::<A>(vpage1), l) as nat) == (pgtbl_idx::<A>(page_base::<A>(vpage2), l) as nat),
    ensures
        vpage1 == vpage2,
    decreases levels,
{
    PTPage::<A>::lemma_count_positive();
    let e = PTPage::<A>::count();
    if levels == 0 {
        vstd::arithmetic::power::lemma_pow0(e as int);
    } else {
        lemma_page_base_div::<A>(vpage1);
        lemma_page_base_div::<A>(vpage2);
        vstd::arithmetic::power::lemma_pow_adds(e as int, 1, (levels - 1) as nat);
        vstd::arithmetic::power::lemma_pow1(e as int);
        vstd::arithmetic::power::lemma_pow_positive(e as int, (levels - 1) as nat);
        vstd::arithmetic::div_mod::lemma_multiply_divide_lt(
            vpage1 as int,
            e as int,
            pow(e as int, (levels - 1) as nat),
        );
        vstd::arithmetic::div_mod::lemma_multiply_divide_lt(
            vpage2 as int,
            e as int,
            pow(e as int, (levels - 1) as nat),
        );
        assert forall|l: PageLevel| (l.depth() as nat) + 1 < levels implies #[trigger] (pgtbl_idx::<A>(page_base::<A>(vpage1 / e), l) as nat)
            == (pgtbl_idx::<A>(page_base::<A>(vpage2 / e), l) as nat) by {
            PageLevel::lemma_parent_depth(l);
            lemma_pgtbl_idx_page_base_step::<A>(vpage1, l.spec_parent());
            lemma_pgtbl_idx_page_base_step::<A>(vpage2, l.spec_parent());
            assert((pgtbl_idx::<A>(page_base::<A>(vpage1), l.spec_parent()) as nat) == (pgtbl_idx::<A>(page_base::<A>(vpage2), l.spec_parent()) as nat));
        }
        lemma_pgtbl_idx_injective::<A>(vpage1 / e, vpage2 / e, (levels - 1) as nat);
        assert((pgtbl_idx::<A>(page_base::<A>(vpage1), PageLevel::Level0) as nat) == (pgtbl_idx::<A>(page_base::<A>(vpage2), PageLevel::Level0) as nat));
        lemma_fundamental_div_mod(vpage1 as int, e as int);
        lemma_fundamental_div_mod(vpage2 as int, e as int);
    }
}

/// One step of a walk: an entry that decodes as a table at `level` sends the walk into the page
/// it names, and everything the walk does from there it does from `frame` too.
pub proof fn lemma_walk_step<A: ArchPagingMeta>(
    view: PhyMemView<A>,
    frame: FrameId,
    level: PageLevel,
    vpage: nat,
)
    requires
        PTEntry::<A>::spec_from_bits(
            view.word_at(view.path_id(frame, vpage, level)),
        ).is_table_spec(level),
    ensures
        level.spec_child() is Some,
        ({
            let id = view.path_id(frame, vpage, level);
            let next = FrameId(
                PTEntry::<A>::spec_from_bits(view.word_at(id)).page_frame_spec() as nat,
            );
            let child = level.spec_child()->Some_0;
            &&& view.walk_leaf_ptbl(frame, level, vpage) == view.walk_leaf_ptbl(
                next,
                child,
                vpage,
            )
            &&& forall|c: WordId|
                #![trigger view.on_walk_path(frame, level, vpage, c)]
                #![trigger view.on_walk_path(next, child, vpage, c)]
                view.on_walk_path(frame, level, vpage, c) == (c == id || view.on_walk_path(
                    next,
                    child,
                    vpage,
                    c,
                ))
            &&& forall|f: FrameId|
                #![trigger view.walk_visits(frame, level, vpage, f)]
                #![trigger view.walk_visits(next, child, vpage, f)]
                view.walk_visits(frame, level, vpage, f) == (f == frame || view.walk_visits(
                    next,
                    child,
                    vpage,
                    f,
                ))
        }),
{
    PageLevel::lemma_no_child_is_leaf(level);
}

/// A walk stops where it stands when the entry it reads there does not decode as a table --
/// either because that entry maps a page, or because level 0 has nothing below it.
pub proof fn lemma_walk_leaf_ptbl_stops<A: ArchPagingMeta>(
    view: PhyMemView<A>,
    frame: FrameId,
    level: PageLevel,
    vpage: nat,
)
    requires
        !PTEntry::<A>::spec_from_bits(
            view.word_at(view.path_id(frame, vpage, level)),
        ).is_table_spec(level),
    ensures
        view.walk_leaf_ptbl(frame, level, vpage) == (frame, level),
        forall|c: WordId| #[trigger]
            view.on_walk_path(frame, level, vpage, c) == (c == view.path_id(
                frame,
                vpage,
                level,
            )),
        forall|f: FrameId| #[trigger]
            view.walk_visits(frame, level, vpage, f) == (f == frame),
{
}

/// A walk rests on an entry it reads, in a frame it visits, at or below the level it started at.
pub proof fn lemma_rest_on_walk_path<A: ArchPagingMeta>(
    view: PhyMemView<A>,
    frame: FrameId,
    level: PageLevel,
    vpage: nat,
)
    ensures
        view.on_walk_path(
            frame,
            level,
            vpage,
            view.path_id(
                view.walk_leaf_ptbl(frame, level, vpage).0,
                vpage,
                view.walk_leaf_ptbl(frame, level, vpage).1,
            ),
        ),
        view.walk_visits(frame, level, vpage, view.walk_leaf_ptbl(frame, level, vpage).0),
        view.walk_leaf_ptbl(frame, level, vpage).1.depth() <= level.depth(),
    decreases level.depth(),
{
    let e = PTEntry::<A>::spec_from_bits(view.word_at(view.path_id(frame, vpage, level)));
    if e.is_table_spec(level) {
        lemma_walk_step(view, frame, level, vpage);
        PageLevel::lemma_child_decreases(level);
        lemma_rest_on_walk_path(view, FrameId(e.page_frame_spec() as nat), level.spec_child()->Some_0, vpage);
    } else {
        lemma_walk_leaf_ptbl_stops(view, frame, level, vpage);
    }
}

/// A walk of `vpage` sees only the entries it reads, so anything else may change under it.
///
/// Where the walk rests, which entries it reads and which frames it visits are settled together,
/// because the induction step needs all three facts about the table one level down.
pub proof fn lemma_walk_leaf_entry_local<A: ArchPagingMeta>(
    v1: PhyMemView<A>,
    v2: PhyMemView<A>,
    frame: FrameId,
    level: PageLevel,
    vpage: nat,
)
    requires
        v1.frame_to_objs == v2.frame_to_objs,
        forall|c: WordId| #[trigger]
            v1.on_walk_path(frame, level, vpage, c) ==> v1.word_at(c) == v2.word_at(c),
    ensures
        v1.walk_leaf_ptbl(frame, level, vpage) == v2.walk_leaf_ptbl(frame, level, vpage),
        forall|c: WordId|
            #![trigger v1.on_walk_path(frame, level, vpage, c)]
            #![trigger v2.on_walk_path(frame, level, vpage, c)]
            v1.on_walk_path(frame, level, vpage, c) == v2.on_walk_path(frame, level, vpage, c),
        forall|f: FrameId|
            #![trigger v1.walk_visits(frame, level, vpage, f)]
            #![trigger v2.walk_visits(frame, level, vpage, f)]
            v1.walk_visits(frame, level, vpage, f) == v2.walk_visits(
                frame,
                level,
                vpage,
                f,
            ),
    decreases level.depth(),
{
    let id = v1.path_id(frame, vpage, level);
    assert(v1.on_walk_path(frame, level, vpage, id));
    let e = PTEntry::<A>::spec_from_bits(v1.word_at(id));
    if e.is_table_spec(level) {
        let child = level.spec_child()->Some_0;
        let next = FrameId(e.page_frame_spec() as nat);
        lemma_walk_step(v1, frame, level, vpage);
        lemma_walk_step(v2, frame, level, vpage);
        assert forall|c: WordId| #[trigger]
            v1.on_walk_path(next, child, vpage, c) implies v1.word_at(c) == v2.word_at(c) by {
            assert(v1.on_walk_path(frame, level, vpage, c));
        }
        PageLevel::lemma_child_decreases(level);
        lemma_walk_leaf_entry_local(v1, v2, next, child, vpage);
    } else {
        lemma_walk_leaf_ptbl_stops(v1, frame, level, vpage);
        lemma_walk_leaf_ptbl_stops(v2, frame, level, vpage);
    }
}

/// Where a walk goes depends only on the residents of the frames it visits, so moving a frame no
/// walk visits moves nothing. `live` names the frames the walk in question stays within.
pub proof fn lemma_walk_leaf_entry_frames<A: ArchPagingMeta>(
    v1: PhyMemView<A>,
    v2: PhyMemView<A>,
    live: Set<FrameId>,
    frame: FrameId,
    level: PageLevel,
    vpage: nat,
)
    requires
        v1.data == v2.data,
        v1.frozen == v2.frozen,
        forall|f: FrameId| #[trigger]
            live.contains(f) ==> v1.frame_to_objs[f] == v2.frame_to_objs[f],
        forall|f: FrameId| #[trigger]
            v1.walk_visits(frame, level, vpage, f) ==> live.contains(f),
    ensures
        v1.walk_leaf_ptbl(frame, level, vpage) == v2.walk_leaf_ptbl(frame, level, vpage),
        forall|c: WordId|
            #![trigger v1.on_walk_path(frame, level, vpage, c)]
            #![trigger v2.on_walk_path(frame, level, vpage, c)]
            v1.on_walk_path(frame, level, vpage, c) == v2.on_walk_path(frame, level, vpage, c),
        forall|f: FrameId|
            #![trigger v1.walk_visits(frame, level, vpage, f)]
            #![trigger v2.walk_visits(frame, level, vpage, f)]
            v1.walk_visits(frame, level, vpage, f) == v2.walk_visits(
                frame,
                level,
                vpage,
                f,
            ),
    decreases level.depth(),
{
    assert(v1.walk_visits(frame, level, vpage, frame));
    assert(live.contains(frame));
    let e = PTEntry::<A>::spec_from_bits(v1.word_at(v1.path_id(frame, vpage, level)));
    if e.is_table_spec(level) {
        let child = level.spec_child()->Some_0;
        let next = FrameId(e.page_frame_spec() as nat);
        lemma_walk_step(v1, frame, level, vpage);
        lemma_walk_step(v2, frame, level, vpage);
        assert forall|f: FrameId| #[trigger]
            v1.walk_visits(next, child, vpage, f) implies live.contains(f) by {
            assert(v1.walk_visits(frame, level, vpage, f));
        }
        PageLevel::lemma_child_decreases(level);
        lemma_walk_leaf_entry_frames(v1, v2, live, next, child, vpage);
    } else {
        lemma_walk_leaf_ptbl_stops(v1, frame, level, vpage);
        lemma_walk_leaf_ptbl_stops(v2, frame, level, vpage);
    }
}

/// Two pages holding equal entries hold the same entry for `vpage`, whatever level they are read
/// at.
pub proof fn lemma_root_copy_entry<A: ArchPagingMeta>(
    view: PhyMemView<A>,
    r1: FrameId,
    r2: FrameId,
    level: PageLevel,
    vpage: nat,
)
    requires
        forall|i: nat| i < PTPage::<A>::count() ==> #[trigger] view.word_at(
            WordId((view.resident(r1).0 + i) as nat),
        ) == view.word_at(WordId((view.resident(r2).0 + i) as nat)),
    ensures
        view.word_at(view.path_id(r1, vpage, level)) == view.word_at(
            view.path_id(r2, vpage, level),
        ),
{
    lemma_pgtbl_idx_bounded::<A>(vpage, level);
    assert(view.path_id(r1, vpage, level) == WordId(
        (view.resident(r1).0 + pgtbl_idx::<A>(page_base::<A>(vpage), level) as nat) as nat,
    ));
    assert(view.path_id(r2, vpage, level) == WordId(
        (view.resident(r2).0 + pgtbl_idx::<A>(page_base::<A>(vpage), level) as nat) as nat,
    ));
}

/// Two roots holding equal entries lead a walk to the same place from the level below, which is
/// what makes a copied root page a faithful clone of an address space. Only the entry read in the
/// root itself differs between the two, because it lives in a different page.
pub proof fn lemma_walk_leaf_entry_root_copy<A: ArchPagingMeta>(
    view: PhyMemView<A>,
    r1: FrameId,
    r2: FrameId,
    level: PageLevel,
    vpage: nat,
)
    requires
        PTEntry::<A>::spec_from_bits(
            view.word_at(view.path_id(r1, vpage, level)),
        ).is_table_spec(level),
        forall|i: nat| i < PTPage::<A>::count() ==> #[trigger] view.word_at(
            WordId((view.resident(r1).0 + i) as nat),
        ) == view.word_at(WordId((view.resident(r2).0 + i) as nat)),
    ensures
        view.walk_leaf_ptbl(r1, level, vpage) == view.walk_leaf_ptbl(r2, level, vpage),
        forall|c: WordId| #[trigger]
            view.on_walk_path(r1, level, vpage, c) ==> c == view.path_id(r1, vpage, level)
                || view.on_walk_path(r2, level, vpage, c),
        forall|f: FrameId| #[trigger]
            view.walk_visits(r1, level, vpage, f) ==> f == r1 || view.walk_visits(
                r2,
                level,
                vpage,
                f,
            ),
{
    lemma_root_copy_entry(view, r1, r2, level, vpage);
    lemma_walk_step(view, r1, level, vpage);
    lemma_walk_step(view, r2, level, vpage);
}

/// A copied root translates every page exactly as the root it was copied from.
pub proof fn lemma_translate_root_copy<A: ArchPagingMeta>(
    view: PhyMemView<A>,
    r1: FrameId,
    r2: FrameId,
    top: PageLevel,
    vpage: nat,
)
    requires
        forall|i: nat| i < PTPage::<A>::count() ==> #[trigger] view.word_at(
            WordId((view.resident(r1).0 + i) as nat),
        ) == view.word_at(WordId((view.resident(r2).0 + i) as nat)),
    ensures
        view.translate(r1, top, vpage) == view.translate(r2, top, vpage),
{
    lemma_root_copy_entry(view, r1, r2, top, vpage);
    let e = PTEntry::<A>::spec_from_bits(view.word_at(view.path_id(r1, vpage, top)));
    if e.is_table_spec(top) {
        lemma_walk_leaf_entry_root_copy(view, r1, r2, top, vpage);
    } else {
        lemma_walk_leaf_ptbl_stops(view, r1, top, vpage);
        lemma_walk_leaf_ptbl_stops(view, r2, top, vpage);
    }
}

/// Where `vpage` leads depends only on the entries its own walk reads. This is what lets a
/// transition that rewrites entries elsewhere leave every other translation alone.
pub proof fn lemma_translate_local<A: ArchPagingMeta>(
    v1: PhyMemView<A>,
    v2: PhyMemView<A>,
    cr3: FrameId,
    top: PageLevel,
    vpage: nat,
)
    requires
        v1.frame_to_objs == v2.frame_to_objs,
        forall|c: WordId| #[trigger]
            v1.on_walk_path(cr3, top, vpage, c) ==> v1.word_at(c) == v2.word_at(c),
    ensures
        v1.translate(cr3, top, vpage) == v2.translate(cr3, top, vpage),
        v1.resting_slot(cr3, top, vpage) == v2.resting_slot(cr3, top, vpage),
{
    lemma_walk_leaf_entry_local(v1, v2, cr3, top, vpage);
    lemma_rest_on_walk_path(v1, cr3, top, vpage);
}

/// Where `vpage` leads depends only on the residents of the frames its own walk visits, so a
/// transition that only moves other frames leaves it alone.
pub proof fn lemma_translate_frames<A: ArchPagingMeta>(
    v1: PhyMemView<A>,
    v2: PhyMemView<A>,
    live: Set<FrameId>,
    cr3: FrameId,
    top: PageLevel,
    vpage: nat,
)
    requires
        v1.data == v2.data,
        v1.frozen == v2.frozen,
        forall|f: FrameId| #[trigger]
            live.contains(f) ==> v1.frame_to_objs[f] == v2.frame_to_objs[f],
        forall|f: FrameId| #[trigger]
            v1.walk_visits(cr3, top, vpage, f) ==> live.contains(f),
    ensures
        v1.translate(cr3, top, vpage) == v2.translate(cr3, top, vpage),
        v1.resting_slot(cr3, top, vpage) == v2.resting_slot(cr3, top, vpage),
{
    lemma_walk_leaf_entry_frames(v1, v2, live, cr3, top, vpage);
    lemma_rest_on_walk_path(v1, cr3, top, vpage);
}

} // verus!

verus! {

/// The page a virtual address falls in.
pub open spec fn addr_to_vpage<A: ArchPagingMeta>(addr: nat) -> nat {
    addr / PTPage::<A>::count()
}

/// How far into its page a virtual address sits.
pub open spec fn voffset<A: ArchPagingMeta>(v: nat) -> nat {
    v % PTPage::<A>::count()
}

/// The ids an object covers.
pub open spec fn obj_ids<A: ArchPagingMeta>(obj: ObjId) -> Set<WordId> {
    Set::range(obj.0, obj.0 + PTPage::<A>::count()).map_by(|n: nat| WordId(n), |w: WordId| w.0)
}

/// The id an address reaches in `obj`.
pub open spec fn oid_of<A: ArchPagingMeta>(obj: ObjId, v: nat) -> WordId {
    WordId(obj.0 + voffset::<A>(v))
}

/// The object a certificate came from, recovered from the address it certifies.
pub open spec fn obj_of<A: ArchPagingMeta>(oid: WordId, v: nat) -> ObjId {
    ObjId((oid.0 - voffset::<A>(v)) as nat)
}

/// The governed addresses of one page of one address space.
pub open spec fn page_addrs<A: ArchPagingMeta>(dom: Set<(nat, nat)>, a: nat, vpage: nat) -> Set<
    (nat, nat),
> {
    dom.filter(|k: (nat, nat)| k.0 == a && addr_to_vpage::<A>(k.1) == vpage)
}

/// The certificates of one page, all reading `oid`.
pub open spec fn page_view<A: ArchPagingMeta>(
    dom: Set<(nat, nat)>,
    a: nat,
    vpage: nat,
    oid: Option<WordId>,
) -> Map<(nat, nat), Option<WordId>> {
    Map::new(page_addrs::<A>(dom, a, vpage), |k: (nat, nat)| oid)
}

/// The certificates a page gains from `obj`.
pub open spec fn mapped_view<A: ArchPagingMeta>(
    dom: Set<(nat, nat)>,
    a: nat,
    vpage: nat,
    obj: ObjId,
) -> Map<(nat, nat), Option<WordId>> {
    Map::new(page_addrs::<A>(dom, a, vpage), |k: (nat, nat)| Some(oid_of::<A>(obj, k.1)))
}

/// The pages one address space governs.
pub open spec fn space_pages(dom: Set<(nat, nat)>, a: nat) -> Set<nat> {
    dom.filter(|k: (nat, nat)| k.0 == a).map_by(|k: (nat, nat)| k.1, |vpage: nat| (a, vpage))
}

/// The keys one address space contributes over a set of pages or addresses.
pub open spec fn space_keys(a: nat, ks: Set<nat>) -> Set<(nat, nat)> {
    ks.map_by(|vpage: nat| (a, vpage), |k: (nat, nat)| k.1)
}

pub broadcast proof fn lemma_space_keys(a: nat, ks: Set<nat>, k: (nat, nat))
    ensures
        #[trigger] space_keys(a, ks).contains(k) <==> k.0 == a && ks.contains(k.1),
{
    broadcast use Set::lemma_map_by_contains;

}

pub broadcast proof fn lemma_space_pages(dom: Set<(nat, nat)>, a: nat, vpage: nat)
    ensures
        #[trigger] space_pages(dom, a).contains(vpage) <==> dom.contains((a, vpage)),
{
    broadcast use Set::lemma_map_by_contains;

}

/// An entry no walk descends through: absent at every level, or a mapping at every level.
///
/// This is what makes an entry a *leaf slot*. A walk goes on only through a table pointer, so
/// replacing one such entry with another cannot move any walk -- it can only change what the
/// pages already resting there map. Quantified over all levels because a word carries no level
/// of its own: the same bits are a table pointer at one level and a huge page at another, and a
/// self-mapped table is read at several.
pub open spec fn never_table<A: ArchPagingMeta>(w: usize) -> bool {
    forall|l: PageLevel| !#[trigger] PTEntry::<A>::spec_from_bits(w).is_table_spec(l)
}

/// The frame an entry read at `level` hands a walk of `vpage`, or `None` if it maps nothing.
/// This is the last step of [`PhyMemView::translate`], on its own.
pub open spec fn leaf_frame<A: ArchPagingMeta>(w: usize, level: PageLevel, vpage: nat) -> Option<
    FrameId,
> {
    let e = PTEntry::<A>::spec_from_bits(w);
    if e.is_leaf_spec(level) {
        Some(FrameId((e.page_frame_spec() as nat + leaf_offset::<A>(vpage, level)) as nat))
    } else {
        Option::None
    }
}

/// A write that neither removes nor installs a table pointer leaves every walk exactly where it
/// was: which frames it stands in and which entries it reads are decided by the entries it
/// descends through, and this write touches none of those.
pub proof fn lemma_leaf_write_local<A: ArchPagingMeta>(
    v1: PhyMemView<A>,
    v2: PhyMemView<A>,
    frame: FrameId,
    level: PageLevel,
    vpage: nat,
)
    requires
        v1.frame_to_objs == v2.frame_to_objs,
        forall|c: WordId| #[trigger]
            v1.word_at(c) != v2.word_at(c) ==> never_table::<A>(v1.word_at(c)) && never_table::<A>(
                v2.word_at(c),
            ),
    ensures
        v1.walk_leaf_ptbl(frame, level, vpage) == v2.walk_leaf_ptbl(frame, level, vpage),
        forall|f: FrameId| #[trigger]
            v1.walk_visits(frame, level, vpage, f) == v2.walk_visits(frame, level, vpage, f),
        forall|c: WordId| #[trigger]
            v1.on_walk_path(frame, level, vpage, c) == v2.on_walk_path(frame, level, vpage, c),
    decreases level.depth(),
{
    let id = v1.path_id(frame, vpage, level);
    let e1 = PTEntry::<A>::spec_from_bits(v1.word_at(id));
    let e2 = PTEntry::<A>::spec_from_bits(v2.word_at(id));
    // Neither view sees a table pointer here unless both see the very same word.
    if e1.is_table_spec(level) {
        assert(v1.word_at(id) == v2.word_at(id));
    }
    if e2.is_table_spec(level) {
        assert(v1.word_at(id) == v2.word_at(id));
    }
    match level.spec_child() {
        Option::None => {},
        Option::Some(child) => {
            if e1.is_table_spec(level) {
                let nf = FrameId(e1.page_frame_spec() as nat);
                lemma_leaf_write_local::<A>(v1, v2, nf, child, vpage);
                assert forall|f: FrameId| #[trigger]
                    v1.walk_visits(frame, level, vpage, f) == v2.walk_visits(
                        frame,
                        level,
                        vpage,
                        f,
                    ) by {
                    assert(v1.walk_visits(nf, child, vpage, f) == v2.walk_visits(
                        nf,
                        child,
                        vpage,
                        f,
                    ));
                }
                assert forall|d: WordId| #[trigger]
                    v1.on_walk_path(frame, level, vpage, d) == v2.on_walk_path(
                        frame,
                        level,
                        vpage,
                        d,
                    ) by {
                    assert(v1.on_walk_path(nf, child, vpage, d) == v2.on_walk_path(
                        nf,
                        child,
                        vpage,
                        d,
                    ));
                }
            }
        },
    }
}

/// The frame a leaf entry for `vpage` must name: the frame holding the object the page maps.
pub open spec fn walk_target(
    vmap: Map<(nat, nat), Option<ObjId>>,
    obj_to_frame: Map<ObjId, Option<FrameId>>,
    a: nat,
    vpage: nat,
) -> Option<FrameId> {
    match vmap[(a, vpage)] {
        Option::None => Option::None,
        Option::Some(o) => obj_to_frame[o],
    }
}

} // verus!

tokenized_state_machine!(Mem<A: ArchPagingMeta> {
    fields {
        /// Word id -> its value, writable. The single copy, and what a write consumes.
        #[sharding(map)]
        pub data: Map<WordId, usize>,

        /// Content that has given up the right to be written for the right to be shared.
        #[sharding(persistent_map)]
        pub frozen: Map<WordId, usize>,

        /// Object -> the frame holding it. Physical, and invisible to permissions.
        #[sharding(map)]
        pub obj_to_frame: Map<ObjId, Option<FrameId>>,

        /// Frame -> the objects placed there. What makes "this frame holds nothing but my
        /// content" ownable, and hence what a write can demand.
        #[sharding(map)]
        pub frame_to_objs: Map<FrameId, Set<ObjId>>,

        /// Counts raw ids, so fresh object bases can be compared with word ids.
        #[sharding(variable)]
        pub next_oid: nat,

        /// Source of address space ids. Spawning takes the next one rather than being handed
        /// one, so uniqueness is the machine's to guarantee, not the caller's to promise.
        #[sharding(variable)]
        pub next_asid: nat,

        /// The word ids that page table entries occupy. A write to anything else cannot move a
        /// translation, which is what lets an ordinary write proceed without a path proof.
        #[sharding(variable)]
        pub pt_words: Set<WordId>,

        /// (address space, page) -> the entry where its walk stops. Kept as state rather than
        /// derived because a transition cannot read the page tables: this is what lets a remap
        /// see *every* address space that reads the entry it writes. Spaces sharing a sub table
        /// share these ids, so a kernel range reached from every root is remapped for every
        /// thread at once, while a range reached from one root is remapped for that thread alone.
        #[sharding(variable)]
        pub leaf_id: Map<(nat, nat), Option<(WordId, PageLevel)>>,

        /// (address space, page) -> the object it maps. A ghost refinement of the entries in
        /// memory. Keyed on the address space because a page means nothing on its own: two
        /// threads running different roots read different entries for the same page.
        #[sharding(map)]
        pub vmap: Map<(nat, nat), Option<ObjId>>,

        /// (address space, virtual address) -> the word id it reaches. This is the half of a
        /// permission that is *not* portable between threads; the `data` token it is paired
        /// with names an object and travels freely.
        #[sharding(map)]
        pub vmem: Map<(nat, nat), Option<WordId>>,

        #[sharding(variable)]
        pub vmem_dom: Set<(nat, nat)>,

        #[sharding(variable)]
        pub vmap_dom: Set<(nat, nat)>,

        #[sharding(constant)]
        pub frames_dom: Set<FrameId>,

        /// The frames handed out. A frame outside this set is free: it has no `frame_to_objs`
        /// token at all, so nothing can be placed in it until it is allocated.
        #[sharding(variable)]
        pub allocated: Set<FrameId>,

        /// The running address spaces. Boot brings up one; threads are added later.
        #[sharding(variable)]
        pub asids: Set<nat>,

        /// CPU -> the address space it is running, i.e. what its CR3 holds. Holding this token
        /// is what lets code dereference an address of that space: a certificate names an
        /// address space, and only the CPU running it can follow the walk.
        #[sharding(map)]
        pub cpus: Map<nat, nat>,

        /// Address space -> the frame its walk starts from, i.e. what CR3 holds while it runs.
        #[sharding(variable)]
        pub cr3: Map<nat, FrameId>,

        #[sharding(constant)]
        pub top: PageLevel,

        #[sharding(constant)]
        pub marker: PhantomData<A>,
    }

    #[invariant]
    pub spec fn domains_fixed(&self) -> bool {
        &&& self.vmem.dom() =~= self.vmem_dom
        &&& self.vmap.dom() =~= self.vmap_dom
        &&& self.frame_to_objs.dom() =~= self.allocated
        &&& self.allocated.subset_of(self.frames_dom)
    }

    #[invariant]
    pub spec fn pages_governed(&self) -> bool {
        forall|k: (nat, nat)| #[trigger] self.vmem_dom.contains(k)
            ==> self.vmap_dom.contains((k.0, addr_to_vpage::<A>(k.1)))
    }

    /// Every page is describable by the entry indices a walk reads, so distinct pages differ
    /// somewhere a walk looks.
    #[invariant]
    pub spec fn pages_bounded(&self) -> bool {
        forall|k: (nat, nat)| #[trigger] self.vmap_dom.contains(k)
            ==> self.asids.contains(k.0) && k.1 < pow(
                PTPage::<A>::count() as int,
                (self.top.depth() + 1) as nat,
            )
    }

    /// Every frame can be named by an entry, so encoding one and decoding it back gives it again.
    #[invariant]
    pub spec fn frames_encodable(&self) -> bool {
        forall|f: FrameId| #[trigger] self.frames_dom.contains(f)
            ==> f.0 <= usize::MAX && encodable::<A>(f.0 as usize)
    }

    #[invariant]
    pub spec fn certificates_backed(&self) -> bool {
        forall|k: (nat, nat)| #[trigger] self.vmem_dom.contains(k) && self.vmem[k] is Some ==> {
            &&& self.vmap[(k.0, addr_to_vpage::<A>(k.1))] is Some
            &&& self.vmem[k]->Some_0 == oid_of::<A>(self.vmap[(k.0, addr_to_vpage::<A>(k.1))]->Some_0, k.1)
        }
    }

    #[invariant]
    pub spec fn ids_fresh(&self) -> bool {
        &&& forall|c: WordId| #[trigger] self.data.dom().contains(c) ==> c.0 < self.next_oid
        &&& forall|c: WordId| #[trigger] self.frozen.dom().contains(c) ==> c.0 < self.next_oid
        &&& forall|b: ObjId| #[trigger] self.obj_to_frame.dom().contains(b)
            ==> b.0 + PTPage::<A>::count() <= self.next_oid
        &&& forall|k: (nat, nat)| #[trigger] self.vmap_dom.contains(k) && self.vmap[k] is Some
            ==> self.vmap[k]->Some_0.0 + PTPage::<A>::count() <= self.next_oid
        &&& forall|c: WordId| #[trigger] self.pt_words.contains(c) ==> c.0 < self.next_oid
    }

    #[invariant]
    pub spec fn content_total(&self) -> bool {
        &&& forall|c: WordId| #[trigger] self.data.dom().contains(c) ==> !self.frozen.dom().contains(c)
        &&& forall|b: ObjId| #[trigger] self.obj_to_frame.dom().contains(b)
            ==> obj_ids::<A>(b).subset_of(self.data.dom().union(self.frozen.dom()))
    }

    #[invariant]
    pub spec fn objects_disjoint(&self) -> bool {
        forall|b1: ObjId, b2: ObjId, c: WordId|
            self.obj_to_frame.dom().contains(b1) && #[trigger] self.obj_to_frame.dom().contains(b2)
                && #[trigger] obj_ids::<A>(b1).contains(c) && obj_ids::<A>(b2).contains(c)
                ==> b1 == b2
    }

    #[invariant]
    pub spec fn residency_sound(&self) -> bool {
        forall|pfn: FrameId, b: ObjId|
            self.allocated.contains(pfn) && #[trigger] self.frame_to_objs[pfn].contains(b) ==> {
                &&& self.obj_to_frame.dom().contains(b)
                &&& self.obj_to_frame[b] == Some(pfn)
            }
    }

    #[invariant]
    pub spec fn residency_complete(&self) -> bool {
        forall|b: ObjId| #[trigger] self.obj_to_frame.dom().contains(b) && self.obj_to_frame[b] is Some
            ==> {
            &&& self.allocated.contains(self.obj_to_frame[b]->Some_0)
            &&& self.frame_to_objs[self.obj_to_frame[b]->Some_0].contains(b)
        }
    }

    /// A frame holds one set of words, so objects sharing a frame must agree.
    #[invariant]
    pub spec fn coplaced_agree(&self) -> bool {
        forall|b1: ObjId, b2: ObjId, off: nat|
            self.obj_to_frame.dom().contains(b1) && #[trigger] self.obj_to_frame.dom().contains(b2)
                && self.obj_to_frame[b1] is Some && self.obj_to_frame[b1] == self.obj_to_frame[b2]
                && off < PTPage::<A>::count()
                ==> #[trigger] self.phy_view().word_at(WordId((b1.0 + off) as nat))
                    == self.phy_view().word_at(WordId((b2.0 + off) as nat))
    }

    /// The part of physical memory a walk of this state reads.
    pub open spec fn phy_view(&self) -> PhyMemView<A> {
        PhyMemView {
            data: self.data,
            frozen: self.frozen,
            frame_to_objs: self.frame_to_objs,
            marker: PhantomData,
        }
    }

    /// The recorded remap target is the entry where the walk really stops.
    #[invariant]
    pub spec fn leaf_ids_agree(&self) -> bool {
        &&& self.leaf_id.dom() =~= self.vmap_dom
        &&& forall|k: (nat, nat)| #[trigger] self.vmap_dom.contains(k) ==> self.leaf_id[k] == Some(
            self.phy_view().resting_slot(self.cr3[k.0], self.top, k.1),
        )
    }

    #[invariant]
    pub spec fn cpus_run_spaces(&self) -> bool {
        forall|cpu: nat| #[trigger] self.cpus.dom().contains(cpu) ==> self.asids.contains(self.cpus[cpu])
    }

    #[invariant]
    pub spec fn asids_fresh(&self) -> bool {
        forall|a: nat| #[trigger] self.asids.contains(a) ==> a < self.next_asid
    }

    #[invariant]
    pub spec fn root_placed(&self) -> bool {
        &&& self.cr3.dom() =~= self.asids
        &&& forall|a: nat| #[trigger] self.asids.contains(a) ==> {
            &&& self.allocated.contains(self.cr3[a])
            &&& exists|o: ObjId| self.frame_to_objs[self.cr3[a]] =~= Set::<ObjId>::empty().insert(o)
        }
    }

    /// A frame a walk lands on holds exactly one object. That is what turns the frame back into
    /// an object whose words can be read; frames holding data may be shared freely.
    #[invariant]
    pub spec fn path_frames_solo(&self) -> bool {
        forall|k: (nat, nat), f: FrameId|
            self.vmap_dom.contains(k) && #[trigger] self.phy_view().walk_visits(
                self.cr3[k.0],
                self.top,
                k.1,
                f,
            ) ==> {
                &&& self.allocated.contains(f)
                &&& exists|o: ObjId| self.frame_to_objs[f] =~= Set::<ObjId>::empty().insert(o)
            }
    }

    /// Every entry a walk reads is a table word.
    #[invariant]
    pub spec fn paths_in_tables(&self) -> bool {
        forall|k: (nat, nat), c: WordId|
            self.vmap_dom.contains(k) && #[trigger] self.phy_view().on_walk_path(
                self.cr3[k.0],
                self.top,
                k.1,
                c,
            ) ==> self.pt_words.contains(c)
    }

    /// What the hardware finds is what `vmap` says. Stated on the whole walk rather than one
    /// entry at a time: a page a table is reached at is not a property of the table -- a
    /// self-mapped page is reached at every level -- so there is no per-table level to key on.
    #[invariant]
    pub spec fn walk_agrees(&self) -> bool {
        forall|k: (nat, nat)| #[trigger] self.vmap_dom.contains(k) ==> self.phy_view().translate(
            self.cr3[k.0],
            self.top,
            k.1,
        ) == walk_target(self.vmap, self.obj_to_frame, k.0, k.1)
    }

    /// Boot brings up one CPU running one kernel thread on page tables the platform has already
    /// built. What it accepts is a *skeleton*: any number of table pages, wired to each other
    /// however the builder liked, but mapping nothing -- so the address space starts out empty
    /// and every page is claimed through the mapping transitions. Further threads join later
    /// through [`spawn`](Self::spawn).
    init!{
        boot(
            view: PhyMemView<A>,
            obj_to_frame: Map<ObjId, Option<FrameId>>,
            next_oid: nat,
            frames: Set<FrameId>,
            vpages: Set<nat>,
            vaddrs: Set<nat>,
            boot_asid: nat,
            root: FrameId,
            top: PageLevel,
        ) {
            require view.frozen =~= Map::empty();
            require view.frame_to_objs.dom().subset_of(frames);
            require view.frame_to_objs.dom().contains(root);
            require forall|f: FrameId| #[trigger] frames.contains(f)
                ==> f.0 <= usize::MAX && encodable::<A>(f.0 as usize);
            require forall|v: nat| #[trigger] vaddrs.contains(v) ==> vpages.contains(addr_to_vpage::<A>(v));
            require forall|vpage: nat| #[trigger] vpages.contains(vpage)
                ==> vpage < pow(PTPage::<A>::count() as int, (top.depth() + 1) as nat);

            // Every page handed over is a table page, so it is the sole resident of its frame.
            require forall|f: FrameId| #[trigger] view.frame_to_objs.dom().contains(f)
                ==> view.frame_to_objs[f] =~= Set::<ObjId>::empty().insert(view.resident(f));
            require forall|f: FrameId| #[trigger] view.frame_to_objs.dom().contains(f) ==> {
                &&& obj_to_frame.dom().contains(view.resident(f))
                &&& obj_to_frame[view.resident(f)] == Some(f)
            };
            require forall|b: ObjId| #[trigger] obj_to_frame.dom().contains(b) ==> {
                &&& obj_to_frame[b] is Some
                &&& view.frame_to_objs.dom().contains(obj_to_frame[b]->Some_0)
                &&& view.resident(obj_to_frame[b]->Some_0) == b
                &&& obj_ids::<A>(b).subset_of(view.data.dom())
            };
            require forall|b1: ObjId, b2: ObjId, c: WordId|
                obj_to_frame.dom().contains(b1) && #[trigger] obj_to_frame.dom().contains(b2)
                    && #[trigger] obj_ids::<A>(b1).contains(c) && obj_ids::<A>(b2).contains(c)
                    ==> b1 == b2;

            // Ids already handed out stay below the watermark, so freshly minted ones are fresh.
            require forall|c: WordId| #[trigger] view.data.dom().contains(c) ==> c.0 < next_oid;
            require forall|b: ObjId| #[trigger] obj_to_frame.dom().contains(b)
                ==> b.0 + PTPage::<A>::count() <= next_oid;

            // The tables map nothing and point nowhere else.
            require forall|vpage: nat| #[trigger] vpages.contains(vpage)
                ==> view.skeleton_walk(view.frame_to_objs.dom(), root, top, vpage);

            init data = view.data;
            init frozen = Map::empty();
            init obj_to_frame = obj_to_frame;
            init frame_to_objs = view.frame_to_objs;
            init allocated = view.frame_to_objs.dom();
            init frames_dom = frames;
            init asids = Set::<nat>::empty().insert(boot_asid);
            init cpus = Map::<nat, nat>::empty().insert(0, boot_asid);
            init next_asid = boot_asid + 1;
            init cr3 = Map::<nat, FrameId>::empty().insert(boot_asid, root);
            init top = top;
            init next_oid = next_oid;
            init pt_words = view.data.dom();
            init vmap = Map::new(space_keys(boot_asid, vpages), |k: (nat, nat)| Option::<ObjId>::None);
            init vmap_dom = space_keys(boot_asid, vpages);
            init leaf_id = Map::new(
                space_keys(boot_asid, vpages),
                |k: (nat, nat)| Some(view.resting_slot(root, top, k.1)),
            );
            init vmem = Map::new(space_keys(boot_asid, vaddrs), |k: (nat, nat)| Option::<WordId>::None);
            init vmem_dom = space_keys(boot_asid, vaddrs);
            init marker = PhantomData;
        }
    }

    /// Switch this CPU to another address space, which on the machine is a write to CR3. The
    /// token is linear, so certificates of the space left behind stop being usable at exactly
    /// the point the hardware stops resolving them.
    transition!{
        switch(cpu: nat, a: nat) {
            remove cpus -= [cpu => let old];
            require pre.asids.contains(a);
            add cpus += [cpu => a];
        }
    }

    /// Hand out a frame no one holds. The `frame_to_objs` token minted here is what makes the
    /// frame exclusively owned, and it is the only way a frame becomes usable.
    transition!{
        alloc_frame(f: FrameId) {
            require pre.frames_dom.contains(f);
            require !pre.allocated.contains(f);
            update allocated = pre.allocated.insert(f);
            add frame_to_objs += [f => Set::<ObjId>::empty()];
        }
    }

    /// Recycle a frame. Giving up the token is what makes it free again, and it may only be
    /// given up once nothing is placed there.
    transition!{
        dealloc_frame(f: FrameId) {
            remove frame_to_objs -= [f => let occ];
            require occ =~= Set::<ObjId>::empty();
            update allocated = pre.allocated.remove(f);
        }
    }

    /// Start another address space from an existing one. It runs its *own* root, a fresh frame
    /// whose entries copy the source root's, so it starts out mapping the same pages but may be
    /// remapped without disturbing the space it came from. The root frame comes from
    /// [`alloc_frame`](Self::alloc_frame); `src_vmap` and `words` are how the caller shows what the
    /// source space maps and holds without the transition reading a sharded field.
    transition!{
        spawn(
            src: nat,
            nroot: FrameId,
            src_vmap: Map<(nat, nat), Option<ObjId>>,
            words: Map<WordId, usize>,
        ) {
            assert(PTPage::<A>::count() > 0) by {
                PTPage::<A>::lemma_count_positive();
            };
            let a = pre.next_asid;
            let nobj = ObjId(pre.next_oid);
            require pre.asids.contains(src);
            update next_asid = pre.next_asid + 1;
            update next_oid = pre.next_oid + PTPage::<A>::count();

            remove frame_to_objs -= [nroot => let occ];
            require occ =~= Set::<ObjId>::empty();
            have frame_to_objs >= [pre.cr3[src] => let roots];
            let robj = roots.choose();
            have data >= (words);
            require words.dom() =~= obj_ids::<A>(robj);
            add frame_to_objs += [nroot => Set::<ObjId>::empty().insert(nobj)];
            add obj_to_frame += [nobj => Some(nroot)];
            add data += (Map::new(
                obj_ids::<A>(nobj),
                |c: WordId| words[WordId((c.0 - nobj.0 + robj.0) as nat)],
            ));
            update pt_words = pre.pt_words.union(obj_ids::<A>(nobj));

            require src_vmap.dom() =~= space_keys(src, space_pages(pre.vmap_dom, src));
            have vmap >= (src_vmap);
            update asids = pre.asids.insert(a);
            update cr3 = pre.cr3.insert(a, nroot);
            update vmap_dom = pre.vmap_dom.union(
                space_keys(a, space_pages(pre.vmap_dom, src)),
            );
            update leaf_id = Map::new(
                pre.vmap_dom.union(space_keys(a, space_pages(pre.vmap_dom, src))),
                |k: (nat, nat)| if k.0 != a {
                    pre.leaf_id[k]
                } else if !PTEntry::<A>::spec_from_bits(
                    words[entry_id::<A>(robj, k.1, pre.top)],
                ).is_table_spec(pre.top) {
                    Some((entry_id::<A>(nobj, k.1, pre.top), pre.top))
                } else {
                    pre.leaf_id[(src, k.1)]
                },
            );
            add vmap += (Map::new(
                space_keys(a, space_pages(pre.vmap_dom, src)),
                |k: (nat, nat)| src_vmap[(src, k.1)],
            ));
        }
    }

    /// Write content. The certificate says which content, the `data` token confers the right,
    /// and `frame_to_objs` witnesses that no other object shares the frame -- so a page still
    /// sharing a frame after a fork cannot write until it has relocated.
    ///
    /// No page table entry is consulted, so a concurrent remap cannot block a write. That is
    /// sound because the word written is not a table word, and a translation reads nothing else.
    transition!{
        write_non_pt(cpu: nat, v: nat, val: usize) {
            have cpus >= [cpu => let a];
            have vmem >= [(a, v) => let oid];
            require oid is Some;
            let obj = obj_of::<A>(oid->Some_0, v);
            have obj_to_frame >= [obj => let p];
            require p is Some;
            have frame_to_objs >= [p->Some_0 => let occupants];
            require occupants =~= Set::<ObjId>::empty().insert(obj);
            require !pre.pt_words.contains(oid->Some_0);
            remove data -= [oid->Some_0 => let old];
            add data += [oid->Some_0 => val];
        }
    }

    /// Write a leaf slot: an entry no walk descends through, before or after. That is what keeps
    /// every walk where it was, so this step changes only what the pages already resting on the
    /// entry map. Installing a table pointer, which does move walks, is a separate step.
    ///
    /// The pages remapped are *every* page whose walk rests on that entry, across every address
    /// space -- which is what makes a shared kernel sub table remap every thread at once. Their
    /// certificates are revoked and reissued rather than left alone: a certificate names the
    /// object its page maps, so a page that now maps something else cannot keep the ones it had.
    ///
    /// `placement` is how the caller shows where the objects being mapped live; it is a submap of
    /// `obj_to_frame`, so it cannot claim a placement the machine disagrees with.
    transition!{
        write_pt(
            c: WordId,
            obj: ObjId,
            val: usize,
            placement: Map<ObjId, Option<FrameId>>,
            oldmap: Map<(nat, nat), Option<ObjId>>,
            nvmap: Map<(nat, nat), Option<ObjId>>,
            oldmem: Map<(nat, nat), Option<WordId>>,
        ) {
            require pre.pt_words.contains(c);
            require obj_ids::<A>(obj).contains(c);
            have obj_to_frame >= [obj => let p];
            require p is Some;
            have frame_to_objs >= [p->Some_0 => let occupants];
            require occupants =~= Set::<ObjId>::empty().insert(obj);

            require never_table::<A>(val);
            remove data -= [c => let old];
            require never_table::<A>(old);
            add data += [c => val];

            let affected = pre.vmap_dom.filter(
                |k: (nat, nat)| pre.leaf_id[k]->Some_0.0 == c,
            );

            have obj_to_frame >= (placement);
            require forall|k: (nat, nat)| #[trigger] affected.contains(k) ==> {
                &&& nvmap[k] is Some ==> placement.dom().contains(nvmap[k]->Some_0)
                &&& nvmap[k] is Some ==> nvmap[k]->Some_0.0 + PTPage::<A>::count() <= pre.next_oid
                &&& leaf_frame::<A>(val, pre.leaf_id[k]->Some_0.1, k.1) == walk_target(
                    nvmap,
                    placement,
                    k.0,
                    k.1,
                )
            };

            require oldmap.dom() =~= affected;
            require nvmap.dom() =~= affected;
            remove vmap -= (oldmap);
            add vmap += (nvmap);

            let readdrs = pre.vmem_dom.filter(
                |k: (nat, nat)| affected.contains((k.0, addr_to_vpage::<A>(k.1))),
            );
            require oldmem.dom() =~= readdrs;
            remove vmem -= (oldmem);
            add vmem += (Map::new(
                readdrs,
                |k: (nat, nat)| match nvmap[(k.0, addr_to_vpage::<A>(k.1))] {
                    Option::None => Option::None,
                    Option::Some(o) => Option::Some(oid_of::<A>(o, k.1)),
                },
            ));
        }
    }

    /// Give up the right to write for the right to share.
    transition!{
        freeze(oid: WordId) {
            require !pre.pt_words.contains(oid);
            remove data -= [oid => let w];
            add frozen (union)= [oid => w];
        }
    }

    /// Read through a certificate and the content it names.
    property!{
        read(cpu: nat, v: nat) {
            have cpus >= [cpu => let a];
            have vmem >= [(a, v) => let oid];
            require oid is Some;
            have data >= [oid->Some_0 => let w];
        }
    }

    /// Read shared content. Never writable, because writing consumes a `data` token and frozen
    /// content has none.
    property!{
        read_shared(cpu: nat, v: nat) {
            have cpus >= [cpu => let a];
            have vmem >= [(a, v) => let oid];
            require oid is Some;
            have frozen >= [oid->Some_0 => let w];
        }
    }

    /// Two addresses reach the same content exactly when their certificates carry the same id --
    /// and the addresses may sit in different address spaces. This is what lets content cross a
    /// thread boundary: the `data` token names an object, so it travels freely, and the receiving
    /// thread re-pairs it with a certificate of its own address space.
    property!{
        alias(a1: nat, v1: nat, a2: nat, v2: nat) {
            have vmem >= [(a1, v1) => let c1];
            have vmem >= [(a2, v2) => let c2];
            require c1 is Some && c1 == c2;
        }
    }

    /// Switching CPUs changes nothing about memory or the page tables.
    #[inductive(switch)]
    fn switch_inductive(pre: Self, post: Self, cpu: nat, a: nat) {
    }

    /// A frame no one held is a frame no walk landed on, so handing it out moves nothing.
    #[inductive(alloc_frame)]
    fn alloc_frame_inductive(pre: Self, post: Self, f: FrameId) {
        lemma_frames_local::<A>(pre, post, pre.allocated);
        // Placing a frame leaves every word where it was, but not the view that reads them.
        assert forall|c: WordId| #[trigger] post.phy_view().word_at(c) == pre.phy_view().word_at(c) by {}
    }

    /// A frame with nothing placed in it is a frame no walk landed on, since a walk lands only
    /// where a single object resides.
    #[inductive(dealloc_frame)]
    fn dealloc_frame_inductive(pre: Self, post: Self, f: FrameId) {
        assert forall|g: FrameId|
            #[trigger] pre.allocated.contains(g) && (exists|o: ObjId|
                pre.frame_to_objs[g] =~= Set::<ObjId>::empty().insert(o))
                implies pre.allocated.remove(f).contains(g) by {
            let o = choose|o: ObjId| pre.frame_to_objs[g] =~= Set::<ObjId>::empty().insert(o);
            assert(pre.frame_to_objs[g].contains(o));
        }
        assert forall|a: nat| #[trigger] pre.asids.contains(a) implies pre.cr3[a] != f by {
            let o = choose|o: ObjId|
                pre.frame_to_objs[pre.cr3[a]] =~= Set::<ObjId>::empty().insert(o);
            assert(pre.frame_to_objs[pre.cr3[a]].contains(o));
        }
        lemma_frames_local::<A>(pre, post, pre.allocated.remove(f));
        // Recycling a frame leaves every word where it was, but not the view that reads them.
        assert forall|c: WordId| #[trigger] post.phy_view().word_at(c) == pre.phy_view().word_at(c) by {}
    }

    /// A new address space walks its copied root exactly as the source walked its own, so it
    /// starts out mapping what the source maps; and the walks already in flight see neither the
    /// fresh words nor the fresh frame.
    #[inductive(spawn)]
    fn spawn_inductive(
        pre: Self,
        post: Self,
        src: nat,
        nroot: FrameId,
        src_vmap: Map<(nat, nat), Option<ObjId>>,
        words: Map<WordId, usize>,
    ) {
        broadcast use lemma_space_keys, lemma_space_pages;

        let a = pre.next_asid;
        let nobj = ObjId(pre.next_oid);
        let robj = pre.frame_to_objs[pre.cr3[src]].choose();
        let top = pre.top;

        assert(!pre.asids.contains(a));
        assert(post.cr3.dom() =~= post.asids);
        assert(post.vmap.dom() =~= post.vmap_dom);

        // The fresh words are beyond every id in use, so no walk reads them.
        let mid1 = Mem::State::<A> {
            data: post.data,
            next_oid: post.next_oid,
            pt_words: post.pt_words,
            ..pre
        };
        lemma_words_local::<A>(pre, mid1, obj_ids::<A>(nobj));

        // The fresh frame held nothing, so no walk landed on it.
        let mid2 = Mem::State::<A> {
            frame_to_objs: post.frame_to_objs,
            allocated: post.allocated,
            ..mid1
        };
        assert forall|g: FrameId|
            #[trigger] pre.allocated.contains(g) && (exists|o: ObjId|
                pre.frame_to_objs[g] =~= Set::<ObjId>::empty().insert(o))
                implies pre.allocated.remove(nroot).contains(g) by {
            let o = choose|o: ObjId| pre.frame_to_objs[g] =~= Set::<ObjId>::empty().insert(o);
            assert(pre.frame_to_objs[g].contains(o));
        }
        lemma_frames_local::<A>(mid1, mid2, pre.allocated.remove(nroot));
        assert(mid2.leaf_ids_agree());

        assert(post.phy_view().resident(nroot) == nobj) by {
            assert(post.frame_to_objs[nroot].contains(nobj));
            assert(post.frame_to_objs[nroot].contains(post.frame_to_objs[nroot].choose()));
        }
        assert(post.phy_view().resident(pre.cr3[src]) == robj);
        assert forall|i: nat| i < PTPage::<A>::count() implies #[trigger] post.phy_view().word_at(
            WordId((nobj.0 + i) as nat),
        ) == post.phy_view().word_at(WordId((robj.0 + i) as nat)) by {
            assert(obj_ids::<A>(nobj).contains(WordId((nobj.0 + i) as nat)));
            assert(obj_ids::<A>(nobj).contains(WordId((nobj.0 + i) as nat)));
            assert(obj_ids::<A>(robj).contains(WordId((robj.0 + i) as nat)));
        }

        // Below the root the new space walks exactly what the source walks, because the two roots
        // hold the same entries; only the root entry itself is read from a different page.
        assert forall|vpage: nat|
            PTEntry::<A>::spec_from_bits(
                #[trigger] post.phy_view().word_at(post.phy_view().path_id(nroot, vpage, top)),
            ).is_table_spec(top) implies {
            &&& post.phy_view().walk_leaf_ptbl(nroot, top, vpage) == post.phy_view().walk_leaf_ptbl(
                pre.cr3[src],
                top,
                vpage,
            )
            &&& forall|c: WordId| #[trigger]
                post.phy_view().on_walk_path(nroot, top, vpage, c) ==> c == post.phy_view().path_id(
                    nroot,
                    vpage,
                    top,
                ) || post.phy_view().on_walk_path(pre.cr3[src], top, vpage, c)
            &&& forall|f: FrameId| #[trigger]
                post.phy_view().walk_visits(nroot, top, vpage, f) ==> f == nroot
                    || post.phy_view().walk_visits(pre.cr3[src], top, vpage, f)
        } by {
            lemma_walk_leaf_entry_root_copy(post.phy_view(), nroot, pre.cr3[src], top, vpage);
        }
        assert forall|vpage: nat|
            !PTEntry::<A>::spec_from_bits(
                #[trigger] post.phy_view().word_at(post.phy_view().path_id(nroot, vpage, top)),
            ).is_table_spec(top) implies {
            &&& post.phy_view().walk_leaf_ptbl(nroot, top, vpage) == (nroot, top)
            &&& forall|c: WordId| #[trigger]
                post.phy_view().on_walk_path(nroot, top, vpage, c) ==> c == post.phy_view().path_id(
                    nroot,
                    vpage,
                    top,
                )
            &&& forall|f: FrameId| #[trigger]
                post.phy_view().walk_visits(nroot, top, vpage, f) ==> f == nroot
        } by {
            lemma_walk_leaf_ptbl_stops(post.phy_view(), nroot, top, vpage);
        }

        assert forall|k: (nat, nat)| #[trigger] post.vmap_dom.contains(k) implies post.phy_view().translate(
            post.cr3[k.0],
            top,
            k.1,
        ) == walk_target(post.vmap, post.obj_to_frame, k.0, k.1) by {
            let s = if k.0 == a {
                src
            } else {
                k.0
            };
            assert(pre.vmap_dom.contains((s, k.1)));
            assert(post.vmap[k] == pre.vmap[(s, k.1)]) by {
                if k.0 == a {
                    assert(src_vmap.dom().contains((src, k.1)));
                    assert(src_vmap.submap_of(pre.vmap));
                }
            }
            if k.0 == a {
                lemma_translate_root_copy(
                    post.phy_view(),
                    nroot,
                    pre.cr3[src],
                    top,
                    k.1,
                );
            }
        }

        assert forall|k: (nat, nat), c: WordId|
            post.vmap_dom.contains(k) && #[trigger] post.phy_view().on_walk_path(
                post.cr3[k.0],
                top,
                k.1,
                c,
            ) implies post.pt_words.contains(c) by {
            if k.0 == a {
                assert(pre.vmap_dom.contains((src, k.1)));
                if c == post.phy_view().path_id(nroot, k.1, top) {
                    lemma_pgtbl_idx_bounded::<A>(k.1, top);
                    assert(obj_ids::<A>(nobj).contains(c));
                } else {
                    assert(post.phy_view().on_walk_path(pre.cr3[src], top, k.1, c));
                }
            }
        }

        assert(post.leaf_id.dom() =~= post.vmap_dom);
        assert forall|k: (nat, nat)| #[trigger] post.vmap_dom.contains(k) implies post.leaf_id[k]
            == Some(post.phy_view().resting_slot(post.cr3[k.0], top, k.1)) by {
            let s = if k.0 == a {
                src
            } else {
                k.0
            };
            assert(pre.vmap_dom.contains((s, k.1)));
            if k.0 == a {
                lemma_pgtbl_idx_bounded::<A>(k.1, top);
                assert(entry_id::<A>(robj, k.1, top) == WordId((robj.0 + pgtbl_idx::<A>(page_base::<A>(k.1), top) as nat) as nat));
                assert(entry_id::<A>(nobj, k.1, top) == WordId((nobj.0 + pgtbl_idx::<A>(page_base::<A>(k.1), top) as nat) as nat));
                assert(post.phy_view().word_at(
                    entry_id::<A>(nobj, k.1, top),
                ) == words[entry_id::<A>(robj, k.1, top)]);
                assert(post.phy_view().resident(nroot) == nobj);
                assert(mid2.leaf_id[(src, k.1)] == Some(
                    post.phy_view().resting_slot(pre.cr3[src], top, k.1),
                ));
            } else {
                assert(post.leaf_id[k] == pre.leaf_id[k]);
                assert(mid2.leaf_id[k] == Some(
                    post.phy_view().resting_slot(post.cr3[k.0], top, k.1),
                ));
            }
        }
        assert forall|c: WordId| #[trigger] post.pt_words.contains(c) implies c.0 < post.next_oid
            by {}
        assert forall|b1: ObjId, b2: ObjId, off: nat|
            post.obj_to_frame.dom().contains(b1) && #[trigger] post.obj_to_frame.dom().contains(b2)
                && post.obj_to_frame[b1] is Some && post.obj_to_frame[b1]
                == post.obj_to_frame[b2] && off < PTPage::<A>::count() implies #[trigger] post.phy_view().word_at(
            WordId((b1.0 + off) as nat),
        ) == post.phy_view().word_at(WordId((b2.0 + off) as nat)) by {
            if b1 == nobj || b2 == nobj {
                if b1 != nobj {
                    assert(pre.frame_to_objs[nroot].contains(b1));
                }
                if b2 != nobj {
                    assert(pre.frame_to_objs[nroot].contains(b2));
                }
            } else {
                assert(pre.obj_to_frame.dom().contains(b1));
                assert(pre.obj_to_frame.dom().contains(b2));
                assert(b1.0 + PTPage::<A>::count() <= nobj.0);
                assert(b2.0 + PTPage::<A>::count() <= nobj.0);
                assert(!obj_ids::<A>(nobj).contains(WordId((b1.0 + off) as nat)));
                assert(!obj_ids::<A>(nobj).contains(WordId((b2.0 + off) as nat)));
                assert(pre.phy_view().word_at(WordId((b1.0 + off) as nat)) == pre.phy_view().word_at(
                    WordId((b2.0 + off) as nat),
                ));
            }
        }
        assert forall|k: (nat, nat)|
            #[trigger] post.vmap_dom.contains(k) && post.vmap[k] is Some implies post.vmap[k]->Some_0.0
                + PTPage::<A>::count() <= post.next_oid by {
            let s = if k.0 == a {
                src
            } else {
                k.0
            };
            assert(pre.vmap_dom.contains((s, k.1)));
            if k.0 == a {
                assert(src_vmap.dom().contains((src, k.1)));
                assert(src_vmap.submap_of(pre.vmap));
            }
        }
        assert forall|k: (nat, nat), f: FrameId|
            post.vmap_dom.contains(k) && #[trigger] post.phy_view().walk_visits(
                post.cr3[k.0],
                top,
                k.1,
                f,
            ) implies {
                &&& post.allocated.contains(f)
                &&& exists|o: ObjId| post.frame_to_objs[f] =~= Set::<ObjId>::empty().insert(o)
            } by {
            if k.0 == a {
                assert(pre.vmap_dom.contains((src, k.1)));
                if f == nroot {
                    assert(post.frame_to_objs[nroot] =~= Set::<ObjId>::empty().insert(nobj));
                } else {
                    assert(post.phy_view().walk_visits(pre.cr3[src], top, k.1, f));
                }
            }
        }
    }

    /// Every translation is unmoved by a write that touches no table word, which is exactly
    /// what [`lemma_translate_local`] gives.
    #[inductive(write_non_pt)]
    fn write_non_pt_inductive(pre: Self, post: Self, cpu: nat, v: nat, val: usize) {
        let a = pre.cpus[cpu];
        let oid = pre.vmem[(a, v)]->Some_0;
        assert forall|c: WordId| c != oid implies pre.phy_view().word_at(c) == post.phy_view().word_at(c)
            by {}
        assert(!pre.pt_words.contains(oid));
        lemma_words_local::<A>(pre, post, Set::<WordId>::empty().insert(oid));
        assert forall|b1: ObjId, b2: ObjId, off: nat|
            pre.obj_to_frame.dom().contains(b1) && #[trigger] pre.obj_to_frame.dom().contains(b2)
                && pre.obj_to_frame[b1] is Some && pre.obj_to_frame[b1] == pre.obj_to_frame[b2]
                && off < PTPage::<A>::count() implies #[trigger] post.phy_view().word_at(
            WordId((b1.0 + off) as nat),
        ) == post.phy_view().word_at(WordId((b2.0 + off) as nat)) by {
            let obj = obj_of::<A>(oid, v);
            let p = pre.obj_to_frame[obj]->Some_0;
            if WordId((b1.0 + off) as nat) == oid || WordId((b2.0 + off) as nat) == oid {
                assert(obj_ids::<A>(obj).contains(oid));
                assert(obj_ids::<A>(b1).contains(oid) || obj_ids::<A>(b2).contains(oid));
                assert(b1 == obj || b2 == obj);
                assert(pre.obj_to_frame[b1] == Some(p));
                assert(pre.obj_to_frame[b2] == Some(p));
                assert(pre.frame_to_objs[p].contains(b1));
                assert(pre.frame_to_objs[p].contains(b2));
                assert(b1 == b2);
            }
        }
    }

    /// Freezing moves a word between the two halves of `word_at` without changing it, so nothing
    /// The write leaves every walk where it was, so the only thing that moves is what the pages
    /// resting on the written entry map -- and their certificates, which name the object mapped.
    #[inductive(write_pt)]
    fn write_pt_inductive(
        pre: Self,
        post: Self,
        c: WordId,
        obj: ObjId,
        val: usize,
        placement: Map<ObjId, Option<FrameId>>,
        oldmap: Map<(nat, nat), Option<ObjId>>,
        nvmap: Map<(nat, nat), Option<ObjId>>,
        oldmem: Map<(nat, nat), Option<WordId>>,
    ) {
        let affected = pre.vmap_dom.filter(|k: (nat, nat)| pre.leaf_id[k]->Some_0.0 == c);
        assert forall|x: ObjId| #[trigger] placement.dom().contains(x) implies pre.obj_to_frame.dom().contains(
            x,
        ) && pre.obj_to_frame[x] == placement[x] by {}

        assert forall|d: WordId| d != c implies pre.phy_view().word_at(d) == post.phy_view().word_at(
            d,
        ) by {}
        assert forall|d: WordId| #[trigger]
            pre.phy_view().word_at(d) != post.phy_view().word_at(d) implies never_table::<A>(
            pre.phy_view().word_at(d),
        ) && never_table::<A>(post.phy_view().word_at(d)) by {
            assert(d == c);
        }
        assert forall|k: (nat, nat)| #[trigger] pre.vmap_dom.contains(k) implies post.phy_view().resting_slot(
            post.cr3[k.0],
            post.top,
            k.1,
        ) == pre.phy_view().resting_slot(pre.cr3[k.0], pre.top, k.1) by {
            lemma_leaf_write_local::<A>(
                pre.phy_view(),
                post.phy_view(),
                pre.cr3[k.0],
                pre.top,
                k.1,
            );
        }
        assert forall|k: (nat, nat), f: FrameId| pre.vmap_dom.contains(k) implies #[trigger] post.phy_view().walk_visits(
            post.cr3[k.0],
            post.top,
            k.1,
            f,
        ) == pre.phy_view().walk_visits(pre.cr3[k.0], pre.top, k.1, f) by {
            lemma_leaf_write_local::<A>(
                pre.phy_view(),
                post.phy_view(),
                pre.cr3[k.0],
                pre.top,
                k.1,
            );
        }
        assert forall|k: (nat, nat), d: WordId| pre.vmap_dom.contains(k) implies #[trigger] post.phy_view().on_walk_path(
            post.cr3[k.0],
            post.top,
            k.1,
            d,
        ) == pre.phy_view().on_walk_path(pre.cr3[k.0], pre.top, k.1, d) by {
            lemma_leaf_write_local::<A>(
                pre.phy_view(),
                post.phy_view(),
                pre.cr3[k.0],
                pre.top,
                k.1,
            );
        }

        // A walk that does not rest on the written entry reads the same word there as before.
        assert forall|k: (nat, nat)| #[trigger] pre.vmap_dom.contains(k) implies post.phy_view().translate(
            post.cr3[k.0],
            post.top,
            k.1,
        ) == walk_target(post.vmap, post.obj_to_frame, k.0, k.1) by {
            let slot = pre.phy_view().resting_slot(pre.cr3[k.0], pre.top, k.1);
            assert(pre.leaf_id[k] == Some(slot));
            assert(post.phy_view().resting_slot(post.cr3[k.0], post.top, k.1) == slot);
            assert(post.phy_view().translate(post.cr3[k.0], post.top, k.1) == leaf_frame::<A>(
                post.phy_view().word_at(slot.0),
                slot.1,
                k.1,
            ));
            if affected.contains(k) {
                assert(slot.0 == c);
                assert(post.phy_view().word_at(c) == val);
                assert(leaf_frame::<A>(val, slot.1, k.1) == walk_target(
                    nvmap,
                    placement,
                    k.0,
                    k.1,
                ));
                assert(post.vmap[k] == nvmap[k]);
                if nvmap[k] is Some {
                    let o = nvmap[k]->Some_0;
                    assert(placement.dom().contains(o));
                    assert(post.obj_to_frame[o] == placement[o]);
                }
            } else {
                assert(slot.0 != c);
                assert(post.phy_view().word_at(slot.0) == pre.phy_view().word_at(slot.0));
                assert(pre.phy_view().translate(pre.cr3[k.0], pre.top, k.1) == leaf_frame::<A>(
                    pre.phy_view().word_at(slot.0),
                    slot.1,
                    k.1,
                ));
                assert(post.vmap[k] == pre.vmap[k]);
            }
        }

        assert forall|b1: ObjId, b2: ObjId, off: nat|
            pre.obj_to_frame.dom().contains(b1) && #[trigger] pre.obj_to_frame.dom().contains(b2)
                && pre.obj_to_frame[b1] is Some && pre.obj_to_frame[b1] == pre.obj_to_frame[b2]
                && off < PTPage::<A>::count() implies #[trigger] post.phy_view().word_at(
            WordId((b1.0 + off) as nat),
        ) == post.phy_view().word_at(WordId((b2.0 + off) as nat)) by {
            let p = pre.obj_to_frame[obj]->Some_0;
            if WordId((b1.0 + off) as nat) == c || WordId((b2.0 + off) as nat) == c {
                assert(obj_ids::<A>(b1).contains(c) || obj_ids::<A>(b2).contains(c));
                assert(b1 == obj || b2 == obj);
                assert(pre.obj_to_frame[b1] == Some(p));
                assert(pre.obj_to_frame[b2] == Some(p));
                assert(pre.frame_to_objs[p].contains(b1));
                assert(pre.frame_to_objs[p].contains(b2));
                assert(b1 == b2);
            }
        }
    }

    /// Freezing moves a word between the two halves of `word_at` without changing it, so nothing
    /// a walk reads is disturbed.
    #[inductive(freeze)]
    fn freeze_inductive(pre: Self, post: Self, oid: WordId) {
        assert forall|c: WordId| pre.phy_view().word_at(c) == post.phy_view().word_at(c)
            by {}
        lemma_words_local::<A>(pre, post, Set::<WordId>::empty());
    }

    #[inductive(boot)]
    fn boot_inductive(
        post: Self,
        view: PhyMemView<A>,
        obj_to_frame: Map<ObjId, Option<FrameId>>,
        next_oid: nat,
        frames: Set<FrameId>,
        vpages: Set<nat>,
        vaddrs: Set<nat>,
        boot_asid: nat,
        root: FrameId,
        top: PageLevel,
    ) {
        broadcast use vstd::set_lib::group_set_lib_default;

        assert(post.cr3.dom() =~= post.asids);
        assert(post.vmap.dom() =~= post.vmap_dom);
        assert(post.vmem.dom() =~= post.vmem_dom);
        assert(post.phy_view() =~= view) by {
            assert(post.frozen =~= view.frozen);
        }
        assert forall|b1: ObjId, b2: ObjId, off: nat|
            post.obj_to_frame.dom().contains(b1) && #[trigger] post.obj_to_frame.dom().contains(b2)
                && post.obj_to_frame[b1] is Some && post.obj_to_frame[b1] == post.obj_to_frame[b2]
                && off < PTPage::<A>::count()
            implies #[trigger] post.phy_view().word_at(WordId((b1.0 + off) as nat))
                == post.phy_view().word_at(WordId((b2.0 + off) as nat)) by {
            assert(b1 == view.resident(post.obj_to_frame[b1]->Some_0));
        }
        assert forall|k: (nat, nat)| #[trigger] post.vmap_dom.contains(k) implies post.phy_view().translate(
            post.cr3[k.0],
            post.top,
            k.1,
        ) == walk_target(post.vmap, post.obj_to_frame, k.0, k.1) by {
            lemma_skeleton_translate(view, post.allocated, root, post.top, k.1);
        }
        assert forall|k: (nat, nat), f: FrameId|
            post.vmap_dom.contains(k) && #[trigger] post.phy_view().walk_visits(
                post.cr3[k.0],
                post.top,
                k.1,
                f,
            ) implies {
                &&& post.allocated.contains(f)
                &&& exists|o: ObjId| post.frame_to_objs[f] =~= Set::<ObjId>::empty().insert(o)
            } by {
            lemma_skeleton_visits(view, post.allocated, root, post.top, k.1, f);
            assert(post.frame_to_objs[f] =~= Set::<ObjId>::empty().insert(view.resident(f)));
        }
        assert forall|k: (nat, nat), c: WordId|
            post.vmap_dom.contains(k) && #[trigger] post.phy_view().on_walk_path(
                post.cr3[k.0],
                post.top,
                k.1,
                c,
            ) implies post.pt_words.contains(c) by {
            assert forall|g: FrameId| #[trigger] post.allocated.contains(g) implies obj_ids::<A>(
                view.resident(g),
            ).subset_of(post.pt_words) by {
                assert(obj_to_frame.dom().contains(view.resident(g)));
            }
            lemma_skeleton_on_path(view, post.allocated, post.pt_words, root, post.top, k.1, c);
        }
    }
});

verus! {

/// A walk over a skeleton stands only in the skeleton's own pages.
pub proof fn lemma_skeleton_visits<A: ArchPagingMeta>(
    view: PhyMemView<A>,
    frames: Set<FrameId>,
    frame: FrameId,
    level: PageLevel,
    vpage: nat,
    f: FrameId,
)
    requires
        view.skeleton_walk(frames, frame, level, vpage),
        frames.contains(frame),
        view.walk_visits(frame, level, vpage, f),
    ensures
        frames.contains(f),
    decreases level.depth(),
{
    let e = PTEntry::<A>::spec_from_bits(view.word_at(view.path_id(frame, vpage, level)));
    if e.is_table_spec(level) {
        lemma_walk_step(view, frame, level, vpage);
        let next = FrameId(e.page_frame_spec() as nat);
        let child = level.spec_child()->Some_0;
        if f != frame {
            lemma_skeleton_visits(view, frames, next, child, vpage, f);
        }
    } else {
        lemma_walk_leaf_ptbl_stops(view, frame, level, vpage);
    }
}

/// A walk over a skeleton reads only words the skeleton's own pages hold.
pub proof fn lemma_skeleton_on_path<A: ArchPagingMeta>(
    view: PhyMemView<A>,
    frames: Set<FrameId>,
    words: Set<WordId>,
    frame: FrameId,
    level: PageLevel,
    vpage: nat,
    c: WordId,
)
    requires
        view.skeleton_walk(frames, frame, level, vpage),
        frames.contains(frame),
        forall|g: FrameId| #[trigger]
            frames.contains(g) ==> obj_ids::<A>(view.resident(g)).subset_of(words),
        view.on_walk_path(frame, level, vpage, c),
    ensures
        words.contains(c),
    decreases level.depth(),
{
    lemma_pgtbl_idx_bounded::<A>(vpage, level);
    assert(obj_ids::<A>(view.resident(frame)).contains(view.path_id(frame, vpage, level)));
    let e = PTEntry::<A>::spec_from_bits(view.word_at(view.path_id(frame, vpage, level)));
    if e.is_table_spec(level) {
        lemma_walk_step(view, frame, level, vpage);
        let next = FrameId(e.page_frame_spec() as nat);
        let child = level.spec_child()->Some_0;
        if c != view.path_id(frame, vpage, level) {
            lemma_skeleton_on_path(view, frames, words, next, child, vpage, c);
        }
    } else {
        lemma_walk_leaf_ptbl_stops(view, frame, level, vpage);
    }
}

/// A skeleton maps nothing: every walk over it comes to rest on an entry that is not a mapping.
pub proof fn lemma_skeleton_translate<A: ArchPagingMeta>(
    view: PhyMemView<A>,
    frames: Set<FrameId>,
    frame: FrameId,
    level: PageLevel,
    vpage: nat,
)
    requires
        view.skeleton_walk(frames, frame, level, vpage),
        frames.contains(frame),
    ensures
        view.translate(frame, level, vpage) is None,
    decreases level.depth(),
{
    let e = PTEntry::<A>::spec_from_bits(view.word_at(view.path_id(frame, vpage, level)));
    if e.is_table_spec(level) {
        lemma_walk_step(view, frame, level, vpage);
        let next = FrameId(e.page_frame_spec() as nat);
        let child = level.spec_child()->Some_0;
        lemma_skeleton_translate(view, frames, next, child, vpage);
    } else {
        lemma_walk_leaf_ptbl_stops(view, frame, level, vpage);
    }
}

/// A tree whose entries are all absent stops the walk at the root, and so is the simplest
/// skeleton [`boot`](Mem::State::boot) accepts.
pub proof fn lemma_absent_root_skeleton<A: ArchPagingMeta>(
    view: PhyMemView<A>,
    frames: Set<FrameId>,
    root: FrameId,
    top: PageLevel,
    vpage: nat,
)
    requires
        forall|c: WordId| #[trigger] obj_ids::<A>(view.resident(root)).contains(c)
            ==> view.word_at(c) == absent_word(),
    ensures
        view.walk_leaf_ptbl(root, top, vpage) == (root, top),
        view.skeleton_walk(frames, root, top, vpage),
{
    lemma_absent_word::<A>();
    lemma_pgtbl_idx_bounded::<A>(vpage, top);
    assert(obj_ids::<A>(view.resident(root)).contains(view.path_id(root, vpage, top)));
    lemma_walk_leaf_ptbl_stops(view, root, top, vpage);
}

/// A lone root of absent entries meets every condition [`boot`](Mem::State::boot) imposes, so the
/// state machine is startable: the preconditions that let it accept richer tables rule nothing in
/// that the empty address space needed.
pub proof fn lemma_boot_absent_root<A: ArchPagingMeta>(root: FrameId, top: PageLevel, vpage: nat)
    ensures
        ({
            let view = PhyMemView::<A> {
                data: Map::new(obj_ids::<A>(ObjId(0)), |c: WordId| absent_word()),
                frozen: Map::empty(),
                frame_to_objs: Map::<FrameId, Set<ObjId>>::empty().insert(
                    root,
                    Set::<ObjId>::empty().insert(ObjId(0)),
                ),
                marker: PhantomData,
            };
            let obj_to_frame = Map::<ObjId, Option<FrameId>>::empty().insert(ObjId(0), Some(root));
            let next_oid = PTPage::<A>::count();
            &&& view.frozen =~= Map::<WordId, usize>::empty()
            &&& view.frame_to_objs.dom().contains(root)
            &&& forall|f: FrameId| #[trigger] view.frame_to_objs.dom().contains(f)
                ==> view.frame_to_objs[f] =~= Set::<ObjId>::empty().insert(view.resident(f))
            &&& forall|f: FrameId| #[trigger] view.frame_to_objs.dom().contains(f) ==> {
                &&& obj_to_frame.dom().contains(view.resident(f))
                &&& obj_to_frame[view.resident(f)] == Some(f)
            }
            &&& forall|b: ObjId| #[trigger] obj_to_frame.dom().contains(b) ==> {
                &&& obj_to_frame[b] is Some
                &&& view.frame_to_objs.dom().contains(obj_to_frame[b]->Some_0)
                &&& view.resident(obj_to_frame[b]->Some_0) == b
                &&& obj_ids::<A>(b).subset_of(view.data.dom())
            }
            &&& forall|b1: ObjId, b2: ObjId, c: WordId|
                obj_to_frame.dom().contains(b1) && #[trigger] obj_to_frame.dom().contains(b2)
                    && #[trigger] obj_ids::<A>(b1).contains(c) && obj_ids::<A>(b2).contains(c)
                    ==> b1 == b2
            &&& forall|c: WordId| #[trigger] view.data.dom().contains(c) ==> c.0 < next_oid
            &&& forall|b: ObjId| #[trigger] obj_to_frame.dom().contains(b)
                ==> b.0 + PTPage::<A>::count() <= next_oid
            &&& view.skeleton_walk(view.frame_to_objs.dom(), root, top, vpage)
        }),
{
    let view = PhyMemView::<A> {
        data: Map::new(obj_ids::<A>(ObjId(0)), |c: WordId| absent_word()),
        frozen: Map::empty(),
        frame_to_objs: Map::<FrameId, Set<ObjId>>::empty().insert(
            root,
            Set::<ObjId>::empty().insert(ObjId(0)),
        ),
        marker: PhantomData,
    };
    PTPage::<A>::lemma_count_positive();
    broadcast use vstd::set_lib::group_set_lib_default;

    assert(view.frame_to_objs[root].contains(ObjId(0)));
    assert(view.resident(root) == ObjId(0));
    lemma_absent_root_skeleton::<A>(view, view.frame_to_objs.dom(), root, top, vpage);
}

/// The words a walk of `vpage` reads are untouched by a step that changes only `oid`, a word no
/// table holds.
pub proof fn lemma_path_words<A: ArchPagingMeta>(
    pre: Mem::State<A>,
    post: Mem::State<A>,
    touched: Set<WordId>,
    k: (nat, nat),
)
    requires
        pre.paths_in_tables(),
        pre.vmap_dom.contains(k),
        forall|c: WordId| #[trigger] touched.contains(c) ==> !pre.pt_words.contains(c),
        forall|c: WordId| !touched.contains(c) ==> pre.phy_view().word_at(c) == post.phy_view().word_at(c),
    ensures
        forall|c: WordId| #[trigger]
            pre.phy_view().on_walk_path(pre.cr3[k.0], pre.top, k.1, c)
                ==> pre.phy_view().word_at(c) == post.phy_view().word_at(c),
{
    assert forall|c: WordId| #[trigger]
        pre.phy_view().on_walk_path(
            pre.cr3[k.0],
            pre.top,
            k.1,
            c,
        ) implies pre.phy_view().word_at(c) == post.phy_view().word_at(c) by {
        if touched.contains(c) {
            assert(!pre.pt_words.contains(c));
        }
    }
}

/// A step that only changes where frames outside `live` stand leaves every walk alone. Walks
/// stay within `live` because they visit only allocated frames with a single resident, which
/// is what [`path_frames_solo`](Mem::State::path_frames_solo) says.
pub proof fn lemma_frames_local<A: ArchPagingMeta>(
    pre: Mem::State<A>,
    post: Mem::State<A>,
    live: Set<FrameId>,
)
    requires
        pre.paths_in_tables(),
        pre.walk_agrees(),
        pre.path_frames_solo(),
        pre.leaf_ids_agree(),
        pre.root_placed(),
        pre.pages_bounded(),
        forall|f: FrameId| #[trigger]
            live.contains(f) ==> pre.frame_to_objs[f] == post.frame_to_objs[f],
        forall|f: FrameId|
            #[trigger] pre.allocated.contains(f) && (exists|o: ObjId|
                pre.frame_to_objs[f] =~= Set::<ObjId>::empty().insert(o)) ==> live.contains(f),
        post.data == pre.data,
        post.frozen == pre.frozen,
        post.cr3 == pre.cr3,
        post.asids == pre.asids,
        post.top == pre.top,
        post.vmap == pre.vmap,
        post.vmap_dom == pre.vmap_dom,
        post.obj_to_frame == pre.obj_to_frame,
        post.pt_words == pre.pt_words,
        post.leaf_id == pre.leaf_id,
    ensures
        post.walk_agrees(),
        post.paths_in_tables(),
        post.leaf_ids_agree(),
        forall|k: (nat, nat), f: FrameId|
            #![trigger post.phy_view().walk_visits(post.cr3[k.0], post.top, k.1, f)]
            #![trigger pre.phy_view().walk_visits(pre.cr3[k.0], pre.top, k.1, f)]
            pre.vmap_dom.contains(k) ==> post.phy_view().walk_visits(
                post.cr3[k.0],
                post.top,
                k.1,
                f,
            ) == pre.phy_view().walk_visits(pre.cr3[k.0], pre.top, k.1, f),
{
    assert forall|k: (nat, nat), f: FrameId|
        pre.vmap_dom.contains(k) && #[trigger] pre.phy_view().walk_visits(
            pre.cr3[k.0],
            pre.top,
            k.1,
            f,
        ) implies live.contains(f) by {
        assert(pre.allocated.contains(f));
    }
    assert forall|k: (nat, nat), f: FrameId| pre.vmap_dom.contains(k) implies #[trigger] post.phy_view().walk_visits(
        post.cr3[k.0],
        post.top,
        k.1,
        f,
    ) == pre.phy_view().walk_visits(pre.cr3[k.0], pre.top, k.1, f) by {
        lemma_walk_leaf_entry_frames(
            pre.phy_view(),
            post.phy_view(),
            live,
            pre.cr3[k.0],
            pre.top,
            k.1,
        );
    }
    assert forall|k: (nat, nat)| #[trigger] post.vmap_dom.contains(k) implies post.phy_view().translate(
        post.cr3[k.0],
        post.top,
        k.1,
    ) == walk_target(post.vmap, post.obj_to_frame, k.0, k.1) && post.leaf_id[k] == Some(
        post.phy_view().resting_slot(post.cr3[k.0], post.top, k.1),
    ) by {
        lemma_translate_frames(
            pre.phy_view(),
            post.phy_view(),
            live,
            pre.cr3[k.0],
            pre.top,
            k.1,
        );
    }
    assert forall|k: (nat, nat), c: WordId|
        post.vmap_dom.contains(k) && #[trigger] post.phy_view().on_walk_path(
            post.cr3[k.0],
            post.top,
            k.1,
            c,
        ) implies post.pt_words.contains(c) by {
        lemma_walk_leaf_entry_frames(
            pre.phy_view(),
            post.phy_view(),
            live,
            pre.cr3[k.0],
            pre.top,
            k.1,
        );
        assert(pre.phy_view().on_walk_path(pre.cr3[k.0], pre.top, k.1, c));
    }
}

/// A step that leaves every table word alone leaves every walk alone: where a page leads, which
/// frames the walk visits and which words it reads are all unchanged.
pub proof fn lemma_words_local<A: ArchPagingMeta>(
    pre: Mem::State<A>,
    post: Mem::State<A>,
    touched: Set<WordId>,
)
    requires
        pre.paths_in_tables(),
        pre.walk_agrees(),
        pre.path_frames_solo(),
        pre.leaf_ids_agree(),
        pre.root_placed(),
        pre.pages_bounded(),
        forall|c: WordId| #[trigger] touched.contains(c) ==> !pre.pt_words.contains(c),
        post.frame_to_objs == pre.frame_to_objs,
        post.frames_dom == pre.frames_dom,
        post.cr3 == pre.cr3,
        post.asids == pre.asids,
        post.top == pre.top,
        post.vmap == pre.vmap,
        post.vmap_dom == pre.vmap_dom,
        post.obj_to_frame == pre.obj_to_frame,
        post.leaf_id == pre.leaf_id,
        pre.pt_words.subset_of(post.pt_words),
        post.allocated == pre.allocated,
        forall|c: WordId| !touched.contains(c) ==> pre.phy_view().word_at(c) == post.phy_view().word_at(c),
    ensures
        post.walk_agrees(),
        post.path_frames_solo(),
        post.paths_in_tables(),
        post.leaf_ids_agree(),
        forall|k: (nat, nat)|
            #![trigger post.phy_view().walk_leaf_ptbl(post.cr3[k.0], post.top, k.1)]
            #![trigger pre.phy_view().walk_leaf_ptbl(pre.cr3[k.0], pre.top, k.1)]
            pre.vmap_dom.contains(k) ==> post.phy_view().walk_leaf_ptbl(
                post.cr3[k.0],
                post.top,
                k.1,
            ) == pre.phy_view().walk_leaf_ptbl(pre.cr3[k.0], pre.top, k.1),
        forall|k: (nat, nat), f: FrameId|
            #![trigger post.phy_view().walk_visits(post.cr3[k.0], post.top, k.1, f)]
            #![trigger pre.phy_view().walk_visits(pre.cr3[k.0], pre.top, k.1, f)]
            pre.vmap_dom.contains(k) ==> post.phy_view().walk_visits(
                post.cr3[k.0],
                post.top,
                k.1,
                f,
            ) == pre.phy_view().walk_visits(pre.cr3[k.0], pre.top, k.1, f),
        forall|k: (nat, nat), c: WordId|
            #![trigger post.phy_view().on_walk_path(post.cr3[k.0], post.top, k.1, c)]
            #![trigger pre.phy_view().on_walk_path(pre.cr3[k.0], pre.top, k.1, c)]
            pre.vmap_dom.contains(k) ==> post.phy_view().on_walk_path(
                post.cr3[k.0],
                post.top,
                k.1,
                c,
            ) == pre.phy_view().on_walk_path(pre.cr3[k.0], pre.top, k.1, c),
{
    assert forall|k: (nat, nat)| pre.vmap_dom.contains(k) implies #[trigger] post.phy_view().walk_leaf_ptbl(
        post.cr3[k.0],
        post.top,
        k.1,
    ) == pre.phy_view().walk_leaf_ptbl(pre.cr3[k.0], pre.top, k.1) by {
        lemma_path_words::<A>(pre, post, touched, k);
        lemma_walk_leaf_entry_local(pre.phy_view(), post.phy_view(), pre.cr3[k.0], pre.top, k.1);
    }
    assert forall|k: (nat, nat), f: FrameId| pre.vmap_dom.contains(k) implies #[trigger] post.phy_view().walk_visits(
        post.cr3[k.0],
        post.top,
        k.1,
        f,
    ) == pre.phy_view().walk_visits(pre.cr3[k.0], pre.top, k.1, f) by {
        lemma_path_words::<A>(pre, post, touched, k);
        lemma_walk_leaf_entry_local(pre.phy_view(), post.phy_view(), pre.cr3[k.0], pre.top, k.1);
    }
    assert forall|k: (nat, nat), c: WordId| pre.vmap_dom.contains(k) implies #[trigger] post.phy_view().on_walk_path(
        post.cr3[k.0],
        post.top,
        k.1,
        c,
    ) == pre.phy_view().on_walk_path(pre.cr3[k.0], pre.top, k.1, c) by {
        lemma_path_words::<A>(pre, post, touched, k);
        lemma_walk_leaf_entry_local(pre.phy_view(), post.phy_view(), pre.cr3[k.0], pre.top, k.1);
    }
    assert forall|k: (nat, nat)| #[trigger] post.vmap_dom.contains(k) implies post.phy_view().translate(
        post.cr3[k.0],
        post.top,
        k.1,
    ) == walk_target(post.vmap, post.obj_to_frame, k.0, k.1) && post.leaf_id[k] == Some(
        post.phy_view().resting_slot(post.cr3[k.0], post.top, k.1),
    ) by {
        lemma_path_words::<A>(pre, post, touched, k);
        lemma_translate_local(pre.phy_view(), post.phy_view(), pre.cr3[k.0], pre.top, k.1);
    }
    assert forall|k: (nat, nat), c: WordId|
        post.vmap_dom.contains(k) && #[trigger] post.phy_view().on_walk_path(
            post.cr3[k.0],
            post.top,
            k.1,
            c,
        ) implies post.pt_words.contains(c) by {
        assert(pre.phy_view().on_walk_path(pre.cr3[k.0], pre.top, k.1, c));
    }
    assert forall|k: (nat, nat), f: FrameId|
        post.vmap_dom.contains(k) && #[trigger] post.phy_view().walk_visits(
            post.cr3[k.0],
            post.top,
            k.1,
            f,
        ) implies {
        &&& post.allocated.contains(f)
        &&& exists|o: ObjId| post.frame_to_objs[f] =~= Set::<ObjId>::empty().insert(o)
    } by {
        assert(pre.phy_view().walk_visits(pre.cr3[k.0], pre.top, k.1, f));
    }
}

} // verus!
