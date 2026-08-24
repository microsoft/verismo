//! A model of content, physical frames, page tables, and virtual aliases, as a tokenized state
//! machine -- with the page table modelled as a *tree*, walked from a frame, exactly as hardware
//! walks it.
use core::marker::PhantomData;

use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use vstd::arithmetic::power::pow;
use vstd::prelude::*;

use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlagsSpec};
use crate::structs::entry::PTEntry;
use crate::structs::level::PageLevel;
use crate::structs::ptpage::PTPage;
use verus_state_machines_macros::tokenized_state_machine;

verus! {

/// Entry index a page number selects `level` levels above the leaf: its digits in base
/// `PTPage::<A>::count()`.
pub open spec fn vindex<A: ArchPagingMeta>(vp: nat, level: nat) -> nat
    decreases level,
{
    if level == 0 {
        vp % PTPage::<A>::count()
    } else {
        vindex::<A>(vp / PTPage::<A>::count(), (level - 1) as nat)
    }
}

/// Id of the word an entry occupies.
pub open spec fn entry_id<A: ArchPagingMeta>(table: nat, vp: nat, level: nat) -> nat {
    (table + vindex::<A>(vp, level)) as nat
}

/// A word, wherever it lives. Content is writable or frozen, never both.
pub open spec fn word_at(data: Map<nat, usize>, frozen: Map<nat, usize>, c: nat) -> usize {
    if data.dom().contains(c) {
        data[c]
    } else {
        frozen[c]
    }
}

/// The object living in a frame. A walk lands on a frame but must go on reading words. Well
/// defined only because page table pages are their frame's sole residents.
pub open spec fn resident(frame_to_objs: Map<nat, Set<nat>>, frame: nat) -> nat {
    frame_to_objs[frame].choose()
}

/// The model counts levels from the leaf as a `nat`; the entry decoder names them by `PageLevel`.
pub open spec fn plevel(level: nat) -> PageLevel {
    PageLevel::spec_from_depth(level)
}

/// Where a walk of `vp` stands once it has descended from `cr3` to `level`, or `None` if the
/// walk stopped above it.
///
/// A function of memory alone, and keyed on the level rather than on the page, so a frame that
/// is reached at two levels -- a self-mapped table -- gets a separate answer at each.
pub open spec fn frame_at<A: ArchPagingMeta>(
    data: Map<nat, usize>,
    frozen: Map<nat, usize>,
    frame_to_objs: Map<nat, Set<nat>>,
    cr3: nat,
    top: nat,
    level: nat,
    vp: nat,
) -> Option<nat>
    decreases top - level,
{
    if level >= top {
        Some(cr3)
    } else {
        match frame_at::<A>(data, frozen, frame_to_objs, cr3, top, (level + 1) as nat, vp) {
            Option::None => Option::None,
            Option::Some(f) => {
                let e = PTEntry::<A>::spec_from_bits(
                    word_at(data, frozen, path_id::<A>(frame_to_objs, f, vp, (level + 1) as nat)),
                );
                if e.is_table_spec(plevel((level + 1) as nat)) {
                    Some(e.page_frame_spec() as nat)
                } else {
                    Option::None
                }
            },
        }
    }
}

/// Id of the entry a walk of `vp` reads while standing in `frame` at `level`.
pub open spec fn path_id<A: ArchPagingMeta>(
    frame_to_objs: Map<nat, Set<nat>>,
    frame: nat,
    vp: nat,
    level: nat,
) -> nat {
    entry_id::<A>(resident(frame_to_objs, frame), vp, level)
}

/// The frame `vp` translates to: the whole walk, from `cr3` down to a leaf. Consults nothing but
/// memory, so agreeing with it is a real obligation on the words stored.
pub open spec fn translate<A: ArchPagingMeta>(
    data: Map<nat, usize>,
    frozen: Map<nat, usize>,
    frame_to_objs: Map<nat, Set<nat>>,
    cr3: nat,
    top: nat,
    vp: nat,
) -> Option<nat> {
    match frame_at::<A>(data, frozen, frame_to_objs, cr3, top, 0, vp) {
        Option::None => Option::None,
        Option::Some(f) => {
            let e = PTEntry::<A>::spec_from_bits(
                word_at(data, frozen, path_id::<A>(frame_to_objs, f, vp, 0)),
            );
            if e.is_leaf_spec(plevel(0)) {
                Some(e.page_frame_spec() as nat)
            } else {
                Option::None
            }
        },
    }
}

/// Id of the entry a walk of `vp` reads at `level`, if the walk gets that far.
pub open spec fn path_id_at<A: ArchPagingMeta>(
    data: Map<nat, usize>,
    frozen: Map<nat, usize>,
    frame_to_objs: Map<nat, Set<nat>>,
    cr3: nat,
    top: nat,
    level: nat,
    vp: nat,
) -> Option<nat> {
    match frame_at::<A>(data, frozen, frame_to_objs, cr3, top, level, vp) {
        Option::None => Option::None,
        Option::Some(f) => Some(path_id::<A>(frame_to_objs, f, vp, level)),
    }
}

/// Whether `c` is one of the entries a walk of `vp` reads. Changing anything else cannot change
/// where `vp` leads, which is what [`lemma_translate_local`] states and every transition leans on.
pub open spec fn on_path<A: ArchPagingMeta>(
    data: Map<nat, usize>,
    frozen: Map<nat, usize>,
    frame_to_objs: Map<nat, Set<nat>>,
    cr3: nat,
    top: nat,
    vp: nat,
    c: nat,
) -> bool {
    exists|l: nat|
        l <= top && #[trigger] path_id_at::<A>(data, frozen, frame_to_objs, cr3, top, l, vp) == Some(
            c,
        )
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
        PTEntry::<A>::spec_from_bits(leaf_word::<A>(frame)).is_leaf_spec(plevel(0)),
        PTEntry::<A>::spec_from_bits(leaf_word::<A>(frame)).page_frame_spec() == frame,
{
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

pub proof fn lemma_table_word<A: ArchPagingMeta>(frame: usize, level: nat)
    requires
        encodable::<A>(frame),
        level > 0,
    ensures
        PTEntry::<A>::spec_from_bits(table_word::<A>(frame)).is_table_spec(plevel(level)),
        PTEntry::<A>::spec_from_bits(table_word::<A>(frame)).page_frame_spec() == frame,
{
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

/// An entry always lies inside its table page.
pub proof fn lemma_vindex_bounded<A: ArchPagingMeta>(vp: nat, level: nat)
    requires
        PTPage::<A>::count() > 0,
    ensures
        vindex::<A>(vp, level) < PTPage::<A>::count(),
    decreases level,
{
    if level > 0 {
        lemma_vindex_bounded::<A>(vp / PTPage::<A>::count(), (level - 1) as nat);
    }
}

/// Two pages the walk cannot tell apart at any level are the same page, so an entry belongs to
/// exactly one page.
pub proof fn lemma_vindex_injective<A: ArchPagingMeta>(vp1: nat, vp2: nat, levels: nat)
    requires
        PTPage::<A>::count() > 0,
        vp1 < pow(PTPage::<A>::count() as int, levels as nat),
        vp2 < pow(PTPage::<A>::count() as int, levels as nat),
        forall|l: nat| l < levels ==> vindex::<A>(vp1, l) == vindex::<A>(vp2, l),
    ensures
        vp1 == vp2,
    decreases levels,
{
    let e = PTPage::<A>::count();
    if levels == 0 {
        vstd::arithmetic::power::lemma_pow0(e as int);
    } else {
        vstd::arithmetic::power::lemma_pow_adds(e as int, 1, (levels - 1) as nat);
        vstd::arithmetic::power::lemma_pow1(e as int);
        vstd::arithmetic::power::lemma_pow_positive(e as int, (levels - 1) as nat);
        vstd::arithmetic::div_mod::lemma_multiply_divide_lt(
            vp1 as int,
            e as int,
            pow(e as int, (levels - 1) as nat),
        );
        vstd::arithmetic::div_mod::lemma_multiply_divide_lt(
            vp2 as int,
            e as int,
            pow(e as int, (levels - 1) as nat),
        );
        assert forall|l: nat| l + 1 < levels implies #[trigger] vindex::<A>(vp1 / e, l)
            == vindex::<A>(vp2 / e, l) by {
            assert(vindex::<A>(vp1, l + 1) == vindex::<A>(vp2, l + 1));
        }
        lemma_vindex_injective::<A>(vp1 / e, vp2 / e, (levels - 1) as nat);
        assert(vindex::<A>(vp1, 0) == vindex::<A>(vp2, 0));
        lemma_fundamental_div_mod(vp1 as int, e as int);
        lemma_fundamental_div_mod(vp2 as int, e as int);
    }
}


/// A walk of `vp` sees only the entries it reads, so anything else may change under it.
pub proof fn lemma_frame_at_local<A: ArchPagingMeta>(
    d1: Map<nat, usize>,
    f1: Map<nat, usize>,
    d2: Map<nat, usize>,
    f2: Map<nat, usize>,
    frame_to_objs: Map<nat, Set<nat>>,
    cr3: nat,
    top: nat,
    level: nat,
    vp: nat,
)
    requires
        level <= top,
        forall|c: nat| #[trigger]
            on_path::<A>(d1, f1, frame_to_objs, cr3, top, vp, c) ==> word_at(d1, f1, c) == word_at(
                d2,
                f2,
                c,
            ),
    ensures
        frame_at::<A>(d1, f1, frame_to_objs, cr3, top, level, vp) == frame_at::<A>(
            d2,
            f2,
            frame_to_objs,
            cr3,
            top,
            level,
            vp,
        ),
    decreases top - level,
{
    if level < top {
        let up = (level + 1) as nat;
        lemma_frame_at_local::<A>(d1, f1, d2, f2, frame_to_objs, cr3, top, up, vp);
        if let Option::Some(c) = path_id_at::<A>(d1, f1, frame_to_objs, cr3, top, up, vp) {
            assert(on_path::<A>(d1, f1, frame_to_objs, cr3, top, vp, c)) by {
                assert(path_id_at::<A>(d1, f1, frame_to_objs, cr3, top, up, vp) == Some(c));
            }
        }
    }
}

/// Where `vp` leads depends only on the entries its own walk reads. This is what lets a
/// transition that rewrites entries elsewhere leave every other translation alone.
/// Where a walk goes depends only on the residents of the frames it lands on, so changing the
/// placement of a frame no walk lands on moves nothing. `live` names the frames the walks in
/// question stay within.
pub proof fn lemma_frame_at_frames<A: ArchPagingMeta>(
    data: Map<nat, usize>,
    frozen: Map<nat, usize>,
    m1: Map<nat, Set<nat>>,
    m2: Map<nat, Set<nat>>,
    live: Set<nat>,
    cr3: nat,
    top: nat,
    level: nat,
    vp: nat,
)
    requires
        forall|f: nat| #[trigger] live.contains(f) ==> m1[f] == m2[f],
        forall|l: nat|
            l <= top && #[trigger] frame_at::<A>(data, frozen, m1, cr3, top, l, vp) is Some
                ==> live.contains(frame_at::<A>(data, frozen, m1, cr3, top, l, vp)->Some_0),
    ensures
        frame_at::<A>(data, frozen, m1, cr3, top, level, vp) == frame_at::<A>(
            data,
            frozen,
            m2,
            cr3,
            top,
            level,
            vp,
        ),
    decreases top - level,
{
    if level < top {
        lemma_frame_at_frames::<A>(data, frozen, m1, m2, live, cr3, top, (level + 1) as nat, vp);
    }
}

/// Two roots holding equal entries lead a walk to the same place at every level below the top,
/// which is what makes a copied root page a faithful clone of an address space.
pub proof fn lemma_frame_at_root_copy<A: ArchPagingMeta>(
    data: Map<nat, usize>,
    frozen: Map<nat, usize>,
    frame_to_objs: Map<nat, Set<nat>>,
    r1: nat,
    r2: nat,
    top: nat,
    level: nat,
    vp: nat,
)
    requires
        PTPage::<A>::count() > 0,
        level < top,
        forall|i: nat| i < PTPage::<A>::count() ==> #[trigger] word_at(
            data,
            frozen,
            (resident(frame_to_objs, r1) + i) as nat,
        ) == word_at(data, frozen, (resident(frame_to_objs, r2) + i) as nat),
    ensures
        frame_at::<A>(data, frozen, frame_to_objs, r1, top, level, vp) == frame_at::<A>(
            data,
            frozen,
            frame_to_objs,
            r2,
            top,
            level,
            vp,
        ),
    decreases top - level,
{
    if level + 1 < top {
        lemma_frame_at_root_copy::<A>(
            data,
            frozen,
            frame_to_objs,
            r1,
            r2,
            top,
            (level + 1) as nat,
            vp,
        );
    } else {
        lemma_vindex_bounded::<A>(vp, top);
        assert(frame_at::<A>(data, frozen, frame_to_objs, r1, top, (level + 1) as nat, vp) == Some(
            r1,
        ));
        assert(frame_at::<A>(data, frozen, frame_to_objs, r2, top, (level + 1) as nat, vp) == Some(
            r2,
        ));
        assert(path_id::<A>(frame_to_objs, r1, vp, (level + 1) as nat) == (resident(
            frame_to_objs,
            r1,
        ) + vindex::<A>(vp, top)) as nat);
        assert(path_id::<A>(frame_to_objs, r2, vp, (level + 1) as nat) == (resident(
            frame_to_objs,
            r2,
        ) + vindex::<A>(vp, top)) as nat);
        assert(word_at(data, frozen, (resident(frame_to_objs, r1) + vindex::<A>(vp, top)) as nat)
            == word_at(
            data,
            frozen,
            (resident(frame_to_objs, r2) + vindex::<A>(vp, top)) as nat,
        ));
    }
}

/// A copied root translates every page exactly as the root it was copied from.
pub proof fn lemma_translate_root_copy<A: ArchPagingMeta>(
    data: Map<nat, usize>,
    frozen: Map<nat, usize>,
    frame_to_objs: Map<nat, Set<nat>>,
    r1: nat,
    r2: nat,
    top: nat,
    vp: nat,
)
    requires
        PTPage::<A>::count() > 0,
        forall|i: nat| i < PTPage::<A>::count() ==> #[trigger] word_at(
            data,
            frozen,
            (resident(frame_to_objs, r1) + i) as nat,
        ) == word_at(data, frozen, (resident(frame_to_objs, r2) + i) as nat),
    ensures
        translate::<A>(data, frozen, frame_to_objs, r1, top, vp) == translate::<A>(
            data,
            frozen,
            frame_to_objs,
            r2,
            top,
            vp,
        ),
{
    if top > 0 {
        lemma_frame_at_root_copy::<A>(data, frozen, frame_to_objs, r1, r2, top, 0, vp);
    } else {
        lemma_vindex_bounded::<A>(vp, 0);
    }
}

pub proof fn lemma_translate_local<A: ArchPagingMeta>(
    d1: Map<nat, usize>,
    f1: Map<nat, usize>,
    d2: Map<nat, usize>,
    f2: Map<nat, usize>,
    frame_to_objs: Map<nat, Set<nat>>,
    cr3: nat,
    top: nat,
    vp: nat,
)
    requires
        forall|c: nat| #[trigger]
            on_path::<A>(d1, f1, frame_to_objs, cr3, top, vp, c) ==> word_at(d1, f1, c) == word_at(
                d2,
                f2,
                c,
            ),
    ensures
        translate::<A>(d1, f1, frame_to_objs, cr3, top, vp) == translate::<A>(
            d2,
            f2,
            frame_to_objs,
            cr3,
            top,
            vp,
        ),
{
    lemma_frame_at_local::<A>(d1, f1, d2, f2, frame_to_objs, cr3, top, 0, vp);
    if let Option::Some(c) = path_id_at::<A>(d1, f1, frame_to_objs, cr3, top, 0, vp) {
        assert(on_path::<A>(d1, f1, frame_to_objs, cr3, top, vp, c)) by {
            assert(path_id_at::<A>(d1, f1, frame_to_objs, cr3, top, 0, vp) == Some(c));
        }
    }
}

} // verus!

verus! {

/// The page a virtual address falls in.
pub open spec fn vpage<A: ArchPagingMeta>(v: nat) -> nat {
    v / PTPage::<A>::count()
}

/// How far into its page a virtual address sits.
pub open spec fn voffset<A: ArchPagingMeta>(v: nat) -> nat {
    v % PTPage::<A>::count()
}

/// The ids an object covers.
pub open spec fn obj_ids<A: ArchPagingMeta>(obj: nat) -> Set<nat> {
    Set::range(obj, obj + PTPage::<A>::count())
}

/// The id an address reaches in `obj`.
pub open spec fn oid_of<A: ArchPagingMeta>(obj: nat, v: nat) -> nat {
    obj + voffset::<A>(v)
}

/// The object a certificate came from, recovered from the address it certifies.
pub open spec fn obj_of<A: ArchPagingMeta>(oid: nat, v: nat) -> nat {
    (oid - voffset::<A>(v)) as nat
}

/// The governed addresses of one page of one address space.
pub open spec fn page_addrs<A: ArchPagingMeta>(dom: Set<(nat, nat)>, a: nat, vp: nat) -> Set<
    (nat, nat),
> {
    dom.filter(|k: (nat, nat)| k.0 == a && vpage::<A>(k.1) == vp)
}

/// The certificates of one page, all reading `oid`.
pub open spec fn page_view<A: ArchPagingMeta>(
    dom: Set<(nat, nat)>,
    a: nat,
    vp: nat,
    oid: Option<nat>,
) -> Map<(nat, nat), Option<nat>> {
    Map::new(page_addrs::<A>(dom, a, vp), |k: (nat, nat)| oid)
}

/// The certificates a page gains from `obj`.
pub open spec fn mapped_view<A: ArchPagingMeta>(
    dom: Set<(nat, nat)>,
    a: nat,
    vp: nat,
    obj: nat,
) -> Map<(nat, nat), Option<nat>> {
    Map::new(page_addrs::<A>(dom, a, vp), |k: (nat, nat)| Some(oid_of::<A>(obj, k.1)))
}

/// The pages one address space governs.
pub open spec fn space_pages(dom: Set<(nat, nat)>, a: nat) -> Set<nat> {
    dom.filter(|k: (nat, nat)| k.0 == a).map_by(|k: (nat, nat)| k.1, |vp: nat| (a, vp))
}

/// The keys one address space contributes over a set of pages or addresses.
pub open spec fn space_keys(a: nat, ks: Set<nat>) -> Set<(nat, nat)> {
    ks.map_by(|vp: nat| (a, vp), |k: (nat, nat)| k.1)
}

pub broadcast proof fn lemma_space_keys(a: nat, ks: Set<nat>, k: (nat, nat))
    ensures
        #[trigger] space_keys(a, ks).contains(k) <==> k.0 == a && ks.contains(k.1),
{
    broadcast use Set::lemma_map_by_contains;

}

pub broadcast proof fn lemma_space_pages(dom: Set<(nat, nat)>, a: nat, vp: nat)
    ensures
        #[trigger] space_pages(dom, a).contains(vp) <==> dom.contains((a, vp)),
{
    broadcast use Set::lemma_map_by_contains;

}

/// The frame a leaf entry for `vp` must name: the frame holding the object the page maps.
pub open spec fn walk_target(
    vmap: Map<(nat, nat), Option<nat>>,
    obj_to_frame: Map<nat, Option<nat>>,
    a: nat,
    vp: nat,
) -> Option<nat> {
    match vmap[(a, vp)] {
        Option::None => Option::None,
        Option::Some(o) => obj_to_frame[o],
    }
}

} // verus!

tokenized_state_machine!(Mem<A: ArchPagingMeta> {
    fields {
        /// Object id -> its word, writable. The single copy, and what a write consumes.
        #[sharding(map)]
        pub data: Map<nat, usize>,

        /// Content that has given up the right to be written for the right to be shared.
        #[sharding(persistent_map)]
        pub frozen: Map<nat, usize>,

        /// Object -> the frame holding it. Physical, and invisible to permissions.
        #[sharding(map)]
        pub obj_to_frame: Map<nat, Option<nat>>,

        /// Frame -> the objects placed there. What makes "this frame holds nothing but my
        /// content" ownable, and hence what a write can demand.
        #[sharding(map)]
        pub frame_to_objs: Map<nat, Set<nat>>,

        #[sharding(variable)]
        pub next_oid: nat,

        /// Source of address space ids. Spawning takes the next one rather than being handed
        /// one, so uniqueness is the machine's to guarantee, not the caller's to promise.
        #[sharding(variable)]
        pub next_asid: nat,

        /// The word ids that page table entries occupy. A write to anything else cannot move a
        /// translation, which is what lets an ordinary write proceed without a path proof.
        #[sharding(variable)]
        pub pt_words: Set<nat>,

        /// (address space, page) -> the entry its walk reads at the leaf level, if it gets
        /// there. Kept as state rather than derived because a transition cannot read the page
        /// tables: this is what lets a remap see *every* address space that reads the entry it
        /// writes. Spaces sharing a sub table share these ids, so a kernel range reached from
        /// every root is remapped for every thread at once, while a range reached from one root
        /// is remapped for that thread alone.
        #[sharding(variable)]
        pub leaf_id: Map<(nat, nat), Option<nat>>,

        /// (address space, page) -> the object it maps. A ghost refinement of the entries in
        /// memory. Keyed on the address space because a page means nothing on its own: two
        /// threads running different roots read different entries for the same page.
        #[sharding(map)]
        pub vmap: Map<(nat, nat), Option<nat>>,

        /// (address space, virtual address) -> the object id it reaches. This is the half of a
        /// permission that is *not* portable between threads; the `data` token it is paired
        /// with names an object and travels freely.
        #[sharding(map)]
        pub vmem: Map<(nat, nat), Option<nat>>,

        #[sharding(variable)]
        pub vmem_dom: Set<(nat, nat)>,

        #[sharding(variable)]
        pub vmap_dom: Set<(nat, nat)>,

        #[sharding(constant)]
        pub frames_dom: Set<nat>,

        /// The frames handed out. A frame outside this set is free: it has no `frame_to_objs`
        /// token at all, so nothing can be placed in it until it is allocated.
        #[sharding(variable)]
        pub allocated: Set<nat>,

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
        pub cr3: Map<nat, nat>,

        #[sharding(constant)]
        pub levels: nat,

        #[sharding(constant)]
        pub marker: PhantomData<A>,
    }

    #[invariant]
    pub spec fn geometry(&self) -> bool {
        &&& PTPage::<A>::count() > 0
        &&& self.levels > 0
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
            ==> self.vmap_dom.contains((k.0, vpage::<A>(k.1)))
    }

    /// Every page is describable by `levels` entry indices, so distinct pages differ somewhere a
    /// walk looks.
    #[invariant]
    pub spec fn pages_bounded(&self) -> bool {
        forall|k: (nat, nat)| #[trigger] self.vmap_dom.contains(k)
            ==> self.asids.contains(k.0) && k.1 < pow(PTPage::<A>::count() as int, self.levels)
    }

    /// Every frame can be named by an entry, so encoding one and decoding it back gives it again.
    #[invariant]
    pub spec fn frames_encodable(&self) -> bool {
        forall|f: nat| #[trigger] self.frames_dom.contains(f)
            ==> f <= usize::MAX && encodable::<A>(f as usize)
    }

    #[invariant]
    pub spec fn certificates_backed(&self) -> bool {
        forall|k: (nat, nat)| #[trigger] self.vmem_dom.contains(k) && self.vmem[k] is Some ==> {
            &&& self.vmap[(k.0, vpage::<A>(k.1))] is Some
            &&& self.vmem[k]->Some_0 == oid_of::<A>(self.vmap[(k.0, vpage::<A>(k.1))]->Some_0, k.1)
        }
    }

    #[invariant]
    pub spec fn ids_fresh(&self) -> bool {
        &&& forall|c: nat| #[trigger] self.data.dom().contains(c) ==> c < self.next_oid
        &&& forall|c: nat| #[trigger] self.frozen.dom().contains(c) ==> c < self.next_oid
        &&& forall|b: nat| #[trigger] self.obj_to_frame.dom().contains(b)
            ==> b + PTPage::<A>::count() <= self.next_oid
        &&& forall|k: (nat, nat)| #[trigger] self.vmap_dom.contains(k) && self.vmap[k] is Some
            ==> self.vmap[k]->Some_0 + PTPage::<A>::count() <= self.next_oid
        &&& forall|c: nat| #[trigger] self.pt_words.contains(c) ==> c < self.next_oid
    }

    #[invariant]
    pub spec fn content_total(&self) -> bool {
        &&& forall|c: nat| #[trigger] self.data.dom().contains(c) ==> !self.frozen.dom().contains(c)
        &&& forall|b: nat| #[trigger] self.obj_to_frame.dom().contains(b)
            ==> obj_ids::<A>(b).subset_of(self.data.dom().union(self.frozen.dom()))
    }

    #[invariant]
    pub spec fn objects_disjoint(&self) -> bool {
        forall|b1: nat, b2: nat, c: nat|
            self.obj_to_frame.dom().contains(b1) && #[trigger] self.obj_to_frame.dom().contains(b2)
                && #[trigger] obj_ids::<A>(b1).contains(c) && obj_ids::<A>(b2).contains(c)
                ==> b1 == b2
    }

    #[invariant]
    pub spec fn residency_sound(&self) -> bool {
        forall|pfn: nat, b: nat|
            self.allocated.contains(pfn) && #[trigger] self.frame_to_objs[pfn].contains(b) ==> {
                &&& self.obj_to_frame.dom().contains(b)
                &&& self.obj_to_frame[b] == Some(pfn)
            }
    }

    #[invariant]
    pub spec fn residency_complete(&self) -> bool {
        forall|b: nat| #[trigger] self.obj_to_frame.dom().contains(b) && self.obj_to_frame[b] is Some
            ==> {
            &&& self.allocated.contains(self.obj_to_frame[b]->Some_0)
            &&& self.frame_to_objs[self.obj_to_frame[b]->Some_0].contains(b)
        }
    }

    /// A frame holds one set of words, so objects sharing a frame must agree.
    #[invariant]
    pub spec fn coplaced_agree(&self) -> bool {
        forall|b1: nat, b2: nat, off: nat|
            self.obj_to_frame.dom().contains(b1) && #[trigger] self.obj_to_frame.dom().contains(b2)
                && self.obj_to_frame[b1] is Some && self.obj_to_frame[b1] == self.obj_to_frame[b2]
                && off < PTPage::<A>::count()
                ==> #[trigger] word_at(self.data, self.frozen, (b1 + off) as nat)
                    == word_at(self.data, self.frozen, (b2 + off) as nat)
    }

    /// The level a walk starts at.
    pub open spec fn top(&self) -> nat {
        (self.levels - 1) as nat
    }

    /// The recorded leaf entry is the one the walk really reads.
    #[invariant]
    pub spec fn leaf_ids_agree(&self) -> bool {
        &&& self.leaf_id.dom() =~= self.vmap_dom
        &&& forall|k: (nat, nat)| #[trigger] self.vmap_dom.contains(k) ==> self.leaf_id[k]
            == path_id_at::<A>(
            self.data,
            self.frozen,
            self.frame_to_objs,
            self.cr3[k.0],
            self.top(),
            0,
            k.1,
        )
    }

    #[invariant]
    pub spec fn cpus_run_spaces(&self) -> bool {
        forall|c: nat| #[trigger] self.cpus.dom().contains(c) ==> self.asids.contains(self.cpus[c])
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
            &&& exists|o: nat| self.frame_to_objs[self.cr3[a]] =~= Set::<nat>::empty().insert(o)
        }
    }

    /// A frame a walk lands on holds exactly one object. That is what turns the frame back into
    /// an object whose words can be read; frames holding data may be shared freely.
    #[invariant]
    pub spec fn path_frames_solo(&self) -> bool {
        forall|k: (nat, nat), l: nat|
            self.vmap_dom.contains(k) && l <= self.top() && #[trigger] frame_at::<A>(
                self.data,
                self.frozen,
                self.frame_to_objs,
                self.cr3[k.0],
                self.top(),
                l,
                k.1,
            ) is Some ==> {
                let f = frame_at::<A>(
                    self.data,
                    self.frozen,
                    self.frame_to_objs,
                    self.cr3[k.0],
                    self.top(),
                    l,
                    k.1,
                )->Some_0;
                &&& self.allocated.contains(f)
                &&& exists|o: nat| self.frame_to_objs[f] =~= Set::<nat>::empty().insert(o)
            }
    }

    /// Every entry a walk reads is a table word.
    #[invariant]
    pub spec fn paths_in_tables(&self) -> bool {
        forall|k: (nat, nat), c: nat|
            self.vmap_dom.contains(k) && #[trigger] on_path::<A>(
                self.data,
                self.frozen,
                self.frame_to_objs,
                self.cr3[k.0],
                self.top(),
                k.1,
                c,
            ) ==> self.pt_words.contains(c)
    }

    /// What the hardware finds is what `vmap` says. Stated on the whole walk rather than one
    /// entry at a time: a page a table is reached at is not a property of the table -- a
    /// self-mapped page is reached at every level -- so there is no per-table level to key on.
    #[invariant]
    pub spec fn walk_agrees(&self) -> bool {
        forall|k: (nat, nat)| #[trigger] self.vmap_dom.contains(k) ==> translate::<A>(
            self.data,
            self.frozen,
            self.frame_to_objs,
            self.cr3[k.0],
            self.top(),
            k.1,
        ) == walk_target(self.vmap, self.obj_to_frame, k.0, k.1)
    }

    /// Boot brings up one CPU running one kernel thread, so there is a single address space on
    /// an all-absent root. It governs the whole available address range, and further threads
    /// join later through [`spawn`](Self::spawn).
    init!{
        boot(
            frames: Set<nat>,
            vpages: Set<nat>,
            vaddrs: Set<nat>,
            boot_asid: nat,
            root: nat,
            levels: nat,
        ) {
            require levels > 0;
            require PTPage::<A>::count() > 0;
            require frames.contains(root);
            require forall|f: nat| #[trigger] frames.contains(f)
                ==> f <= usize::MAX && encodable::<A>(f as usize);
            require forall|v: nat| #[trigger] vaddrs.contains(v) ==> vpages.contains(vpage::<A>(v));
            require forall|vp: nat| #[trigger] vpages.contains(vp)
                ==> vp < pow(PTPage::<A>::count() as int, levels);
            init data = Map::new(obj_ids::<A>(0), |c: nat| absent_word());
            init frozen = Map::empty();
            init obj_to_frame = Map::empty().insert(0, Some(root));
            init frame_to_objs = Map::<nat, Set<nat>>::empty().insert(
                root,
                Set::<nat>::empty().insert(0),
            );
            init allocated = Set::<nat>::empty().insert(root);
            init frames_dom = frames;
            init asids = Set::<nat>::empty().insert(boot_asid);
            init cpus = Map::<nat, nat>::empty().insert(0, boot_asid);
            init next_asid = boot_asid + 1;
            init cr3 = Map::<nat, nat>::empty().insert(boot_asid, root);
            init levels = levels;
            init next_oid = PTPage::<A>::count();
            init pt_words = obj_ids::<A>(0);
            init vmap = Map::new(space_keys(boot_asid, vpages), |k: (nat, nat)| Option::<nat>::None);
            init vmap_dom = space_keys(boot_asid, vpages);
            init leaf_id = Map::new(
                space_keys(boot_asid, vpages),
                |k: (nat, nat)| if levels == 1 {
                    Some(entry_id::<A>(0, k.1, 0))
                } else {
                    Option::<nat>::None
                },
            );
            init vmem = Map::new(space_keys(boot_asid, vaddrs), |k: (nat, nat)| Option::<nat>::None);
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
        alloc_frame(f: nat) {
            require pre.frames_dom.contains(f);
            require !pre.allocated.contains(f);
            update allocated = pre.allocated.insert(f);
            add frame_to_objs += [f => Set::<nat>::empty()];
        }
    }

    /// Recycle a frame. Giving up the token is what makes it free again, and it may only be
    /// given up once nothing is placed there.
    transition!{
        dealloc_frame(f: nat) {
            remove frame_to_objs -= [f => let occ];
            require occ =~= Set::<nat>::empty();
            update allocated = pre.allocated.remove(f);
        }
    }

    /// Start another address space from an existing one. It runs its *own* root, a fresh frame
    /// whose entries copy the source root's, so it starts out mapping the same pages but may be
    /// remapped without disturbing the space it came from. The root frame comes from
    /// [`alloc_frame`](Self::alloc_frame); `view` and `words` are how the caller shows what the
    /// source space maps and holds without the transition reading a sharded field.
    transition!{
        spawn(
            src: nat,
            nroot: nat,
            view: Map<(nat, nat), Option<nat>>,
            words: Map<nat, usize>,
        ) {
            let a = pre.next_asid;
            let nobj = pre.next_oid;
            require pre.asids.contains(src);
            update next_asid = pre.next_asid + 1;
            update next_oid = pre.next_oid + PTPage::<A>::count();

            remove frame_to_objs -= [nroot => let occ];
            require occ =~= Set::<nat>::empty();
            have frame_to_objs >= [pre.cr3[src] => let roots];
            let robj = roots.choose();
            have data >= (words);
            require words.dom() =~= obj_ids::<A>(robj);
            add frame_to_objs += [nroot => Set::<nat>::empty().insert(nobj)];
            add obj_to_frame += [nobj => Some(nroot)];
            add data += (Map::new(
                obj_ids::<A>(nobj),
                |c: nat| words[(c - nobj + robj) as nat],
            ));
            update pt_words = pre.pt_words.union(obj_ids::<A>(nobj));

            require view.dom() =~= space_keys(src, space_pages(pre.vmap_dom, src));
            have vmap >= (view);
            update asids = pre.asids.insert(a);
            update cr3 = pre.cr3.insert(a, nroot);
            update vmap_dom = pre.vmap_dom.union(
                space_keys(a, space_pages(pre.vmap_dom, src)),
            );
            update leaf_id = Map::new(
                pre.vmap_dom.union(space_keys(a, space_pages(pre.vmap_dom, src))),
                |k: (nat, nat)| if k.0 != a {
                    pre.leaf_id[k]
                } else if pre.levels == 1 {
                    // The copied root is itself the leaf table, so its entries are new ids.
                    Some(entry_id::<A>(nobj, k.1, 0))
                } else {
                    pre.leaf_id[(src, k.1)]
                },
            );
            add vmap += (Map::new(
                space_keys(a, space_pages(pre.vmap_dom, src)),
                |k: (nat, nat)| view[(src, k.1)],
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
            require occupants =~= Set::<nat>::empty().insert(obj);
            require !pre.pt_words.contains(oid->Some_0);
            remove data -= [oid->Some_0 => let old];
            add data += [oid->Some_0 => val];
        }
    }

    /// Give up the right to write for the right to share.
    transition!{
        freeze(oid: nat) {
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
    fn alloc_frame_inductive(pre: Self, post: Self, f: nat) {
        lemma_frames_local::<A>(pre, post, pre.allocated);
    }

    /// A frame with nothing placed in it is a frame no walk landed on, since a walk lands only
    /// where a single object resides.
    #[inductive(dealloc_frame)]
    fn dealloc_frame_inductive(pre: Self, post: Self, f: nat) {
        assert forall|g: nat|
            #[trigger] pre.allocated.contains(g) && (exists|o: nat|
                pre.frame_to_objs[g] =~= Set::<nat>::empty().insert(o))
                implies pre.allocated.remove(f).contains(g) by {
            let o = choose|o: nat| pre.frame_to_objs[g] =~= Set::<nat>::empty().insert(o);
            assert(pre.frame_to_objs[g].contains(o));
        }
        assert forall|a: nat| #[trigger] pre.asids.contains(a) implies pre.cr3[a] != f by {
            let o = choose|o: nat|
                pre.frame_to_objs[pre.cr3[a]] =~= Set::<nat>::empty().insert(o);
            assert(pre.frame_to_objs[pre.cr3[a]].contains(o));
        }
        lemma_frames_local::<A>(pre, post, pre.allocated.remove(f));
    }

    /// A new address space walks its copied root exactly as the source walked its own, so it
    /// starts out mapping what the source maps; and the walks already in flight see neither the
    /// fresh words nor the fresh frame.
    #[inductive(spawn)]
    fn spawn_inductive(
        pre: Self,
        post: Self,
        src: nat,
        nroot: nat,
        view: Map<(nat, nat), Option<nat>>,
        words: Map<nat, usize>,
    ) {
        broadcast use lemma_space_keys, lemma_space_pages;

        let a = pre.next_asid;
        let nobj = pre.next_oid;
        let robj = pre.frame_to_objs[pre.cr3[src]].choose();
        let top = pre.top();

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
        assert forall|g: nat|
            #[trigger] pre.allocated.contains(g) && (exists|o: nat|
                pre.frame_to_objs[g] =~= Set::<nat>::empty().insert(o))
                implies pre.allocated.remove(nroot).contains(g) by {
            let o = choose|o: nat| pre.frame_to_objs[g] =~= Set::<nat>::empty().insert(o);
            assert(pre.frame_to_objs[g].contains(o));
        }
        lemma_frames_local::<A>(mid1, mid2, pre.allocated.remove(nroot));

        assert(resident(post.frame_to_objs, nroot) == nobj) by {
            assert(post.frame_to_objs[nroot].contains(nobj));
            assert(post.frame_to_objs[nroot].contains(post.frame_to_objs[nroot].choose()));
        }
        assert(resident(post.frame_to_objs, pre.cr3[src]) == robj);
        assert forall|i: nat| i < PTPage::<A>::count() implies #[trigger] word_at(
            post.data,
            post.frozen,
            (nobj + i) as nat,
        ) == word_at(post.data, post.frozen, (robj + i) as nat) by {
            assert(obj_ids::<A>(nobj).contains((nobj + i) as nat));
            assert(obj_ids::<A>(nobj).contains((nobj + i) as nat));
            assert(obj_ids::<A>(robj).contains((robj + i) as nat));
        }

        assert forall|k: (nat, nat), l: nat| post.vmap_dom.contains(k) && l <= top implies
            #[trigger] frame_at::<A>(
            post.data,
            post.frozen,
            post.frame_to_objs,
            post.cr3[k.0],
            top,
            l,
            k.1,
        ) == frame_at::<A>(
            pre.data,
            pre.frozen,
            pre.frame_to_objs,
            pre.cr3[if k.0 == a { src } else { k.0 }],
            top,
            l,
            k.1,
        ) || (k.0 == a && l == top) by {
            if k.0 == a {
                assert(pre.vmap_dom.contains((src, k.1)));
                if l < top {
                    lemma_frame_at_root_copy::<A>(
                        post.data,
                        post.frozen,
                        post.frame_to_objs,
                        nroot,
                        pre.cr3[src],
                        top,
                        l,
                        k.1,
                    );
                }
            }
        }

        assert forall|k: (nat, nat)| #[trigger] post.vmap_dom.contains(k) implies translate::<A>(
            post.data,
            post.frozen,
            post.frame_to_objs,
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
                    assert(view.dom().contains((src, k.1)));
                    assert(view.submap_of(pre.vmap));
                }
            }
            if k.0 == a {
                lemma_translate_root_copy::<A>(
                    post.data,
                    post.frozen,
                    post.frame_to_objs,
                    nroot,
                    pre.cr3[src],
                    top,
                    k.1,
                );
            }
        }

        assert forall|k: (nat, nat), c: nat|
            post.vmap_dom.contains(k) && #[trigger] on_path::<A>(
                post.data,
                post.frozen,
                post.frame_to_objs,
                post.cr3[k.0],
                top,
                k.1,
                c,
            ) implies post.pt_words.contains(c) by {
            let l = choose|l: nat|
                l <= top && #[trigger] path_id_at::<A>(
                    post.data,
                    post.frozen,
                    post.frame_to_objs,
                    post.cr3[k.0],
                    top,
                    l,
                    k.1,
                ) == Some(c);
            if k.0 == a && l == top {
                lemma_vindex_bounded::<A>(k.1, l);
            } else {
                let s = if k.0 == a {
                    src
                } else {
                    k.0
                };
                assert(pre.vmap_dom.contains((s, k.1)));
                let f = frame_at::<A>(
                    pre.data,
                    pre.frozen,
                    pre.frame_to_objs,
                    pre.cr3[s],
                    top,
                    l,
                    k.1,
                )->Some_0;
                assert(pre.allocated.contains(f));
                assert(f != nroot) by {
                    let o = choose|o: nat|
                        pre.frame_to_objs[f] =~= Set::<nat>::empty().insert(o);
                    assert(pre.frame_to_objs[f].contains(o));
                }
                assert(path_id_at::<A>(
                    pre.data,
                    pre.frozen,
                    pre.frame_to_objs,
                    pre.cr3[s],
                    top,
                    l,
                    k.1,
                ) == Some(c));
                assert(on_path::<A>(
                    pre.data,
                    pre.frozen,
                    pre.frame_to_objs,
                    pre.cr3[s],
                    top,
                    k.1,
                    c,
                ));
            }
        }

        assert(post.leaf_id.dom() =~= post.vmap_dom);
        assert forall|k: (nat, nat)| #[trigger] post.vmap_dom.contains(k) implies post.leaf_id[k]
            == path_id_at::<A>(
            post.data,
            post.frozen,
            post.frame_to_objs,
            post.cr3[k.0],
            top,
            0,
            k.1,
        ) by {
            let s = if k.0 == a {
                src
            } else {
                k.0
            };
            assert(pre.vmap_dom.contains((s, k.1)));
            if k.0 == a && top == 0 {
                assert(frame_at::<A>(
                    post.data,
                    post.frozen,
                    post.frame_to_objs,
                    nroot,
                    top,
                    0,
                    k.1,
                ) == Some(nroot));
            } else {
                let f = frame_at::<A>(
                    pre.data,
                    pre.frozen,
                    pre.frame_to_objs,
                    pre.cr3[s],
                    top,
                    0,
                    k.1,
                );
                if f is Some {
                    assert(pre.allocated.contains(f->Some_0));
                    assert(f->Some_0 != nroot) by {
                        let o = choose|o: nat|
                            pre.frame_to_objs[f->Some_0] =~= Set::<nat>::empty().insert(o);
                        assert(pre.frame_to_objs[f->Some_0].contains(o));
                    }
                }
            }
        }
        assert forall|c: nat| #[trigger] post.pt_words.contains(c) implies c < post.next_oid
            by {}
        assert forall|b1: nat, b2: nat, off: nat|
            post.obj_to_frame.dom().contains(b1) && #[trigger] post.obj_to_frame.dom().contains(b2)
                && post.obj_to_frame[b1] is Some && post.obj_to_frame[b1]
                == post.obj_to_frame[b2] && off < PTPage::<A>::count() implies #[trigger] word_at(
            post.data,
            post.frozen,
            (b1 + off) as nat,
        ) == word_at(post.data, post.frozen, (b2 + off) as nat) by {
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
                assert(b1 + PTPage::<A>::count() <= nobj);
                assert(b2 + PTPage::<A>::count() <= nobj);
                assert(!obj_ids::<A>(nobj).contains((b1 + off) as nat));
                assert(!obj_ids::<A>(nobj).contains((b2 + off) as nat));
                assert(word_at(pre.data, pre.frozen, (b1 + off) as nat) == word_at(
                    pre.data,
                    pre.frozen,
                    (b2 + off) as nat,
                ));
            }
        }
        assert forall|k: (nat, nat)|
            #[trigger] post.vmap_dom.contains(k) && post.vmap[k] is Some implies post.vmap[k]->Some_0
                + PTPage::<A>::count() <= post.next_oid by {
            let s = if k.0 == a {
                src
            } else {
                k.0
            };
            assert(pre.vmap_dom.contains((s, k.1)));
            if k.0 == a {
                assert(view.dom().contains((src, k.1)));
                assert(view.submap_of(pre.vmap));
            }
        }
        assert forall|k: (nat, nat), l: nat|
            post.vmap_dom.contains(k) && l <= top && #[trigger] frame_at::<A>(
                post.data,
                post.frozen,
                post.frame_to_objs,
                post.cr3[k.0],
                top,
                l,
                k.1,
            ) is Some implies {
                let f = frame_at::<A>(
                    post.data,
                    post.frozen,
                    post.frame_to_objs,
                    post.cr3[k.0],
                    top,
                    l,
                    k.1,
                )->Some_0;
                &&& post.allocated.contains(f)
                &&& exists|o: nat| post.frame_to_objs[f] =~= Set::<nat>::empty().insert(o)
            } by {
            let s = if k.0 == a {
                src
            } else {
                k.0
            };
            assert(pre.vmap_dom.contains((s, k.1)));
            if k.0 == a && l == top {
                assert(post.frame_to_objs[nroot] =~= Set::<nat>::empty().insert(nobj));
            }
        }
    }

    /// Every translation is unmoved by a write that touches no table word, which is exactly
    /// what [`lemma_translate_local`] gives.
    #[inductive(write_non_pt)]
    fn write_non_pt_inductive(pre: Self, post: Self, cpu: nat, v: nat, val: usize) {
        let a = pre.cpus[cpu];
        let oid = pre.vmem[(a, v)]->Some_0;
        assert forall|c: nat| c != oid implies word_at(pre.data, pre.frozen, c) == word_at(
            post.data,
            post.frozen,
            c,
        ) by {}
        assert(!pre.pt_words.contains(oid));
        lemma_words_local::<A>(pre, post, Set::<nat>::empty().insert(oid));
        assert forall|b1: nat, b2: nat, off: nat|
            pre.obj_to_frame.dom().contains(b1) && #[trigger] pre.obj_to_frame.dom().contains(b2)
                && pre.obj_to_frame[b1] is Some && pre.obj_to_frame[b1] == pre.obj_to_frame[b2]
                && off < PTPage::<A>::count() implies #[trigger] word_at(
            post.data,
            post.frozen,
            (b1 + off) as nat,
        ) == word_at(post.data, post.frozen, (b2 + off) as nat) by {
            let obj = obj_of::<A>(oid, v);
            let p = pre.obj_to_frame[obj]->Some_0;
            if (b1 + off) as nat == oid || (b2 + off) as nat == oid {
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
    /// a walk reads is disturbed.
    #[inductive(freeze)]
    fn freeze_inductive(pre: Self, post: Self, oid: nat) {
        assert forall|c: nat| word_at(pre.data, pre.frozen, c) == word_at(post.data, post.frozen, c)
            by {}
        lemma_words_local::<A>(pre, post, Set::<nat>::empty());
    }

    #[inductive(boot)]
    fn boot_inductive(
        post: Self,
        frames: Set<nat>,
        vpages: Set<nat>,
        vaddrs: Set<nat>,
        boot_asid: nat,
        root: nat,
        levels: nat,
    ) {
        broadcast use vstd::set_lib::group_set_lib_default;

        assert(post.cr3.dom() =~= post.asids);
        assert(post.vmap.dom() =~= post.vmap_dom);
        assert(post.vmem.dom() =~= post.vmem_dom);
        assert(post.frame_to_objs[root] =~= Set::<nat>::empty().insert(0));
        assert(resident(post.frame_to_objs, root) == 0) by {
            assert(post.frame_to_objs[root].contains(0));
            assert(post.frame_to_objs[root].contains(post.frame_to_objs[root].choose()));
        }
        lemma_absent_word::<A>();
        assert forall|vp: nat, l: nat| l <= post.top() implies #[trigger] frame_at::<A>(
            post.data,
            post.frozen,
            post.frame_to_objs,
            root,
            post.top(),
            l,
            vp,
        ) == if l == post.top() {
            Some(root)
        } else {
            Option::None
        } by {
            lemma_boot_frame_at::<A>(
                post.data,
                post.frozen,
                post.frame_to_objs,
                root,
                post.top(),
                l,
                vp,
            );
        }
        assert forall|k: (nat, nat)| #[trigger] post.vmap_dom.contains(k) implies translate::<A>(
            post.data,
            post.frozen,
            post.frame_to_objs,
            post.cr3[k.0],
            post.top(),
            k.1,
        ) == walk_target(post.vmap, post.obj_to_frame, k.0, k.1) by {
            lemma_vindex_bounded::<A>(k.1, 0);
            assert(obj_ids::<A>(0).contains(path_id::<A>(post.frame_to_objs, root, k.1, 0)));
        }
        assert forall|k: (nat, nat), l: nat|
            post.vmap_dom.contains(k) && l <= post.top() && #[trigger] frame_at::<A>(
                post.data,
                post.frozen,
                post.frame_to_objs,
                post.cr3[k.0],
                post.top(),
                l,
                k.1,
            ) is Some implies {
                let f = frame_at::<A>(
                    post.data,
                    post.frozen,
                    post.frame_to_objs,
                    post.cr3[k.0],
                    post.top(),
                    l,
                    k.1,
                )->Some_0;
                &&& post.frames_dom.contains(f)
                &&& exists|o: nat| post.frame_to_objs[f] =~= Set::<nat>::empty().insert(o)
            } by {
            assert(post.frame_to_objs[root] =~= Set::<nat>::empty().insert(0));
        }
        assert forall|k: (nat, nat), c: nat|
            post.vmap_dom.contains(k) && #[trigger] on_path::<A>(
                post.data,
                post.frozen,
                post.frame_to_objs,
                post.cr3[k.0],
                post.top(),
                k.1,
                c,
            ) implies post.pt_words.contains(c) by {
            let l = choose|l: nat|
                l <= post.top() && #[trigger] path_id_at::<A>(
                    post.data,
                    post.frozen,
                    post.frame_to_objs,
                    post.cr3[k.0],
                    post.top(),
                    l,
                    k.1,
                ) == Some(c);
            assert(l == post.top());
            lemma_vindex_bounded::<A>(k.1, l);
        }
    }
});

verus! {

/// A tree whose entries are all absent stops the walk at the root.
pub proof fn lemma_boot_frame_at<A: ArchPagingMeta>(
    data: Map<nat, usize>,
    frozen: Map<nat, usize>,
    frame_to_objs: Map<nat, Set<nat>>,
    cr3: nat,
    top: nat,
    level: nat,
    vp: nat,
)
    requires
        level <= top,
        resident(frame_to_objs, cr3) == 0,
        PTPage::<A>::count() > 0,
        forall|c: nat| #[trigger] obj_ids::<A>(0).contains(c) ==> word_at(data, frozen, c)
            == absent_word(),
    ensures
        frame_at::<A>(data, frozen, frame_to_objs, cr3, top, level, vp) == if level == top {
            Some(cr3)
        } else {
            Option::<nat>::None
        },
    decreases top - level,
{
    lemma_absent_word::<A>();
    if level < top {
        let up = (level + 1) as nat;
        lemma_boot_frame_at::<A>(data, frozen, frame_to_objs, cr3, top, up, vp);
        if up == top {
            lemma_vindex_bounded::<A>(vp, up);
            assert(obj_ids::<A>(0).contains(path_id::<A>(frame_to_objs, cr3, vp, up)));
        }
    }
}


/// The words a walk of `vp` reads are untouched by a step that changes only `oid`, a word no
/// table holds.
pub proof fn lemma_path_words<A: ArchPagingMeta>(
    pre: Mem::State<A>,
    post: Mem::State<A>,
    touched: Set<nat>,
    k: (nat, nat),
)
    requires
        pre.paths_in_tables(),
        pre.vmap_dom.contains(k),
        forall|c: nat| #[trigger] touched.contains(c) ==> !pre.pt_words.contains(c),
        forall|c: nat| !touched.contains(c) ==> word_at(pre.data, pre.frozen, c) == word_at(
            post.data,
            post.frozen,
            c,
        ),
    ensures
        forall|c: nat| #[trigger]
            on_path::<A>(pre.data, pre.frozen, pre.frame_to_objs, pre.cr3[k.0], pre.top(), k.1, c)
                ==> word_at(pre.data, pre.frozen, c) == word_at(post.data, post.frozen, c),
{
    assert forall|c: nat| #[trigger]
        on_path::<A>(
            pre.data,
            pre.frozen,
            pre.frame_to_objs,
            pre.cr3[k.0],
            pre.top(),
            k.1,
            c,
        ) implies word_at(pre.data, pre.frozen, c) == word_at(post.data, post.frozen, c) by {
        if touched.contains(c) {
            assert(!pre.pt_words.contains(c));
        }
    }
}

/// A step that only changes where frames outside `live` stand leaves every walk alone. Walks
/// stay within `live` because they land only on allocated frames with a single resident, which
/// is what [`path_frames_solo`](Mem::State::path_frames_solo) says.
pub proof fn lemma_frames_local<A: ArchPagingMeta>(
    pre: Mem::State<A>,
    post: Mem::State<A>,
    live: Set<nat>,
)
    requires
        pre.paths_in_tables(),
        pre.walk_agrees(),
        pre.path_frames_solo(),
        forall|f: nat| #[trigger] live.contains(f) ==> pre.frame_to_objs[f] == post.frame_to_objs[f],
        forall|f: nat|
            #[trigger] pre.allocated.contains(f) && (exists|o: nat|
                pre.frame_to_objs[f] =~= Set::<nat>::empty().insert(o)) ==> live.contains(f),
        post.data == pre.data,
        post.frozen == pre.frozen,
        post.cr3 == pre.cr3,
        post.asids == pre.asids,
        post.levels == pre.levels,
        post.vmap == pre.vmap,
        post.vmap_dom == pre.vmap_dom,
        post.obj_to_frame == pre.obj_to_frame,
        post.pt_words == pre.pt_words,
    ensures
        post.walk_agrees(),
        post.paths_in_tables(),
        forall|k: (nat, nat), l: nat| #[trigger]
            frame_at::<A>(
                post.data,
                post.frozen,
                post.frame_to_objs,
                post.cr3[k.0],
                post.top(),
                l,
                k.1,
            ) == frame_at::<A>(
                pre.data,
                pre.frozen,
                pre.frame_to_objs,
                pre.cr3[k.0],
                pre.top(),
                l,
                k.1,
            ) || !pre.vmap_dom.contains(k),
{
    assert forall|k: (nat, nat), l: nat| pre.vmap_dom.contains(k) implies #[trigger] frame_at::<A>(
        post.data,
        post.frozen,
        post.frame_to_objs,
        post.cr3[k.0],
        post.top(),
        l,
        k.1,
    ) == frame_at::<A>(
        pre.data,
        pre.frozen,
        pre.frame_to_objs,
        pre.cr3[k.0],
        pre.top(),
        l,
        k.1,
    ) by {
        lemma_frame_at_frames::<A>(
            pre.data,
            pre.frozen,
            pre.frame_to_objs,
            post.frame_to_objs,
            live,
            pre.cr3[k.0],
            pre.top(),
            l,
            k.1,
        );
    }
    assert forall|k: (nat, nat)| #[trigger] pre.vmap_dom.contains(k) implies translate::<A>(
        post.data,
        post.frozen,
        post.frame_to_objs,
        post.cr3[k.0],
        post.top(),
        k.1,
    ) == translate::<A>(
        pre.data,
        pre.frozen,
        pre.frame_to_objs,
        pre.cr3[k.0],
        pre.top(),
        k.1,
    ) by {
        assert(frame_at::<A>(
            post.data,
            post.frozen,
            post.frame_to_objs,
            post.cr3[k.0],
            post.top(),
            0,
            k.1,
        ) == frame_at::<A>(
            pre.data,
            pre.frozen,
            pre.frame_to_objs,
            pre.cr3[k.0],
            pre.top(),
            0,
            k.1,
        ));
    }
    assert forall|k: (nat, nat), c: nat|
        post.vmap_dom.contains(k) && #[trigger] on_path::<A>(
            post.data,
            post.frozen,
            post.frame_to_objs,
            post.cr3[k.0],
            post.top(),
            k.1,
            c,
        ) implies post.pt_words.contains(c) by {
        let l = choose|l: nat|
            l <= post.top() && #[trigger] path_id_at::<A>(
                post.data,
                post.frozen,
                post.frame_to_objs,
                post.cr3[k.0],
                post.top(),
                l,
                k.1,
            ) == Some(c);
        assert(frame_at::<A>(
            post.data,
            post.frozen,
            post.frame_to_objs,
            post.cr3[k.0],
            post.top(),
            l,
            k.1,
        ) == frame_at::<A>(
            pre.data,
            pre.frozen,
            pre.frame_to_objs,
            pre.cr3[k.0],
            pre.top(),
            l,
            k.1,
        ));
        assert(path_id_at::<A>(
            pre.data,
            pre.frozen,
            pre.frame_to_objs,
            pre.cr3[k.0],
            pre.top(),
            l,
            k.1,
        ) == Some(c));
        assert(on_path::<A>(
            pre.data,
            pre.frozen,
            pre.frame_to_objs,
            pre.cr3[k.0],
            pre.top(),
            k.1,
            c,
        ));
    }
}

/// A step that leaves every table word alone leaves every walk alone: where a page leads, which
/// frames the walk lands on, and which words it reads are all unchanged.
pub proof fn lemma_words_local<A: ArchPagingMeta>(
    pre: Mem::State<A>,
    post: Mem::State<A>,
    touched: Set<nat>,
)
    requires
        pre.paths_in_tables(),
        pre.walk_agrees(),
        pre.path_frames_solo(),
        forall|c: nat| #[trigger] touched.contains(c) ==> !pre.pt_words.contains(c),
        post.frame_to_objs == pre.frame_to_objs,
        post.frames_dom == pre.frames_dom,
        post.cr3 == pre.cr3,
        post.asids == pre.asids,
        post.levels == pre.levels,
        post.vmap == pre.vmap,
        post.vmap_dom == pre.vmap_dom,
        post.obj_to_frame == pre.obj_to_frame,
        pre.pt_words.subset_of(post.pt_words),
        post.allocated == pre.allocated,
        forall|c: nat| !touched.contains(c) ==> word_at(pre.data, pre.frozen, c) == word_at(
            post.data,
            post.frozen,
            c,
        ),
    ensures
        post.walk_agrees(),
        post.path_frames_solo(),
        post.paths_in_tables(),
        forall|k: (nat, nat), l: nat| pre.vmap_dom.contains(k) && l <= pre.top() ==> #[trigger]
            frame_at::<A>(
                post.data,
                post.frozen,
                post.frame_to_objs,
                post.cr3[k.0],
                post.top(),
                l,
                k.1,
            ) == frame_at::<A>(
                pre.data,
                pre.frozen,
                pre.frame_to_objs,
                pre.cr3[k.0],
                pre.top(),
                l,
                k.1,
            ),
{
    assert forall|k: (nat, nat), l: nat| post.vmap_dom.contains(k) && l <= post.top() implies
        #[trigger] frame_at::<A>(
        post.data,
        post.frozen,
        post.frame_to_objs,
        post.cr3[k.0],
        post.top(),
        l,
        k.1,
    ) == frame_at::<A>(
        pre.data,
        pre.frozen,
        pre.frame_to_objs,
        pre.cr3[k.0],
        pre.top(),
        l,
        k.1,
    ) by {
        lemma_path_words::<A>(pre, post, touched, k);
        lemma_frame_at_local::<A>(
            pre.data,
            pre.frozen,
            post.data,
            post.frozen,
            pre.frame_to_objs,
            pre.cr3[k.0],
            pre.top(),
            l,
            k.1,
        );
    }
    assert forall|k: (nat, nat)| #[trigger] post.vmap_dom.contains(k) implies translate::<A>(
        post.data,
        post.frozen,
        post.frame_to_objs,
        post.cr3[k.0],
        post.top(),
        k.1,
    ) == walk_target(post.vmap, post.obj_to_frame, k.0, k.1) by {
        lemma_path_words::<A>(pre, post, touched, k);
        lemma_translate_local::<A>(
            pre.data,
            pre.frozen,
            post.data,
            post.frozen,
            pre.frame_to_objs,
            pre.cr3[k.0],
            pre.top(),
            k.1,
        );
    }
    assert forall|k: (nat, nat), c: nat|
        post.vmap_dom.contains(k) && #[trigger] on_path::<A>(
            post.data,
            post.frozen,
            post.frame_to_objs,
            post.cr3[k.0],
            post.top(),
            k.1,
            c,
        ) implies post.pt_words.contains(c) by {
        let l = choose|l: nat|
            l <= post.top() && #[trigger] path_id_at::<A>(
                post.data,
                post.frozen,
                post.frame_to_objs,
                post.cr3[k.0],
                post.top(),
                l,
                k.1,
            ) == Some(c);
        assert(path_id_at::<A>(
            pre.data,
            pre.frozen,
            pre.frame_to_objs,
            pre.cr3[k.0],
            pre.top(),
            l,
            k.1,
        ) == Some(c));
        assert(on_path::<A>(
            pre.data,
            pre.frozen,
            pre.frame_to_objs,
            pre.cr3[k.0],
            pre.top(),
            k.1,
            c,
        ));
    }
}

} // verus!

