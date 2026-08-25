//! A model of content, physical frames, page tables, and virtual aliases, as a tokenized state
//! machine.
//!
//! The pivot is that a permission never names a physical address. Between virtual and physical
//! sits an **object**: an abstract identity for a word, independent of where that word is
//! stored. A page table entry maps a page to
//! *content*, and where that content physically sits is a separate, freely changeable fact. So
//! a certificate mentions no frame at all, and every physical relocation -- page swap and
//! copy-on-write alike -- leaves every outstanding permission untouched.
//!
//! An object is minted per *mapping*, not per frame. Two pages sharing a frame after a fork
//! therefore have different object ids from the moment of the fork, because their contents are
//! destined to diverge. Had they shared an id, the copy-on-write would have to mint a new id for
//! the child and so invalidate everything the child holds -- at exactly the moment when nothing
//! in the child's address space observably changed.
//!
//! Tokens, each saying one thing:
//!
//! - `data` -- object id -> its word. The single writable copy, and the only thing a write
//!   consumes, so holding it is what makes a write exclusive however the word is addressed.
//! - `frozen` -- content that has given up the right to be written in exchange for the right to
//!   be shared. Duplicable, so any number of readers may hold one.
//! - `obj_to_frame` -- object -> the frame currently holding it. Physical, and invisible to
//!   permissions.
//! - `frame_to_objs` -- frame -> the objects placed there, the inverse of `obj_to_frame`.
//!   What makes "this frame holds nothing but my content" ownable, and hence what a write can
//!   demand.
//! - `vmap` -- one page table entry: page -> content.
//! - `vmem` -- virtual address -> the object id it reaches. Handed to whoever holds the
//!   address.
//!
//! Three kinds of virtual permission fall straight out:
//!
//! - **Exclusive** (`VirtPointsTo`): certificate plus a `data` token. What `map`, `fork`, and a
//!   copy-on-write produce. Readable and writable.
//! - **Shared** (`SharedVirtPointsTo`): certificate plus a `frozen` token, duplicable and
//!   read-only. What `share` produces for content several pages genuinely observe in common.
//! - **Pinned** (`PinnedPointsTo`): an exclusive permission that also owns `obj_to_frame` and
//!   `frame_to_objs`, and so knows its frame *and* stops it changing. For memory the hardware reaches physically
//!   -- a page table page under CR3 -- where a relocation the software cannot see would be
//!   fatal.
//!
//! Physical sharing is policed separately: two objects may sit in one frame only while their
//! words agree, and a write demands that its object be the frame's sole resident. That requirement is the
//! copy-on-write trigger, discharged by `relocate` -- which is also, exactly, the page swap.
//!
//! Page size is a type parameter rather than a const generic -- the state machine macro rejects
//! const generics outright ("Only generic type parameters are supported for state machine").
use core::marker::PhantomData;

use vstd::prelude::*;

use verus_state_machines_macros::tokenized_state_machine;

verus! {

/// The architecture, at the type level: page size, and how a page table entry encodes the frame
/// it points at.
pub trait PageSizeSpec {
    spec fn size() -> nat;

    /// The word an entry pointing at `f` is stored as. Only the round trip is assumed, which is
    /// all a walk needs: distinct targets are distinguishable, and a written entry reads back.
    spec fn encode(f: Option<nat>) -> usize;

    spec fn decode(w: usize) -> Option<nat>;

    proof fn size_positive()
        ensures
            Self::size() > 0,
    ;

    proof fn decode_encode(f: Option<nat>)
        ensures
            Self::decode(Self::encode(f)) == f,
    ;
}

///  vp -> pfn
pub open spec fn walk_target(
    vmap: Map<nat, Option<nat>>,
    obj_to_frame: Map<nat, Option<nat>>,
    vp: nat,
) -> Option<nat> {
    match vmap[vp] {
        Option::None => Option::None,
        Option::Some(o) => obj_to_frame[o],
    }
}

/// The page a virtual address falls in.
pub open spec fn vpage<S: PageSizeSpec>(v: nat) -> nat {
    v / S::size()
}

/// How far into its page a virtual address sits.
pub open spec fn voffset<S: PageSizeSpec>(v: nat) -> nat {
    v % S::size()
}

/// The governed addresses of one page.
pub open spec fn page_addrs<S: PageSizeSpec>(dom: Set<nat>, vp: nat) -> Set<nat> {
    dom.filter(|v: nat| vpage::<S>(v) == vp)
}

/// The certificates of one page, all reading `oid`. Used to hand a page's certificates back.
pub open spec fn page_view<S: PageSizeSpec>(dom: Set<nat>, vp: nat, oid: Option<nat>) -> Map<
    nat,
    Option<nat>,
> {
    Map::new(page_addrs::<S>(dom, vp), |v: nat| oid)
}

/// The object id an address reaches in the object `obj`. An object's ids are contiguous, so one
/// number identifies all of them and a mapping mints one number rather than a set.
pub open spec fn oid_of<S: PageSizeSpec>(obj: nat, v: nat) -> nat {
    obj + voffset::<S>(v)
}

/// The object a certificate came from, recovered from the address it certifies. This is what lets
/// a write find its content without consulting the page table.
pub open spec fn obj_of<S: PageSizeSpec>(oid: nat, v: nat) -> nat {
    (oid - voffset::<S>(v)) as nat
}

/// The certificates a page gains from the object `obj`.
pub open spec fn mapped_view<S: PageSizeSpec>(dom: Set<nat>, vp: nat, obj: nat) -> Map<
    nat,
    Option<nat>,
> {
    Map::new(page_addrs::<S>(dom, vp), |v: nat| Some(oid_of::<S>(obj, v)))
}

/// The ids a freshly minted object covers.
pub open spec fn obj_ids<S: PageSizeSpec>(obj: nat) -> Set<nat> {
    Set::range(obj, obj + S::size())
}

/// A word, wherever it currently lives. Content is writable or frozen, never both, so this is
/// well defined for every id ever minted.
pub open spec fn word_at(data: Map<nat, usize>, frozen: Map<nat, usize>, c: nat) -> usize {
    if data.dom().contains(c) {
        data[c]
    } else {
        frozen[c]
    }
}

/// The page table words for a set of pages, all naming the frame `f`. Relocating an object
/// rewrites exactly these.
pub open spec fn entry_words<S: PageSizeSpec>(pt_obj: nat, vps: Set<nat>, f: Option<nat>) -> Map<
    nat,
    usize,
> {
    Map::new(vps.map(|vp: nat| (pt_obj + vp) as nat), |c: nat| S::encode(f))
}

/// The words a caller claims a frame holds for the object `obj`, as `relocate` and `fork` demand
/// them.
pub open spec fn content_of<S: PageSizeSpec>(obj: nat, words: Map<nat, usize>, src: nat) -> Map<
    nat,
    usize,
> {
    Map::new(obj_ids::<S>(src), |c: nat| words[(obj + c - src) as nat])
}

} // verus!

tokenized_state_machine!(Mem<S: PageSizeSpec> {
    fields {
        /// Object id -> its word, writable. The single copy, and what a write consumes.
        #[sharding(map)]
        pub data: Map<nat, usize>,

        /// Content that has been frozen: immutable, and its tokens duplicable, so any number of
        /// pages may read it at once. Freezing is one-way, which is what makes a frozen token
        /// safe to hand out freely.
        #[sharding(persistent_map)]
        pub frozen: Map<nat, usize>,

        /// Object -> the frame currently holding it. Purely physical: no certificate and
        /// no permission mentions it, which is why it can change under them.
        #[sharding(map)]
        pub obj_to_frame: Map<nat, Option<nat>>,

        /// Frame -> the objects placed there: the inverse of `obj_to_frame`, read from the frame's
        /// side. More than one resident only while those objects agree word for word, as after a
        /// fork, and until one of them needs to write.
        #[sharding(map)]
        pub frame_to_objs: Map<nat, Set<nat>>,

        /// The next unused object id. Monotonic, which is what makes a freshly minted object
        /// provably unused -- with a partial map, nothing else could own that fact.
        #[sharding(variable)]
        pub next_oid: nat,

        /// One page table entry: virtual page -> the object it reaches.
        #[sharding(map)]
        pub vmap: Map<nat, Option<nat>>,

        /// Object -> the pages that reach it: the inverse of `vmap`. Relocating an object means
        /// rewriting every page table entry that names its frame, so this is what says how many
        /// there are and which.
        #[sharding(map)]
        pub obj_to_vpages: Map<nat, Set<nat>>,

        /// Virtual address -> the object id it reaches. This is what a holder of the address
        /// keeps, and no physical relocation disturbs it.
        #[sharding(map)]
        pub vmem: Map<nat, Option<nat>>,

        /// The virtual addresses this machine governs. Fixed at boot.
        #[sharding(constant)]
        pub vmem_dom: Set<nat>,

        /// The virtual pages this machine governs. Fixed at boot.
        #[sharding(constant)]
        pub vmap_dom: Set<nat>,

        /// The physical frames this machine governs. Fixed at boot.
        #[sharding(constant)]
        pub frames_dom: Set<nat>,

        /// The object whose words *are* the page table. Its identity is fixed, though where it
        /// physically sits is not: it can be relocated like anything else, and the entries that
        /// name it get rewritten when it is.
        #[sharding(constant)]
        pub pt_obj: nat,

        #[sharding(constant)]
        pub marker: PhantomData<S>,
    }

    #[invariant]
    pub spec fn page_size_positive(&self) -> bool {
        S::size() > 0
    }

    /// Every governed address, page, and frame always has a token.
    #[invariant]
    pub spec fn domains_fixed(&self) -> bool {
        &&& self.vmem.dom() =~= self.vmem_dom
        &&& self.vmap.dom() =~= self.vmap_dom
        &&& self.frame_to_objs.dom() =~= self.frames_dom
    }

    /// Every governed address sits in a governed page, so a certificate always has an entry to
    /// answer for it.
    #[invariant]
    pub spec fn pages_governed(&self) -> bool {
        forall|v: nat| #[trigger] self.vmem_dom.contains(v) ==> self.vmap_dom.contains(vpage::<S>(v))
    }

    /// A certificate is answered by the page table alone: the address's page reaches some
    /// content, and the certificate names the id that content gives the address's offset. No
    /// frame appears, which is precisely why relocation is invisible here.
    #[invariant]
    pub spec fn certificates_backed(&self) -> bool {
        forall|v: nat| #[trigger] self.vmem_dom.contains(v) && self.vmem[v] is Some ==> {
            &&& self.vmap[vpage::<S>(v)] is Some
            &&& self.vmem[v]->Some_0 == oid_of::<S>(self.vmap[vpage::<S>(v)]->Some_0, v)
        }
    }

    /// Every id ever minted lies below `next_oid`, so the ids a mapping mints are unused.
    #[invariant]
    pub spec fn ids_fresh(&self) -> bool {
        &&& forall|c: nat| #[trigger] self.data.dom().contains(c) ==> c < self.next_oid
        &&& forall|c: nat| #[trigger] self.frozen.dom().contains(c) ==> c < self.next_oid
        &&& forall|b: nat| #[trigger] self.obj_to_frame.dom().contains(b) ==> b + S::size() <= self.next_oid
        &&& forall|vp: nat|
            #[trigger] self.vmap_dom.contains(vp) && self.vmap[vp] is Some
                ==> self.vmap[vp]->Some_0 + S::size() <= self.next_oid
    }

    /// Content is writable or frozen, never both -- otherwise a writer could move content out
    /// from under a reader holding a frozen token -- and every minted id is one or the other, so
    /// content is never lost.
    #[invariant]
    pub spec fn content_total(&self) -> bool {
        &&& forall|c: nat| #[trigger] self.data.dom().contains(c) ==> !self.frozen.dom().contains(c)
        &&& forall|b: nat| #[trigger] self.obj_to_frame.dom().contains(b) ==> obj_ids::<S>(b).subset_of(
            self.data.dom().union(self.frozen.dom()),
        )
    }

    /// Distinct objects cover distinct ids, so a write to one object's word is not a write to
    /// another's. Minting at `next_oid` is what keeps this true.
    #[invariant]
    pub spec fn objects_disjoint(&self) -> bool {
        forall|b1: nat, b2: nat, c: nat|
            self.obj_to_frame.dom().contains(b1) && #[trigger] self.obj_to_frame.dom().contains(b2)
                && #[trigger] obj_ids::<S>(b1).contains(c) && obj_ids::<S>(b2).contains(c)
                ==> b1 == b2
    }

    /// The page table is not a separate thing from memory: `vmap` is a reading of the words of
    /// `pt_obj`. Every entry decodes to the frame currently holding whatever the page maps, so
    /// installing a mapping *is* writing a word, and relocating an object obliges every entry
    /// naming it to be rewritten.
    #[invariant]
    pub spec fn walk_agrees(&self) -> bool {
        &&& self.obj_to_frame.dom().contains(self.pt_obj)
        &&& self.obj_to_frame[self.pt_obj] is Some
        &&& forall|vp: nat| #[trigger] self.vmap_dom.contains(vp) ==> {
            &&& vp < S::size()
            &&& S::decode(word_at(self.data, self.frozen, (self.pt_obj + vp) as nat))
                == walk_target(self.vmap, self.obj_to_frame, vp)
        }
    }

    /// Nothing may co-reside with the page table. Entries are ordinary words, so a page sharing
    /// the page table's frame would have to agree with it word for word -- and then editing an
    /// entry would silently edit that page too. Forking or mapping onto the page table's frame is
    /// therefore refused rather than reasoned about.
    #[invariant]
    pub spec fn pt_solo(&self) -> bool {
        self.frame_to_objs[self.obj_to_frame[self.pt_obj]->Some_0] =~= Set::<nat>::empty().insert(
            self.pt_obj,
        )
    }

    /// `obj_to_vpages` and `vmap` are two views of one relation, and every minted object has an
    /// entry, empty while nothing maps it.
    #[invariant]
    pub spec fn mapping_sound(&self) -> bool {
        &&& self.obj_to_vpages.dom() =~= self.obj_to_frame.dom()
        &&& forall|o: nat, vp: nat|
            self.obj_to_vpages.dom().contains(o) && #[trigger] self.obj_to_vpages[o].contains(vp)
                ==> {
                &&& self.vmap_dom.contains(vp)
                &&& self.vmap[vp] == Some(o)
            }
    }

    #[invariant]
    pub spec fn mapping_complete(&self) -> bool {
        forall|vp: nat| #[trigger] self.vmap_dom.contains(vp) && self.vmap[vp] is Some ==> {
            &&& self.obj_to_vpages.dom().contains(self.vmap[vp]->Some_0)
            &&& self.obj_to_vpages[self.vmap[vp]->Some_0].contains(vp)
        }
    }

    /// `frame_to_objs` and `obj_to_frame` are two views of one relation. Keeping both is what lets a write
    /// demand sole use of a frame while naming only its own content.
    #[invariant]
    pub spec fn residency_sound(&self) -> bool {
        forall|pfn: nat, b: nat|
            self.frames_dom.contains(pfn) && #[trigger] self.frame_to_objs[pfn].contains(b) ==> {
                &&& self.obj_to_frame.dom().contains(b)
                &&& self.obj_to_frame[b] == Some(pfn)
            }
    }

    #[invariant]
    pub spec fn residency_complete(&self) -> bool {
        forall|b: nat| #[trigger] self.obj_to_frame.dom().contains(b) && self.obj_to_frame[b] is Some ==> {
            &&& self.frames_dom.contains(self.obj_to_frame[b]->Some_0)
            &&& self.frame_to_objs[self.obj_to_frame[b]->Some_0].contains(b)
        }
    }

    /// A frame holds one set of words, so objects sharing a frame must agree. This is the
    /// obligation that makes physical sharing honest, and the reason a write insists on being
    /// its frame's sole resident.
    #[invariant]
    pub spec fn coplaced_agree(&self) -> bool {
        forall|b1: nat, b2: nat, off: nat|
            self.obj_to_frame.dom().contains(b1) && #[trigger] self.obj_to_frame.dom().contains(b2)
                && self.obj_to_frame[b1] is Some && self.obj_to_frame[b1] == self.obj_to_frame[b2] && off < S::size()
                ==> #[trigger] word_at(self.data, self.frozen, (b1 + off) as nat) == word_at(
                self.data,
                self.frozen,
                (b2 + off) as nat,
            )
    }

    init!{
        boot(frames: Set<nat>, vpages: Set<nat>, vaddrs: Set<nat>, pt_frame: nat) {
            require forall|v: nat| #[trigger] vaddrs.contains(v) ==> vpages.contains(vpage::<S>(v));
            require forall|vp: nat| #[trigger] vpages.contains(vp) ==> vp < S::size();
            require frames.contains(pt_frame);
            init data = Map::new(obj_ids::<S>(0), |c: nat| S::encode(Option::<nat>::None));
            init frozen = Map::empty();
            init obj_to_frame = Map::empty().insert(0, Some(pt_frame));
            init obj_to_vpages = Map::empty().insert(0, Set::<nat>::empty());
            init frame_to_objs = Map::new(
                frames,
                |pfn: nat|
                    if pfn == pt_frame {
                        Set::<nat>::empty().insert(0)
                    } else {
                        Set::<nat>::empty()
                    },
            );
            init frames_dom = frames;
            init pt_obj = 0;
            init next_oid = S::size();
            init vmap = Map::new(vpages, |vp: nat| Option::<nat>::None);
            init vmap_dom = vpages;
            init vmem = Map::new(vaddrs, |v: nat| Option::<nat>::None);
            init vmem_dom = vaddrs;
            init marker = PhantomData;
        }
    }

    /// Map a page onto a frame nobody is using, minting fresh content for it. This is where
    /// object ids come from, and the caller gets both the certificates and the content, so it
    /// is the only transition that hands out a full exclusive permission. `words` is what the
    /// frame physically holds, which the claimer is the one in a position to say.
    transition!{
        map(vp: nat, pfn: nat, words: Map<nat, usize>) {
            remove frame_to_objs -= [pfn => let occupants];
            require occupants =~= Set::<nat>::empty();
            add frame_to_objs += [pfn => Set::<nat>::empty().insert(pre.next_oid)];
            add obj_to_frame += [pre.next_oid => Some(pfn)];
            add obj_to_vpages += [pre.next_oid => Set::<nat>::empty().insert(vp)];
            require words.dom() =~= obj_ids::<S>(pre.next_oid);
            remove data -= [(pre.pt_obj + vp) as nat => let _stale];
            add data += [(pre.pt_obj + vp) as nat => S::encode(Some(pfn))];
            add data += (words);
            update next_oid = pre.next_oid + S::size();
            remove vmap -= [vp => let route];
            require route is None;
            add vmap += [vp => Some(pre.next_oid)];
            remove vmem -= (page_view::<S>(pre.vmem_dom, vp, Option::<nat>::None));
            add vmem += (mapped_view::<S>(pre.vmem_dom, vp, pre.next_oid));
        }
    }

    /// Map a second page onto content that already exists. Both pages then hold certificates for
    /// the *same* ids, so a write through one is a write the other sees -- genuine shared memory,
    /// not a fork. The content must be frozen for anyone to read it through both.
    transition!{
        share(vp: nat, obj: nat) {
            have obj_to_frame >= [obj => let p];
            require p is Some;
            remove vmap -= [vp => let route];
            require route is None;
            add vmap += [vp => Some(obj)];
            remove obj_to_vpages -= [obj => let vps];
            add obj_to_vpages += [obj => vps.insert(vp)];
            remove data -= [(pre.pt_obj + vp) as nat => let _stale];
            add data += [(pre.pt_obj + vp) as nat => S::encode(p)];
            remove vmem -= (page_view::<S>(pre.vmem_dom, vp, Option::<nat>::None));
            add vmem += (mapped_view::<S>(pre.vmem_dom, vp, obj));
        }
    }

    /// Fork: map a page onto the frame that already holds `src_obj`, but mint it *fresh*
    /// content. The two pages share a frame and nothing else -- separate ids, separate `data`
    /// tokens, separate futures. `have data` is the obligation that the new content really is a
    /// copy of the old, which is what makes sharing the frame honest until one of them writes.
    transition!{
        fork(vp: nat, pfn: nat, src_obj: nat, words: Map<nat, usize>) {
            have obj_to_frame >= [src_obj => let sp];
            require sp == Some(pfn);
            require src_obj != pre.pt_obj;
            remove frame_to_objs -= [pfn => let occupants];
            add frame_to_objs += [pfn => occupants.insert(pre.next_oid)];
            add obj_to_frame += [pre.next_oid => Some(pfn)];
            add obj_to_vpages += [pre.next_oid => Set::<nat>::empty().insert(vp)];
            require words.dom() =~= obj_ids::<S>(pre.next_oid);
            remove data -= [(pre.pt_obj + vp) as nat => let _stale];
            have data >= (content_of::<S>(pre.next_oid, words, src_obj));
            add data += [(pre.pt_obj + vp) as nat => S::encode(Some(pfn))];
            add data += (words);
            update next_oid = pre.next_oid + S::size();
            remove vmap -= [vp => let route];
            require route is None;
            add vmap += [vp => Some(pre.next_oid)];
            remove vmem -= (page_view::<S>(pre.vmem_dom, vp, Option::<nat>::None));
            add vmem += (mapped_view::<S>(pre.vmem_dom, vp, pre.next_oid));
        }
    }

    /// Move content to a frame nobody is using, having copied its words there. Neither the page
    /// table nor any certificate is touched, because none of them names a frame. This single
    /// transition is both halves of the story the object id exists for: run on the sole resident of
    /// a frame it is a **page swap**, and run on one of several it is the copy half of
    /// **copy-on-write**, after which the mover is sole resident and may write.
    transition!{
        relocate(obj: nat, pfn: nat, words: Map<nat, usize>) {
            remove obj_to_frame -= [obj => let old];
            require old is Some;
            require old->Some_0 != pfn;
            add obj_to_frame += [obj => Some(pfn)];
            remove frame_to_objs -= [old->Some_0 => let leaving];
            remove frame_to_objs -= [pfn => let arriving];
            require arriving =~= Set::<nat>::empty();
            add frame_to_objs += [old->Some_0 => leaving.remove(obj)];
            add frame_to_objs += [pfn => Set::<nat>::empty().insert(obj)];
            require obj != pre.pt_obj;
            have obj_to_vpages >= [obj => let vps];
            remove data -= (entry_words::<S>(pre.pt_obj, vps, old));
            require words.dom() =~= obj_ids::<S>(obj);
            have data >= (words);
            add data += (entry_words::<S>(pre.pt_obj, vps, Some(pfn)));
        }
    }

    /// Drop a page table entry. The caller must hand back every certificate the page issued,
    /// which is what stops an address being left holding content it can no longer reach.
    transition!{
        unmap(vp: nat) {
            remove vmap -= [vp => let route];
            require route is Some;
            add vmap += [vp => Option::<nat>::None];
            remove obj_to_vpages -= [route->Some_0 => let vps];
            add obj_to_vpages += [route->Some_0 => vps.remove(vp)];
            remove data -= [(pre.pt_obj + vp) as nat => let _stale];
            add data += [(pre.pt_obj + vp) as nat => S::encode(Option::<nat>::None)];
            remove vmem -= (mapped_view::<S>(pre.vmem_dom, vp, route->Some_0));
            add vmem += (page_view::<S>(pre.vmem_dom, vp, Option::<nat>::None));
        }
    }

    /// Give up the right to write some content in exchange for the right to share it.
    transition!{
        freeze(oid: nat) {
            require !obj_ids::<S>(pre.pt_obj).contains(oid);
            remove data -= [oid => let w];
            add frozen (union)= [oid => w];
        }
    }

    /// Write content. The certificate says which content, the `data` token confers the right,
    /// and `frame_to_objs` witnesses that no other content shares the frame -- so a page still sharing a
    /// frame after a fork cannot write until it has relocated. No page table entry is consulted,
    /// so a concurrent remap cannot block a write.
    transition!{
        write_non_pt(v: nat, val: usize) {
            have vmem >= [v => let oid];
            require oid is Some;
            let obj = obj_of::<S>(oid->Some_0, v);
            have obj_to_frame >= [obj => let p];
            require p is Some;
            have frame_to_objs >= [p->Some_0 => let occupants];
            require occupants =~= Set::<nat>::empty().insert(obj);
            require !obj_ids::<S>(pre.pt_obj).contains(oid->Some_0);
            remove data -= [oid->Some_0 => let old];
            add data += [oid->Some_0 => val];
        }
    }

    /// Read through a certificate and the content it names.
    property!{
        read(v: nat) {
            have vmem >= [v => let oid];
            require oid is Some;
            have data >= [oid->Some_0 => let w];
        }
    }

    /// Read shared content. Never writable, because writing consumes a `data` token and frozen
    /// content has none.
    property!{
        read_shared(v: nat) {
            have vmem >= [v => let oid];
            require oid is Some;
            have frozen >= [oid->Some_0 => let w];
        }
    }

    /// Two addresses reach the same content exactly when their certificates carry the same id.
    /// No reverse map is needed to discover this: it is visible in the tokens themselves.
    property!{
        alias(v1: nat, v2: nat) {
            have vmem >= [v1 => let c1];
            have vmem >= [v2 => let c2];
            require c1 is Some && c1 == c2;
        }
    }

    #[inductive(boot)]
    fn boot_inductive(
        post: Self,
        frames: Set<nat>,
        vpages: Set<nat>,
        vaddrs: Set<nat>,
        pt_frame: nat,
    ) {
        broadcast use vstd::set_lib::group_set_lib_default;

        S::size_positive();
        assert forall|vp: nat| #[trigger] post.vmap_dom.contains(vp) implies {
            &&& vp < S::size()
            &&& S::decode(word_at(post.data, post.frozen, (post.pt_obj + vp) as nat))
                == walk_target(post.vmap, post.obj_to_frame, vp)
        } by {
            assert(obj_ids::<S>(0).contains(vp));
            S::decode_encode(Option::<nat>::None);
        }
        assert(post.vmem.dom() =~= post.vmem_dom);
        assert(post.vmap.dom() =~= post.vmap_dom);
        assert(post.frame_to_objs.dom() =~= post.frames_dom);
    }

    #[inductive(map)]
    fn map_inductive(pre: Self, post: Self, vp: nat, pfn: nat, words: Map<nat, usize>) {
        broadcast use vstd::set_lib::group_set_lib_default;

        Self::mapped_page(pre, post, vp, pre.next_oid);
        Self::fresh_base(pre, post, pfn, pre.next_oid, words);
        assert forall|b1: nat, b2: nat, c: nat|
            post.obj_to_frame.dom().contains(b1) && #[trigger] post.obj_to_frame.dom().contains(b2)
                && #[trigger] obj_ids::<S>(b1).contains(c) && obj_ids::<S>(b2).contains(c)
            implies b1 == b2 by {
            if b1 != pre.next_oid {
                assert(pre.obj_to_frame.dom().contains(b1));
            }
            if b2 != pre.next_oid {
                assert(pre.obj_to_frame.dom().contains(b2));
            }
        }
        assert forall|b1: nat, b2: nat, off: nat|
            post.obj_to_frame.dom().contains(b1) && #[trigger] post.obj_to_frame.dom().contains(b2)
                && post.obj_to_frame[b1] is Some && post.obj_to_frame[b1] == post.obj_to_frame[b2] && off < S::size()
            implies #[trigger] word_at(post.data, post.frozen, (b1 + off) as nat) == word_at(
            post.data,
            post.frozen,
            (b2 + off) as nat,
        ) by {
            if b1 == pre.next_oid || b2 == pre.next_oid {
                assert(post.obj_to_frame[b1]->Some_0 == pfn);
                assert(b1 == pre.next_oid) by {
                    if b1 != pre.next_oid {
                        assert(pre.obj_to_frame.dom().contains(b1) && pre.obj_to_frame[b1] == Some(pfn));
                        assert(pre.frame_to_objs[pfn].contains(b1));
                    }
                }
                assert(b2 == pre.next_oid) by {
                    if b2 != pre.next_oid {
                        assert(pre.obj_to_frame.dom().contains(b2) && pre.obj_to_frame[b2] == Some(pfn));
                        assert(pre.frame_to_objs[pfn].contains(b2));
                    }
                }
            } else {
                assert(pre.obj_to_frame.dom().contains(b1) && pre.obj_to_frame.dom().contains(b2));
                assert(word_at(pre.data, pre.frozen, (b1 + off) as nat) == word_at(
                    pre.data,
                    pre.frozen,
                    (b2 + off) as nat,
                ));
            }
        }
    }

    #[inductive(share)]
    fn share_inductive(pre: Self, post: Self, vp: nat, obj: nat) {
        broadcast use vstd::set_lib::group_set_lib_default;

        Self::mapped_page(pre, post, vp, obj);
    }

    #[inductive(fork)]
    fn fork_inductive(
        pre: Self,
        post: Self,
        vp: nat,
        pfn: nat,
        src_obj: nat,
        words: Map<nat, usize>,
    ) {
        broadcast use vstd::set_lib::group_set_lib_default;

        Self::mapped_page(pre, post, vp, pre.next_oid);
        Self::fresh_base(pre, post, pfn, pre.next_oid, words);
        assert forall|off: nat| off < S::size() implies #[trigger] word_at(
            post.data,
            post.frozen,
            (pre.next_oid + off) as nat,
        ) == word_at(post.data, post.frozen, (src_obj + off) as nat) by {
            assert(obj_ids::<S>(src_obj).contains((src_obj + off) as nat));
            assert(content_of::<S>(pre.next_oid, words, src_obj)[(src_obj + off) as nat]
                == words[(pre.next_oid + off) as nat]);
        }
        assert(pre.frame_to_objs[pfn].contains(src_obj));
        assert forall|b1: nat, b2: nat, c: nat|
            post.obj_to_frame.dom().contains(b1) && #[trigger] post.obj_to_frame.dom().contains(b2)
                && #[trigger] obj_ids::<S>(b1).contains(c) && obj_ids::<S>(b2).contains(c)
            implies b1 == b2 by {
            if b1 != pre.next_oid {
                assert(pre.obj_to_frame.dom().contains(b1));
            }
            if b2 != pre.next_oid {
                assert(pre.obj_to_frame.dom().contains(b2));
            }
        }
        assert forall|b1: nat, b2: nat, off: nat|
            post.obj_to_frame.dom().contains(b1) && #[trigger] post.obj_to_frame.dom().contains(b2)
                && post.obj_to_frame[b1] is Some && post.obj_to_frame[b1] == post.obj_to_frame[b2] && off < S::size()
            implies #[trigger] word_at(post.data, post.frozen, (b1 + off) as nat) == word_at(
            post.data,
            post.frozen,
            (b2 + off) as nat,
        ) by {
            if b1 != pre.next_oid && b2 != pre.next_oid {
                assert(pre.obj_to_frame.dom().contains(b1) && pre.obj_to_frame.dom().contains(b2));
                assert(word_at(pre.data, pre.frozen, (b1 + off) as nat) == word_at(
                    pre.data,
                    pre.frozen,
                    (b2 + off) as nat,
                ));
            } else {
                assert(post.obj_to_frame[b1]->Some_0 == pfn);
                assert(word_at(post.data, post.frozen, (pre.next_oid + off) as nat) == word_at(
                    post.data,
                    post.frozen,
                    (src_obj + off) as nat,
                ));
                if b1 != pre.next_oid {
                    assert(pre.obj_to_frame.dom().contains(b1) && pre.obj_to_frame[b1] == Some(pfn));
                    assert(word_at(pre.data, pre.frozen, (b1 + off) as nat) == word_at(
                        pre.data,
                        pre.frozen,
                        (src_obj + off) as nat,
                    ));
                }
                if b2 != pre.next_oid {
                    assert(pre.obj_to_frame.dom().contains(b2) && pre.obj_to_frame[b2] == Some(pfn));
                    assert(word_at(pre.data, pre.frozen, (b2 + off) as nat) == word_at(
                        pre.data,
                        pre.frozen,
                        (src_obj + off) as nat,
                    ));
                }
            }
        }
    }

    #[inductive(relocate)]
    fn relocate_inductive(pre: Self, post: Self, obj: nat, pfn: nat, words: Map<nat, usize>) {
        assert(post.frame_to_objs.dom() =~= post.frames_dom);
        assert forall|b: nat| #[trigger] post.obj_to_frame.dom().contains(b) && post.obj_to_frame[b] is Some
            implies {
            &&& post.frames_dom.contains(post.obj_to_frame[b]->Some_0)
            &&& post.frame_to_objs[post.obj_to_frame[b]->Some_0].contains(b)
        } by {
            if b != obj {
                assert(pre.obj_to_frame[b] == post.obj_to_frame[b]);
                assert(pre.frame_to_objs[pre.obj_to_frame[b]->Some_0].contains(b));
            }
        }
        assert forall|b1: nat, b2: nat, off: nat|
            post.obj_to_frame.dom().contains(b1) && #[trigger] post.obj_to_frame.dom().contains(b2)
                && post.obj_to_frame[b1] is Some && post.obj_to_frame[b1] == post.obj_to_frame[b2] && off < S::size()
            implies #[trigger] word_at(post.data, post.frozen, (b1 + off) as nat) == word_at(
            post.data,
            post.frozen,
            (b2 + off) as nat,
        ) by {
            if b1 == obj || b2 == obj {
                assert(post.obj_to_frame[b1]->Some_0 == pfn);
                assert(post.frame_to_objs[pfn].contains(b1));
                assert(post.frame_to_objs[pfn].contains(b2));
            } else {
                assert(pre.obj_to_frame.dom().contains(b1) && pre.obj_to_frame.dom().contains(b2));
                assert(word_at(pre.data, pre.frozen, (b1 + off) as nat) == word_at(
                    pre.data,
                    pre.frozen,
                    (b2 + off) as nat,
                ));
            }
        }
    }

    #[inductive(unmap)]
    fn unmap_inductive(pre: Self, post: Self, vp: nat) {
        broadcast use vstd::set_lib::group_set_lib_default;

        assert(post.vmem.dom() =~= post.vmem_dom);
        assert(post.vmap.dom() =~= post.vmap_dom);
        assert forall|v: nat| #[trigger] post.vmem_dom.contains(v) && post.vmem[v] is Some implies {
            &&& post.vmap[vpage::<S>(v)] is Some
            &&& post.vmem[v]->Some_0 == oid_of::<S>(post.vmap[vpage::<S>(v)]->Some_0, v)
        } by {
            assert(vpage::<S>(v) != vp);
        }
    }

    #[inductive(freeze)]
    fn freeze_inductive(pre: Self, post: Self, oid: nat) {
        assert forall|b: nat, off: nat| post.obj_to_frame.dom().contains(b) && off < S::size()
            implies #[trigger] word_at(post.data, post.frozen, (b + off) as nat) == word_at(
            pre.data,
            pre.frozen,
            (b + off) as nat,
        ) by {
        }
    }

    #[inductive(write_non_pt)]
    fn write_non_pt_inductive(pre: Self, post: Self, v: nat, val: usize) {
        let obj = obj_of::<S>(pre.vmem[v]->Some_0, v);
        assert forall|b1: nat, b2: nat, off: nat|
            post.obj_to_frame.dom().contains(b1) && #[trigger] post.obj_to_frame.dom().contains(b2)
                && post.obj_to_frame[b1] is Some && post.obj_to_frame[b1] == post.obj_to_frame[b2] && off < S::size()
            implies #[trigger] word_at(post.data, post.frozen, (b1 + off) as nat) == word_at(
            post.data,
            post.frozen,
            (b2 + off) as nat,
        ) by {
            let oid = pre.vmem[v]->Some_0;
            assert(obj_ids::<S>(obj).contains(oid));
            assert(post.frame_to_objs[post.obj_to_frame[b1]->Some_0].contains(b1));
            assert(post.frame_to_objs[post.obj_to_frame[b2]->Some_0].contains(b2));
            if b1 != obj {
                assert(obj_ids::<S>(b1).contains((b1 + off) as nat));
            }
            if b2 != obj {
                assert(obj_ids::<S>(b2).contains((b2 + off) as nat));
            }
            assert(word_at(pre.data, pre.frozen, (b1 + off) as nat) == word_at(
                pre.data,
                pre.frozen,
                (b2 + off) as nat,
            ));
        }
    }

    /// The certificates and entry of one page after it is pointed at the object `obj`; shared by every
    /// transition that installs a mapping.
    pub proof fn mapped_page(pre: Self, post: Self, vp: nat, obj: nat)
        requires
            pre.invariant(),
            post.vmem_dom == pre.vmem_dom,
            post.vmap_dom == pre.vmap_dom,
            post.vmap =~= pre.vmap.insert(vp, Some(obj)),
            post.vmem =~= pre.vmem.union_prefer_right(
                mapped_view::<S>(pre.vmem_dom, vp, obj),
            ),
            pre.vmap_dom.contains(vp),
        ensures
            post.vmem.dom() =~= post.vmem_dom,
            post.vmap.dom() =~= post.vmap_dom,
            post.certificates_backed(),
    {
        broadcast use vstd::set_lib::group_set_lib_default;

        assert(post.vmem.dom() =~= post.vmem_dom);
        assert forall|v: nat| #[trigger] post.vmem_dom.contains(v) && post.vmem[v] is Some implies {
            &&& post.vmap[vpage::<S>(v)] is Some
            &&& post.vmem[v]->Some_0 == oid_of::<S>(post.vmap[vpage::<S>(v)]->Some_0, v)
        } by {
            if vpage::<S>(v) != vp {
                assert(pre.vmem[v] == post.vmem[v]);
            }
        }
    }

    /// A freshly minted object is unused, so nothing it adds collides and nothing already placed
    /// shares its frame's words by accident.
    pub proof fn fresh_base(
        pre: Self,
        post: Self,
        pfn: nat,
        obj: nat,
        words: Map<nat, usize>,
        entries: Map<nat, usize>,
    )
        requires
            pre.invariant(),
            obj == pre.next_oid,
            words.dom() =~= obj_ids::<S>(obj),
            entries.dom().subset_of(obj_ids::<S>(pre.pt_obj)),
            post.data =~= pre.data.union_prefer_right(entries).union_prefer_right(words),
            post.frozen =~= pre.frozen,
            post.next_oid == pre.next_oid + S::size(),
        ensures
            post.ids_fresh() <==> {
                &&& forall|b: nat| #[trigger] post.obj_to_frame.dom().contains(b) ==> b + S::size()
                    <= post.next_oid
                &&& forall|vp: nat|
                    #[trigger] post.vmap_dom.contains(vp) && post.vmap[vp] is Some
                        ==> post.vmap[vp]->Some_0 + S::size() <= post.next_oid
            },
            forall|c: nat| #[trigger] post.data.dom().contains(c) ==> !post.frozen.dom().contains(c),
            forall|off: nat| off < S::size() ==> #[trigger] word_at(
                post.data,
                post.frozen,
                (obj + off) as nat,
            ) == words[(obj + off) as nat],
    {
        broadcast use vstd::set_lib::group_set_lib_default;

        assert forall|c: nat| #[trigger] post.data.dom().contains(c) implies c < post.next_oid by {
            if !pre.data.dom().contains(c) {
                assert(obj_ids::<S>(obj).contains(c));
            }
        }
        assert forall|c: nat| #[trigger] post.data.dom().contains(c) implies
            !post.frozen.dom().contains(c) by {
            if !pre.data.dom().contains(c) {
                assert(obj_ids::<S>(obj).contains(c));
            }
        }
        assert forall|c: nat| c < obj implies #[trigger] word_at(post.data, post.frozen, c)
            == word_at(pre.data, pre.frozen, c) by {
            assert(!obj_ids::<S>(obj).contains(c));
        }
    }
});


verus! {

/// The certificates of a whole page, as the mapping transitions trade them.
pub type PageCerts<S> = vstd::tokens::MapToken<nat, Option<nat>, Mem::vmem<S>>;

/// The content of a whole page.
pub type PageData<S> = vstd::tokens::MapToken<nat, usize, Mem::data<S>>;

/// **Exclusive** permission to the content a virtual address reaches: the certificate saying
/// *which* content, and the content itself. Neither half is enough -- the certificate alone says
/// only that the address is mapped, and the content alone does not say how to reach it. This is
/// what a fresh mapping and a copy-on-write both produce, and it is the only kind that can be
/// written through.
pub tracked struct VirtPointsTo<S: PageSizeSpec> {
    pub tracked cert: Mem::vmem<S>,
    pub tracked content: Mem::data<S>,
}

impl<S: PageSizeSpec> VirtPointsTo<S> {
    pub open spec fn instance_id(self) -> vstd::tokens::InstanceId {
        self.cert.instance_id()
    }

    pub open spec fn addr(self) -> nat {
        self.cert.key()
    }

    pub open spec fn oid(self) -> nat {
        self.content.key()
    }

    pub open spec fn value(self) -> usize {
        self.content.value()
    }

    pub open spec fn wf(self) -> bool {
        &&& self.cert.value() == Some(self.oid())
        &&& self.content.instance_id() == self.cert.instance_id()
    }
}

/// **Shared** permission: the certificate, and a duplicable token for frozen content. Several
/// addresses may hold one for the same object id, and none of them can write it, because a
/// write consumes a `data` token and frozen content has none. A page created by a fork does
/// *not* get one of these -- it gets its own exclusive permission over its own object id,
/// because its content is destined to diverge.
pub tracked struct SharedVirtPointsTo<S: PageSizeSpec> {
    pub tracked cert: Mem::vmem<S>,
    pub tracked content: Mem::frozen<S>,
}

impl<S: PageSizeSpec> SharedVirtPointsTo<S> {
    pub open spec fn addr(self) -> nat {
        self.cert.key()
    }

    pub open spec fn oid(self) -> nat {
        self.content.key()
    }

    pub open spec fn value(self) -> usize {
        self.content.value()
    }

    pub open spec fn wf(self) -> bool {
        &&& self.cert.value() == Some(self.oid())
        &&& self.content.instance_id() == self.cert.instance_id()
    }
}

/// Permission to a word with no way to address it: object id and content, and no address of
/// either kind. It names nothing physical -- where the word sits is `obj_to_frame`'s business -- which
/// is why relocation never touches it and why it survives an unmap.
pub tracked struct LogicalPointsTo<S: PageSizeSpec> {
    pub tracked content: Mem::data<S>,
}

/// A certificate and the content it names compose into a permission. This is the only way to
/// build one, so a permission can never outlive the mapping that justified it.
pub proof fn attach<S: PageSizeSpec>(
    tracked cert: Mem::vmem<S>,
    tracked logical: LogicalPointsTo<S>,
) -> (tracked perm: VirtPointsTo<S>)
    requires
        cert.value() == Some(logical.content.key()),
        cert.instance_id() == logical.content.instance_id(),
    ensures
        perm.wf(),
        perm.addr() == cert.key(),
        perm.oid() == logical.content.key(),
        perm.value() == logical.content.value(),
{
    let tracked LogicalPointsTo { content } = logical;
    VirtPointsTo { cert, content }
}

/// Taking a permission apart gives back the content, which is what makes it possible to unmap:
/// the certificate goes back to the page table, the content does not.
pub proof fn detach<S: PageSizeSpec>(tracked perm: VirtPointsTo<S>) -> (tracked r: (
    Mem::vmem<S>,
    LogicalPointsTo<S>,
))
    ensures
        r.0 == perm.cert,
        r.1.content == perm.content,
{
    let tracked VirtPointsTo { cert, content } = perm;
    (cert, LogicalPointsTo { content })
}

/// Map a page onto an unused frame, minting fresh content. The caller gives up the frame, the
/// page's empty certificates, *and the page table entry's old word* -- because installing a
/// mapping is not a separate act from writing memory, it is writing memory. What comes back
/// includes the entry's new word, along with the content and certificates that make up a full
/// exclusive permission for every address in the page.
pub proof fn map_page<S: PageSizeSpec>(
    tracked inst: &Mem::Instance<S>,
    vp: nat,
    pfn: nat,
    words: Map<nat, usize>,
    tracked stale: Mem::data<S>,
    tracked frame: Mem::frame_to_objs<S>,
    tracked next: &mut Mem::next_oid<S>,
    tracked entry: Mem::vmap<S>,
    tracked certs: PageCerts<S>,
) -> (tracked r: (
    Mem::data<S>,
    PageData<S>,
    Mem::obj_to_frame<S>,
    Mem::frame_to_objs<S>,
    Mem::vmap<S>,
    Mem::obj_to_vpages<S>,
    PageCerts<S>,
))
    requires
        old(next).instance_id() == inst.id(),
        stale.instance_id() == inst.id(),
        frame.instance_id() == inst.id(),
        entry.instance_id() == inst.id(),
        certs.instance_id() == inst.id(),
        stale.key() == inst.pt_obj() + vp,
        frame.key() == pfn,
        frame.value() =~= Set::<nat>::empty(),
        entry.key() == vp,
        entry.value() is None,
        words.dom() =~= obj_ids::<S>(old(next).value()),
        certs.map() =~= page_view::<S>(inst.vmem_dom(), vp, Option::<nat>::None),
    ensures
        r.0.key() == inst.pt_obj() + vp,
        r.0.value() == S::encode(Some(pfn)),
        r.1.map() =~= words,
        r.2.key() == old(next).value(),
        r.2.value() == Some(pfn),
        r.3.key() == pfn,
        r.3.value() =~= Set::<nat>::empty().insert(old(next).value()),
        r.4.key() == vp,
        r.4.value() == Some(old(next).value()),
        r.5.key() == old(next).value(),
        r.5.value() =~= Set::<nat>::empty().insert(vp),
        r.6.map() =~= mapped_view::<S>(inst.vmem_dom(), vp, old(next).value()),
        final(next).value() == old(next).value() + S::size(),
{
    let tracked res = inst.map(vp, pfn, words, stale, frame, next, entry, certs);
    (
        res.0.get(),
        res.1.get(),
        res.2.get(),
        res.3.get(),
        res.4.get(),
        res.5.get(),
        res.6.get(),
    )
}

/// Fork a page: map it onto the frame that already holds `src_obj`, but mint it its own object.
/// The parent lends its content (`&PageData`) purely to attest that the words are a copy; what
/// comes back is a *separate* exclusive permission, not a share of the parent's. That is what
/// lets the copy-on-write, when it comes, disturb nothing the child holds.
pub proof fn fork_page<S: PageSizeSpec>(
    tracked inst: &Mem::Instance<S>,
    vp: nat,
    pfn: nat,
    src_obj: nat,
    words: Map<nat, usize>,
    tracked stale: Mem::data<S>,
    tracked src: &PageData<S>,
    tracked src_place: &Mem::obj_to_frame<S>,
    tracked frame: Mem::frame_to_objs<S>,
    tracked next: &mut Mem::next_oid<S>,
    tracked entry: Mem::vmap<S>,
    tracked certs: PageCerts<S>,
) -> (tracked r: (
    Mem::data<S>,
    PageData<S>,
    Mem::obj_to_frame<S>,
    Mem::frame_to_objs<S>,
    Mem::vmap<S>,
    Mem::obj_to_vpages<S>,
    PageCerts<S>,
))
    requires
        old(next).instance_id() == inst.id(),
        stale.instance_id() == inst.id(),
        src.instance_id() == inst.id(),
        src_place.instance_id() == inst.id(),
        frame.instance_id() == inst.id(),
        entry.instance_id() == inst.id(),
        certs.instance_id() == inst.id(),
        stale.key() == inst.pt_obj() + vp,
        src_place.key() == src_obj,
        src_place.value() == Some(pfn),
        frame.key() == pfn,
        entry.key() == vp,
        entry.value() is None,
        words.dom() =~= obj_ids::<S>(old(next).value()),
        src.map() =~= content_of::<S>(old(next).value(), words, src_obj),
        certs.map() =~= page_view::<S>(inst.vmem_dom(), vp, Option::<nat>::None),
    ensures
        r.0.value() == S::encode(Some(pfn)),
        r.1.map() =~= words,
        r.2.key() == old(next).value(),
        r.2.value() == Some(pfn),
        r.3.key() == pfn,
        r.3.value() =~= frame.value().insert(old(next).value()),
        r.4.key() == vp,
        r.4.value() == Some(old(next).value()),
        r.5.value() =~= Set::<nat>::empty().insert(vp),
        r.6.map() =~= mapped_view::<S>(inst.vmem_dom(), vp, old(next).value()),
        final(next).value() == old(next).value() + S::size(),
{
    let tracked res = inst.fork(
        vp,
        pfn,
        src_obj,
        words,
        stale,
        src,
        src_place,
        frame,
        next,
        entry,
        certs,
    );
    (
        res.0.get(),
        res.1.get(),
        res.2.get(),
        res.3.get(),
        res.4.get(),
        res.5.get(),
        res.6.get(),
    )
}

/// Move content to a frame of its own, having copied its words there, and rewrite every page
/// table entry that named the old frame. Nothing about the *mapping* changes -- no certificate
/// and no permission is consumed or produced -- but the entries must change, because they name
/// frames and the frame has changed. That obligation is what the walk invariant buys.
///
/// Run on the sole resident of a frame this is a **page swap**; run on one of several residents
/// it is the copy half of **copy-on-write**, and the caller comes back sole resident and so able
/// to write.
pub proof fn relocate_content<S: PageSizeSpec>(
    tracked inst: &Mem::Instance<S>,
    obj: nat,
    pfn: nat,
    words: Map<nat, usize>,
    tracked stale: PageData<S>,
    tracked content: &PageData<S>,
    tracked mapped_at: &Mem::obj_to_vpages<S>,
    tracked at: Mem::obj_to_frame<S>,
    tracked from: Mem::frame_to_objs<S>,
    tracked to: Mem::frame_to_objs<S>,
) -> (tracked r: (PageData<S>, Mem::obj_to_frame<S>, Mem::frame_to_objs<S>, Mem::frame_to_objs<S>))
    requires
        stale.instance_id() == inst.id(),
        content.instance_id() == inst.id(),
        mapped_at.instance_id() == inst.id(),
        at.instance_id() == inst.id(),
        from.instance_id() == inst.id(),
        to.instance_id() == inst.id(),
        obj != inst.pt_obj(),
        at.key() == obj,
        at.value() == Some(from.key()),
        mapped_at.key() == obj,
        stale.map() =~= entry_words::<S>(inst.pt_obj(), mapped_at.value(), at.value()),
        from.key() != pfn,
        to.key() == pfn,
        to.value() =~= Set::<nat>::empty(),
        words.dom() =~= obj_ids::<S>(obj),
        content.map() =~= words,
    ensures
        r.0.map() =~= entry_words::<S>(inst.pt_obj(), mapped_at.value(), Some(pfn)),
        r.1.key() == obj,
        r.1.value() == Some(pfn),
        r.2.key() == from.key(),
        r.2.value() =~= from.value().remove(obj),
        r.3.key() == pfn,
        r.3.value() =~= Set::<nat>::empty().insert(obj),
{
    let tracked res = inst.relocate(obj, pfn, words, stale, content, at, from, to, mapped_at);
    (res.0.get(), res.1.get(), res.2.get(), res.3.get())
}

/// Remove a mapping. Every certificate the page issued must come back, so no permission can
/// survive the mapping that justified it -- which is exactly why `detach` exists.
pub proof fn unmap_page<S: PageSizeSpec>(
    tracked inst: &Mem::Instance<S>,
    vp: nat,
    tracked stale: Mem::data<S>,
    tracked entry: Mem::vmap<S>,
    tracked vpages: Mem::obj_to_vpages<S>,
    tracked certs: PageCerts<S>,
) -> (tracked r: (Mem::data<S>, Mem::vmap<S>, Mem::obj_to_vpages<S>, PageCerts<S>))
    requires
        stale.instance_id() == inst.id(),
        entry.instance_id() == inst.id(),
        vpages.instance_id() == inst.id(),
        certs.instance_id() == inst.id(),
        stale.key() == inst.pt_obj() + vp,
        entry.key() == vp,
        entry.value() is Some,
        vpages.key() == entry.value()->Some_0,
        certs.map() =~= mapped_view::<S>(inst.vmem_dom(), vp, entry.value()->Some_0),
    ensures
        r.0.key() == inst.pt_obj() + vp,
        r.0.value() == S::encode(Option::<nat>::None),
        r.1.instance_id() == inst.id(),
        r.1.key() == vp,
        r.1.value() is None,
        r.2.instance_id() == inst.id(),
        r.2.key() == vpages.key(),
        r.2.value() =~= vpages.value().remove(vp),
        r.3.instance_id() == inst.id(),
        r.3.map() =~= page_view::<S>(inst.vmem_dom(), vp, Option::<nat>::None),
{
    let tracked res = inst.unmap(vp, stale, entry, vpages, certs);
    (res.0.get(), res.1.get(), res.2.get(), res.3.get())
}

/// Write through an exclusive permission. `obj_to_frame` and `frame_to_objs` witness that no other content
/// shares the frame -- so a page still sharing a frame after a fork must relocate first. No page
/// table entry is consulted, so a concurrent remap cannot block a write.
pub proof fn write_word<S: PageSizeSpec>(
    tracked inst: &Mem::Instance<S>,
    val: usize,
    tracked perm: VirtPointsTo<S>,
    tracked at: &Mem::obj_to_frame<S>,
    tracked frame: &Mem::frame_to_objs<S>,
) -> (tracked r: VirtPointsTo<S>)
    requires
        perm.wf(),
        perm.instance_id() == inst.id(),
        at.instance_id() == inst.id(),
        frame.instance_id() == inst.id(),
        at.key() == obj_of::<S>(perm.oid(), perm.addr()),
        at.value() == Some(frame.key()),
        frame.value() =~= Set::<nat>::empty().insert(at.key()),
    ensures
        r.wf(),
        r.addr() == perm.addr(),
        r.oid() == perm.oid(),
        r.value() == val,
        r.instance_id() == perm.instance_id(),
{
    let tracked VirtPointsTo { cert, content } = perm;
    let tracked content = inst.write_non_pt(cert.key(), val, content, at, frame, &cert);
    VirtPointsTo { cert, content }
}

/// Give up the right to write in exchange for the right to share. An exclusive permission
/// becomes a shared one, and from then on any number of addresses may hold a copy.
pub proof fn freeze_word<S: PageSizeSpec>(
    tracked inst: &Mem::Instance<S>,
    tracked perm: VirtPointsTo<S>,
) -> (tracked r: SharedVirtPointsTo<S>)
    requires
        perm.wf(),
        perm.instance_id() == inst.id(),
    ensures
        r.wf(),
        r.addr() == perm.addr(),
        r.oid() == perm.oid(),
        r.value() == perm.value(),
{
    let tracked VirtPointsTo { cert, content } = perm;
    let tracked content = inst.freeze(content.key(), content);
    SharedVirtPointsTo { cert, content }
}

/// A **pinned** permission: an exclusive permission that additionally knows, and holds fixed,
/// the frame its content sits in. Three tokens: the certificate saying which content the address
/// reaches, the content itself, and `obj_to_frame` and `frame_to_objs` saying where that content physically is
/// and that nothing else is there.
///
/// Holding `obj_to_frame` *by value* is what does the pinning. `relocate` consumes that token, so while
/// this permission exists nobody can move the content -- the translation `addr() -> pfn()` is
/// stable, not merely true at the moment it was read.
///
/// That is what hardware needs. CR3 and every page table entry name a frame number, and the
/// walker follows it without consulting anything this model can revoke; meanwhile software must
/// reach the same page through some virtual mapping to edit it. A pinned permission is exactly
/// the conjunction of the two: `addr()` is how software reaches the page, `pfn()` is what goes
/// in the register, and they are guaranteed to name the same words for as long as it is held.
pub tracked struct PinnedPointsTo<S: PageSizeSpec> {
    pub tracked perm: VirtPointsTo<S>,
    pub tracked at: Mem::obj_to_frame<S>,
    pub tracked frame: Mem::frame_to_objs<S>,
}

impl<S: PageSizeSpec> PinnedPointsTo<S> {
    pub open spec fn instance_id(self) -> vstd::tokens::InstanceId {
        self.perm.instance_id()
    }

    pub open spec fn addr(self) -> nat {
        self.perm.addr()
    }

    pub open spec fn oid(self) -> nat {
        self.perm.oid()
    }

    pub open spec fn value(self) -> usize {
        self.perm.value()
    }

    /// The frame the address translates to. Known, and fixed for as long as this is held.
    pub open spec fn pfn(self) -> nat {
        self.frame.key()
    }

    pub open spec fn obj(self) -> nat {
        self.at.key()
    }

    pub open spec fn wf(self) -> bool {
        &&& self.perm.wf()
        &&& self.at.instance_id() == self.perm.instance_id()
        &&& self.frame.instance_id() == self.perm.instance_id()
        &&& self.obj() == obj_of::<S>(self.oid(), self.addr())
        &&& self.at.value() == Some(self.pfn())
        &&& self.frame.value() =~= Set::<nat>::empty().insert(self.obj())
    }
}

/// Pin an exclusive permission to the frame it currently sits in, by taking custody of the
/// placement. The caller must already be the frame's sole resident -- content still shared after a
/// fork has to be relocated before it can be pinned, which is right: a page table page cannot
/// share a frame with content that is about to diverge from it.
///
/// Pinning fixes the *placement*, not the mapping. Other pages may still be pointed at this
/// content while it is pinned (see `access_pinned`), and they gain no right to write it, because
/// the `data` token stays here.
pub proof fn pin<S: PageSizeSpec>(
    tracked perm: VirtPointsTo<S>,
    tracked at: Mem::obj_to_frame<S>,
    tracked frame: Mem::frame_to_objs<S>,
) -> (tracked pinned: PinnedPointsTo<S>)
    requires
        perm.wf(),
        at.instance_id() == perm.instance_id(),
        frame.instance_id() == perm.instance_id(),
        at.key() == obj_of::<S>(perm.oid(), perm.addr()),
        at.value() == Some(frame.key()),
        frame.value() =~= Set::<nat>::empty().insert(at.key()),
    ensures
        pinned.wf(),
        pinned.addr() == perm.addr(),
        pinned.oid() == perm.oid(),
        pinned.value() == perm.value(),
        pinned.pfn() == frame.key(),
{
    PinnedPointsTo { perm, at, frame }
}

/// Give the placement back, which is what makes the content relocatable again. Anything that
/// depends on the translation -- a live CR3, an installed page table entry -- must be torn down
/// before this, since afterwards nothing stops the content moving.
pub proof fn unpin<S: PageSizeSpec>(tracked pinned: PinnedPointsTo<S>) -> (tracked r: (
    VirtPointsTo<S>,
    Mem::obj_to_frame<S>,
    Mem::frame_to_objs<S>,
))
    ensures
        r.0 == pinned.perm,
        r.1 == pinned.at,
        r.2 == pinned.frame,
{
    let tracked PinnedPointsTo { perm, at, frame } = pinned;
    (perm, at, frame)
}

/// Write through a pinned permission. It needs no extra arguments: the sole-user witness a write
/// demands is already inside. This is how a page table page is edited -- through its virtual
/// address, while the hardware reads the same words through `pfn()`.
pub proof fn write_pinned<S: PageSizeSpec>(
    tracked inst: &Mem::Instance<S>,
    val: usize,
    tracked pinned: PinnedPointsTo<S>,
) -> (tracked r: PinnedPointsTo<S>)
    requires
        pinned.wf(),
        pinned.instance_id() == inst.id(),
    ensures
        r.wf(),
        r.addr() == pinned.addr(),
        r.oid() == pinned.oid(),
        r.pfn() == pinned.pfn(),
        r.value() == val,
        r.instance_id() == pinned.instance_id(),
{
    let tracked PinnedPointsTo { perm, at, frame } = pinned;
    let tracked perm = write_word(inst, val, perm, &at, &frame);
    PinnedPointsTo { perm, at, frame }
}

/// Map a second page onto content that already exists, at some scratch address. Both pages then
/// carry certificates for the *same* ids, so this confers a way to reach the content, never a
/// right to write it -- the `data` token stays wherever it was.
pub proof fn share_page<S: PageSizeSpec>(
    tracked inst: &Mem::Instance<S>,
    vp: nat,
    obj: nat,
    tracked at: &Mem::obj_to_frame<S>,
    tracked stale: Mem::data<S>,
    tracked entry: Mem::vmap<S>,
    tracked vpages: Mem::obj_to_vpages<S>,
    tracked certs: PageCerts<S>,
) -> (tracked r: (Mem::data<S>, Mem::vmap<S>, Mem::obj_to_vpages<S>, PageCerts<S>))
    requires
        at.instance_id() == inst.id(),
        stale.instance_id() == inst.id(),
        entry.instance_id() == inst.id(),
        vpages.instance_id() == inst.id(),
        certs.instance_id() == inst.id(),
        at.key() == obj,
        at.value() is Some,
        stale.key() == inst.pt_obj() + vp,
        entry.key() == vp,
        entry.value() is None,
        vpages.key() == obj,
        certs.map() =~= page_view::<S>(inst.vmem_dom(), vp, Option::<nat>::None),
    ensures
        r.0.key() == inst.pt_obj() + vp,
        r.0.value() == S::encode(at.value()),
        r.1.instance_id() == inst.id(),
        r.1.key() == vp,
        r.1.value() == Some(obj),
        r.2.instance_id() == inst.id(),
        r.2.key() == obj,
        r.2.value() =~= vpages.value().insert(vp),
        r.3.instance_id() == inst.id(),
        r.3.map() =~= mapped_view::<S>(inst.vmem_dom(), vp, obj),
{
    let tracked res = inst.share(vp, obj, stale, at, entry, vpages, certs);
    (res.0.get(), res.1.get(), res.2.get(), res.3.get())
}

/// Reach a pinned page from a scratch address, on demand. This is how a page table page is
/// accessed without one having been mapped for it in advance: nothing about the page changes,
/// and in particular it stays pinned, because `obj_to_frame` is only borrowed.
///
/// So no page table page needs a standing mapping -- the mapping for one is installed by writing
/// an entry in its parent, which is reached the same way, and so on up.
///
/// The root is not an exception to this, and merely *using* it needs no mapping at all: the
/// walker reaches it physically from CR3, and a kernel that never edits its top level after boot
/// never maps it.
///
/// Changing page tables at runtime is a different matter, and it does not bottom out. Installing
/// a mapping means writing an entry in some page table page, which means that page must itself
/// be mapped, which means writing an entry in *its* governing page -- so the set of page table
/// pages that are reachable can never be grown from empty. It must be non-empty to begin with,
/// and closed: the page governing the scratch window has to be reachable through that same
/// window. The minimal arrangement is therefore self-referential, which is what a recursive
/// self-map is; a direct map of all physical memory is the same fixpoint reached bluntly. Either
/// is established before paging is enabled, where addresses are already physical and no entry
/// has to be reachable to be written.
///
/// In this model that base case is the initial distribution of `vmap` tokens. `boot` hands them
/// out, and holding one is what lets a mapping be installed with no earlier mapping to stand on.
/// What the model does *not* yet capture is why that is legitimate -- that would need page table
/// pages to be ordinary content, so that installing a mapping and writing a word were the same
/// act rather than two unrelated fields.
pub proof fn access_pinned<S: PageSizeSpec>(
    tracked inst: &Mem::Instance<S>,
    vp: nat,
    tracked pinned: &PinnedPointsTo<S>,
    tracked stale: Mem::data<S>,
    tracked entry: Mem::vmap<S>,
    tracked vpages: Mem::obj_to_vpages<S>,
    tracked certs: PageCerts<S>,
) -> (tracked r: (Mem::data<S>, Mem::vmap<S>, Mem::obj_to_vpages<S>, PageCerts<S>))
    requires
        pinned.wf(),
        pinned.instance_id() == inst.id(),
        stale.instance_id() == inst.id(),
        entry.instance_id() == inst.id(),
        vpages.instance_id() == inst.id(),
        certs.instance_id() == inst.id(),
        stale.key() == inst.pt_obj() + vp,
        entry.key() == vp,
        entry.value() is None,
        vpages.key() == pinned.obj(),
        certs.map() =~= page_view::<S>(inst.vmem_dom(), vp, Option::<nat>::None),
    ensures
        r.0.value() == S::encode(Some(pinned.pfn())),
        r.1.key() == vp,
        r.1.value() == Some(pinned.obj()),
        r.2.value() =~= vpages.value().insert(vp),
        r.3.map() =~= mapped_view::<S>(inst.vmem_dom(), vp, pinned.obj()),
{
    share_page(inst, vp, pinned.obj(), &pinned.at, stale, entry, vpages, certs)
}

} // verus!
