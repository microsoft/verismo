//! A page-table entry that publishes nothing: no ticket API, and a payload the writer may swap
//! at any moment. A walk descends anyway, on `reachable` alone, which pins the parent's
//! `next()`, the payload's provenance, and each child reader's `obs_id`. The cost is one nested
//! invariant per level. `pt` is the same client with publishing on, and its walk recurses.

use concurrent_rw::*;
use vstd::atomic::PAtomicUsize;
use vstd::invariant::{create_open_invariant_credit, OpenInvariantCredit};
#[cfg(verus_only)]
use vstd::invariant::InvariantPredicate;
#[cfg(verus_only)]
use vstd::open_atomic_invariant_in_proof;
use vstd::open_atomic_invariant;
use vstd::iset::ISet;
#[cfg(verus_only)]
use vstd::iset::iset;
use vstd::prelude::*;
use vstd::raw_ptr::IsExposed;
#[cfg(verus_only)]
use vstd::std_specs::convert::{FromSpec, FromSpecImpl, IntoSpec};

verus! {

pub struct PTEntry {
    pub value: usize,
}

impl From<usize> for PTEntry {
    fn from(value: usize) -> Self {
        PTEntry { value }
    }
}

impl From<PTEntry> for usize {
    fn from(entry: PTEntry) -> Self {
        entry.value
    }
}

#[cfg(verus_only)]
impl FromSpecImpl<usize> for PTEntry {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(v: usize) -> PTEntry {
        PTEntry { value: v }
    }
}

#[cfg(verus_only)]
impl FromSpecImpl<PTEntry> for usize {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(v: PTEntry) -> usize {
        v.value
    }
}

impl PTEntry {
    pub open spec fn inv(self) -> bool {
        true
    }

    pub open spec fn present_spec(&self) -> bool {
        self.value != 0
    }

    #[verifier::when_used_as_spec(present_spec)]
    pub fn present(&self) -> bool
    returns
        self.present()
    {
        self.value != 0
    }

    pub open spec fn next_spec(&self) -> usize {
        self.value
    }

    #[verifier::when_used_as_spec(next_spec)]
    pub fn next(&self) -> usize
    returns
        self.next()
    {
        self.value
    }
}

pub struct Extra {
    reader: Seq<Reader<PTEntry, Extra>>,
    provenance: IsExposed,
}

impl WithPayload for PTEntry {
    type Payload = Extra;

    closed spec fn wf_payload(self, payload: Self::Payload) -> bool {
        self.present() ==> {
            &&& payload.reader.len() == 512
            &&& forall|i: int|
                ((#[trigger] payload.reader[i]).ptr().addr() == self.next() + i * 8)
                && payload.reader[i].ptr()@.provenance == payload.provenance@
        }
    }
}

impl IsValidAtomicType for PTEntry {
    type AtomicType = usize;
}

impl RWModel for PTEntry {
    proof fn into_from_obeys() where Self: From<Self::AtomicType> + Into<Self::AtomicType>
    {
    }

    proof fn into_from_atomic_agree(self) where
        Self: From<Self::AtomicType> + Into<Self::AtomicType>,
    {
    }

    /// A present entry keeps pointing at the same child table, which pins two things about the
    /// payload that `wf_payload` cannot: the child page's provenance, and each child reader's
    /// `obs_id`, without which an `Observed` taken on a child would be useless in the next
    /// block. Both are properties of the payload that was there, not functions of the value.
    closed spec fn reachable(pair: Snapshot<Self, Self::Payload>, other: Snapshot<
        Self,
        Self::Payload,
    >) -> bool {
        pair.value().present() ==> {
            &&& other.value().present()
            &&& pair.value().next() == other.value().next()
            &&& other.payload().provenance@ == pair.payload().provenance@
            &&& forall|i: int|
                (#[trigger] other.payload().reader[i]).obs_id()
                    == pair.payload().reader[i].obs_id() &&
                 (#[trigger] other.payload().reader[i]).namespace()
                    == pair.payload().reader[i].namespace()
        }
    }

    proof fn reachable_self(pair: Snapshot<Self, Self::Payload>) {
    }

    proof fn reachable_transitive(a: Snapshot<Self, Self::Payload>, b: Snapshot<
        Self,
        Self::Payload,
    >, c: Snapshot<Self, Self::Payload>) {
    }

    
}

// The innermost block of every pass, at every depth: read the entry and take what the next pass
// needs. `#[verifier::atomic]` is what makes it a function at all -- an `open_atomic_invariant!`
// body must be a single atomic operation, and this performs exactly one.
#[verifier::atomic]
fn read_entry(
    ptr: *mut usize,
    Tracked(reader): Tracked<&Reader<PTEntry, Extra>>,
    Tracked(state): Tracked<&mut ReaderState<PTEntry, Extra>>,
) -> (out: (usize, Tracked<Observed<PTEntry>>, Tracked<IsExposed>))
    requires
        old(state).inv(),
        old(state).constant() == reader.constant(),
        ptr == reader.ptr(),
    ensures
        final(state).inv(),
        final(state).constant() == old(state).constant(),
        final(state).value() == old(state).value(),
        old(state).constant().has_observed(out.1@),
        out.1@.snapshot() == final(state).current_snapshot(),
        final(state).value() === out.0.into_spec(),
        out.2@@ == final(state).payload_value().provenance@,
    opens_invariants none
    no_unwind
{
    proof {
        state.lemma_inv_perm(reader);
    }
    let v = PAtomicUsize::from_ptr_load(ptr, Tracked(&state.perm));
    let tracked observed;
    let tracked provenance;
    proof {
        observed = state.observe();
        let tracked payload = state.borrow_payload(state.constant());
        provenance = payload.provenance;
    }
    (v, Tracked(observed), Tracked(provenance))
}

// One pass per function, indexed by how deep it reads, each taking the observations already
// gathered above it -- one per level, since it reopens every one of those invariants on the way
// down. Each opens its root and hands the rest to the pass one level shallower, so only the
// descent step repeats. Handing off needs the deeper namespaces to differ from the root, which
// each pass gets from a lemma before it opens anything.

// A reader already open cannot be the child about to be opened: each holds a whole fraction at
// its own location, and two whole fractions do not compose. Getting that takes a `&mut` to the
// child, so the payload is lent out and put back untouched, which leaves the state as it was.
proof fn child_namespace_differs(
    tracked state: &mut ReaderState<PTEntry, Extra>,
    c: ReaderConstant<PTEntry>,
    tracked open: &Reader<PTEntry, Extra>,
)
    requires
        <ReaderState<PTEntry, Extra> as InvariantPredicate<
            ReaderConstant<PTEntry>,
            ReaderState<PTEntry, Extra>,
        >>::inv(c, *old(state)),
        !old(state).value().has_published_payload(),
        old(state).value().present(),
    ensures
        *final(state) == *old(state),
        final(state).payload_value().reader[0].namespace() != open.namespace(),
{
    let tracked payload = state.borrow_payload_mut(c);
    let payload_old = *payload;
    payload.reader.tracked_borrow_mut(0).distinct_namespace(open);
    assert(payload_old.reader == payload.reader);
}

proof fn namespaces_differ(
    tracked r: &Reader<PTEntry, Extra>,
    tracked o1: &Observed<PTEntry>,
    tracked credit: OpenInvariantCredit,
)
    requires
        r.has_observed(*o1),
        o1.value().present(),
    ensures
        o1.payload().reader[0].namespace() != r.namespace(),
    opens_invariants
        [r.namespace()],
{
    let tracked atom = r.borrow_atom();
    open_atomic_invariant_in_proof!(credit => atom => state => {
        state.read_with_observed(o1);
        child_namespace_differs(&mut state, atom.constant(), r);
    });
}
proof fn namespaces_differ2(
    tracked r: &Reader<PTEntry, Extra>,
    tracked o1: &Observed<PTEntry>,
    tracked o2: &Observed<PTEntry>,
    tracked c1: OpenInvariantCredit,
    tracked c2: OpenInvariantCredit,
)
    requires
        r.has_observed(*o1),
        o1.value().present(),
        o2.id() == o1.payload().reader[0].obs_id(),
        o2.value().present(),
    ensures
        o1.payload().reader[0].namespace() != r.namespace(),
        o2.payload().reader[0].namespace() != r.namespace(),
        o2.payload().reader[0].namespace() != o1.payload().reader[0].namespace(),
    opens_invariants
        [r.namespace(), o1.payload().reader[0].namespace()],
{
    let tracked atom0 = r.borrow_atom();
    open_atomic_invariant_in_proof!(c1 => atom0 => state0 => {
        state0.read_with_observed(o1);
        child_namespace_differs(&mut state0, atom0.constant(), r);
        let tracked payload0 = state0.borrow_payload(atom0.constant());
        let tracked reader1 = payload0.reader.tracked_borrow(0);
        let tracked atom1 = reader1.borrow_atom();
        open_atomic_invariant_in_proof!(c2 => atom1 => state1 => {
            state1.lemma_inv_perm(reader1);
            state1.read_with_observed(o2);
            child_namespace_differs(&mut state1, atom1.constant(), r);
            child_namespace_differs(&mut state1, atom1.constant(), reader1);
        });
    });
}

// Every child in the chain differs from `root`, for a chain of any length. Descends one level
// per call, opening the level it is at: proving the child at depth k differs takes the whole
// nest of opens above it, so the recursion has to go down, not shorten from the end.
//
// `opened` is the ancestors whose invariants this call is already inside, and the mask is
// everything but those. That is what lets the nested call typecheck: it opens all but
// `opened + cur`, which is exactly what is left of this mask once `cur` is open.
proof fn namespaces_differ_r_namespace<'a>(
    tracked root: &Reader<PTEntry, Extra>,
    tracked cur: &'a Reader<PTEntry, Extra>,
    tracked opened: Seq<&'a Reader<PTEntry, Extra>>,
    tracked observed: &Seq<&'a Observed<PTEntry>>,
    tracked credits: Seq<OpenInvariantCredit>,
    k: nat,
)
    requires
        k < observed.len(),
        credits.len() + k >= observed.len(),
        cur.has_observed(*observed[k as int]),
        observed[k as int].value().present(),
        forall|i: int|
            k <= i < observed.len() - 1 ==> (#[trigger] observed[i + 1]).id()
                == observed[i].payload().reader[0].obs_id() && observed[i + 1].value().present(),
        !open_namespaces(opened).contains(cur.namespace()),
        opened.len() == k,
        k == 0 ==> cur.namespace() == root.namespace(),
        k > 0 ==> cur.namespace() == observed[k - 1].payload().reader[0].namespace(),
        opened.len() > 0 ==> opened[0].namespace() == root.namespace(),
        forall|j: int|
            1 <= j < k ==> (#[trigger] opened[j]).namespace()
                == observed[j - 1].payload().reader[0].namespace(),
    ensures
        forall|i: int|
            k <= i < observed.len() ==> (#[trigger] observed[i]).payload().reader[0].namespace()
                != root.namespace(),
        forall|i: int, j: int|
            #![trigger observed[i], observed[j]]
            k <= i < observed.len() && 0 <= j < i ==> observed[i].payload().reader[0].namespace()
                != observed[j].payload().reader[0].namespace(),
    decreases observed.len() - k,
    opens_invariants
        chain_namespaces(root, *observed).difference(open_namespaces(opened)),
{
    broadcast use vstd::iset::group_iset_lemmas;

    let tracked mut credits = credits;
    let tracked mut opened = opened;
    let tracked credit = credits.tracked_pop_front();
    // `cur` is a level this descent steps into, so its namespace is one the mask allows.
    let ghost front = observed.remove(observed.len() - 1);
    let ghost f = |o: &Observed<PTEntry>| o.payload().reader[0].namespace();
    assert(front =~= observed.subrange(0, observed.len() - 1));
    if k > 0 {
        assert(front.map_values(f)[k - 1] == cur.namespace());
        assert(front.map_values(f).to_iset().contains(cur.namespace()));
    }
    let tracked atom = cur.borrow_atom();
    open_atomic_invariant_in_proof!(credit => atom => state => {
        let tracked o = observed.tracked_borrow(k as int);
        state.read_with_observed(*o);
        child_namespace_differs(&mut state, atom.constant(), root);
        child_differs_from_all(&mut state, atom.constant(), &opened, opened.len());
        child_namespace_differs(&mut state, atom.constant(), cur);
        assert forall|j: int| 0 <= j < k implies o.payload().reader[0].namespace() != (
        #[trigger] observed[j]).payload().reader[0].namespace() by {
            if j < k - 1 {
                assert(opened[j + 1].namespace()
                    == observed[j].payload().reader[0].namespace());
            }
        }
        if k + 1 < observed.len() {
            let tracked payload = state.borrow_payload(atom.constant());
            let tracked reader1 = payload.reader.tracked_borrow(0);
            let ghost opened0 = opened;
            opened.tracked_push(cur);
            open_namespaces_push(opened0, cur);

            namespaces_differ_r_namespace(
                root,
                reader1,
                opened,
                observed,
                credits,
                (k + 1) as nat,
            );
        }
    });
}
// The children in the chain all have distinct namespaces, and none of them is the root's.
proof fn namespaces_differ_all(
    tracked r: &Reader<PTEntry, Extra>,
    tracked observed: &Seq<&Observed<PTEntry>>,
    tracked credits: Seq<OpenInvariantCredit>,
)
    requires
        observed.len() > 0,
        credits.len() >= observed.len(),
        r.has_observed(*observed[0]),
        observed[0].value().present(),
        forall|i: int|
            0 <= i < observed.len() - 1 ==> (#[trigger] observed[i + 1]).id()
                == observed[i].payload().reader[0].obs_id() && observed[i + 1].value().present(),
    ensures
        forall|i: int|
            0 <= i < observed.len() ==> (#[trigger] observed[i]).payload().reader[0].namespace()
                != r.namespace(),
        forall|i: int, j: int|
            #![trigger observed[i], observed[j]]
            0 <= j < i < observed.len() ==> observed[i].payload().reader[0].namespace()
                != observed[j].payload().reader[0].namespace(),
    opens_invariants
        chain_namespaces(r, *observed),
{
    broadcast use vstd::iset::group_iset_lemmas;

    let tracked opened: Seq<&Reader<PTEntry, Extra>> = Seq::tracked_empty();
    assert(open_namespaces(opened) =~= ISet::empty());
    namespaces_differ_r_namespace(r, r, opened, observed, credits, 0);
}

// One credit per invariant to be opened, since a descent spends one per level.
fn create_open_invariant_credits(n: usize) -> (out: Tracked<Seq<OpenInvariantCredit>>)
    ensures
        out@.len() == n,
    opens_invariants none
    no_unwind
{
    let tracked mut credits: Seq<OpenInvariantCredit> = Seq::tracked_empty();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            credits.len() == i,
        decreases n - i,
    {
        let c = create_open_invariant_credit();
        proof {
            credits.tracked_push(c.get());
        }
        i = i + 1;
    }
    Tracked(credits)
}

// The namespaces a descent from `root` opens: its own, and each level it steps into. The last
// reading is only looked at, never descended through, so its child is not among them.
spec fn chain_namespaces(
    root: &Reader<PTEntry, Extra>,
    observed: Seq<&Observed<PTEntry>>,
) -> ISet<int> {
    observed.remove(observed.len() - 1).map_values(
        |o: &Observed<PTEntry>| o.payload().reader[0].namespace(),
    ).to_iset().insert(root.namespace())
}

// The namespaces whose invariants are already open.
spec fn open_namespaces(opened: Seq<&Reader<PTEntry, Extra>>) -> ISet<int> {
    opened.map_values(|r: &Reader<PTEntry, Extra>| r.namespace()).to_iset()
}

// Pushing a reader onto `opened` adds exactly its namespace.
proof fn open_namespaces_push(opened: Seq<&Reader<PTEntry, Extra>>, r: &Reader<PTEntry, Extra>)
    ensures
        open_namespaces(opened.push(r)) =~= open_namespaces(opened).insert(r.namespace()),
{
    broadcast use vstd::seq::Seq::lemma_to_iset_insert_commutes;

    let f = |r: &Reader<PTEntry, Extra>| r.namespace();
    assert(opened.push(r).map_values(f) =~= opened.map_values(f) + seq![r.namespace()]);
}

// The child differs from every reader already open: one `distinct_namespace` per ancestor.
proof fn child_differs_from_all(
    tracked state: &mut ReaderState<PTEntry, Extra>,
    c: ReaderConstant<PTEntry>,
    tracked opened: &Seq<&Reader<PTEntry, Extra>>,
    n: nat,
)
    requires
        <ReaderState<PTEntry, Extra> as InvariantPredicate<
            ReaderConstant<PTEntry>,
            ReaderState<PTEntry, Extra>,
        >>::inv(c, *old(state)),
        !old(state).value().has_published_payload(),
        old(state).value().present(),
        n <= opened.len(),
    ensures
        *final(state) == *old(state),
        forall|j: int|
            0 <= j < n ==> final(state).payload_value().reader[0].namespace() != (
            #[trigger] opened[j]).namespace(),
    decreases n,
{
    if n > 0 {
        let tracked prev = opened.tracked_borrow(n - 1);
        child_namespace_differs(state, c, *prev);
        child_differs_from_all(state, c, opened, (n - 1) as nat);
    }
}

// The root. Provenance is the point: the child table lives at `next()`, but an address is not
// a pointer, and rebuilding one is not atomic so it cannot happen inside the block.
#[verifier::atomic]
fn read_level0(
    ptr_lvl0: *mut usize,
    Tracked(r): Tracked<&Reader<PTEntry, Extra>>,
) -> (out: (usize, Tracked<Observed<PTEntry>>, Tracked<IsExposed>))
    requires
        r.ptr() == ptr_lvl0,
    ensures
        r.has_observed(out.1@),
        out.1@.value() === out.0.into_spec(),
        out.2@@ == out.1@.payload().provenance@,
    opens_invariants 
        [r.namespace()],
    no_unwind
{
    let tracked atom_lvl0 = r.borrow_atom();
    let value: usize;
    let tracked observed;
    let tracked provenance;
    open_atomic_invariant!(atom_lvl0 => state_lvl0 => {
        let (v, Tracked(o), Tracked(pv)) =
            read_entry(ptr_lvl0, Tracked(r), Tracked(&mut state_lvl0));
        value = v;
        proof {
            observed = o;
            provenance = pv;
        }
    });
    (value, Tracked(observed), Tracked(provenance))
}

// Two blocks deep: the root's, so level 1's reader is reachable, and level 1's -- opened by
// `read_level0` -- so its permission is.
#[verifier::atomic]
fn read_level1(
    ptr_lvl1: *mut usize,
    Tracked(r): Tracked<&Reader<PTEntry, Extra>>,
    Tracked(o1): Tracked<&Observed<PTEntry>>,
) -> (out: (usize, Tracked<Observed<PTEntry>>, Tracked<IsExposed>))
    requires
        r.has_observed(*o1),
        o1.value().present(),
        ptr_lvl1@.addr == o1.value().next(),
        ptr_lvl1@.provenance == o1.payload().provenance@,
    ensures
        out.1@.id() == o1.payload().reader[0].obs_id(),
        out.1@.value() === out.0.into_spec(),
        out.2@@ == out.1@.payload().provenance@,
    opens_invariants 
        [r.namespace(), o1.payload().reader[0].namespace()],
    no_unwind
{
    let tracked atom_lvl0 = r.borrow_atom();
    let ret;
    open_atomic_invariant!(atom_lvl0 => state_lvl0 => {
        let tracked payload_lvl0;
        proof {
            state_lvl0.read_with_observed(o1);
            child_namespace_differs(&mut state_lvl0, atom_lvl0.constant(), r);
            payload_lvl0 = state_lvl0.borrow_payload(atom_lvl0.constant());
        }
        let tracked reader_lvl1 = payload_lvl0.reader.tracked_borrow(0);
        ret = read_level0(ptr_lvl1, Tracked(reader_lvl1));
    });
    ret
}

// Three blocks deep. `o2` is what makes it possible: it says level 1 still points where it did
// when `read_level1` saw it, so `ptr_lvl2`, built from that reading, is still the right pointer.
#[verifier::atomic]
fn read_level2(
    ptr_lvl2: *mut usize,
    Tracked(r): Tracked<&Reader<PTEntry, Extra>>,
    Tracked(o1): Tracked<&Observed<PTEntry>>,
    Tracked(o2): Tracked<&Observed<PTEntry>>,
) -> (out: (usize, Tracked<Observed<PTEntry>>, Tracked<IsExposed>))
    requires
        r.has_observed(*o1),
        o1.value().present(),
        o2.id() == o1.payload().reader[0].obs_id(),
        o2.value().present(),
        ptr_lvl2@.addr == o2.value().next(),
        ptr_lvl2@.provenance == o2.payload().provenance@,
    ensures
        out.1@.id() == o2.payload().reader[0].obs_id(),
        out.1@.value() === out.0.into_spec(),
        out.2@@ == out.1@.payload().provenance@,
    opens_invariants 
        [r.namespace(), o1.payload().reader[0].namespace(), o2.payload().reader[0].namespace()],
    no_unwind
{
    let c1 = create_open_invariant_credit();
    let c2 = create_open_invariant_credit();
    proof {
        namespaces_differ2(r, o1, o2, c1.get(), c2.get());
    }
    let tracked atom_lvl0 = r.borrow_atom();
    let ret;
    open_atomic_invariant!(atom_lvl0 => state_lvl0 => {
        let tracked payload_lvl0;
        proof {
            state_lvl0.read_with_observed(o1);
            payload_lvl0 = state_lvl0.borrow_payload(atom_lvl0.constant());
        }
        let tracked reader_lvl1 = payload_lvl0.reader.tracked_borrow(0);
        ret = read_level1(ptr_lvl2, Tracked(reader_lvl1), Tracked(o2));
    });
    ret
}

// Four blocks deep, but it opens only the root and hands the rest to `read_level2`. That call
// is allowed exactly when the two deeper children differ from the root, which
// `namespaces_differ_all` establishes first, from outside every block.
#[verifier::atomic]
fn read_level3(
    ptr_lvl3: *mut usize,
    Tracked(r): Tracked<&Reader<PTEntry, Extra>>,
    Tracked(o1): Tracked<&Observed<PTEntry>>,
    Tracked(o2): Tracked<&Observed<PTEntry>>,
    Tracked(o3): Tracked<&Observed<PTEntry>>,
) -> (out: (usize, Tracked<Observed<PTEntry>>, Tracked<IsExposed>))
    requires
        r.has_observed(*o1),
        o1.value().present(),
        o2.id() == o1.payload().reader[0].obs_id(),
        o2.value().present(),
        o3.id() == o2.payload().reader[0].obs_id(),
        o3.value().present(),
        ptr_lvl3@.addr == o3.value().next(),
        ptr_lvl3@.provenance == o3.payload().provenance@,
    ensures
        out.1@.id() == o3.payload().reader[0].obs_id(),
        out.1@.value() === out.0.into_spec(),
        out.2@@ == out.1@.payload().provenance@,
    opens_invariants
        [
            r.namespace(),
            o1.payload().reader[0].namespace(),
            o2.payload().reader[0].namespace(),
            o3.payload().reader[0].namespace(),
        ],
    no_unwind
{
    let c1 = create_open_invariant_credit();
    let c2 = create_open_invariant_credit();
    let c3 = create_open_invariant_credit();
    proof {
        let tracked mut observed: Seq<&Observed<PTEntry>> = Seq::tracked_empty();
        observed.tracked_push(o1);
        observed.tracked_push(o2);
        observed.tracked_push(o3);
        let tracked mut credits: Seq<OpenInvariantCredit> = Seq::tracked_empty();
        credits.tracked_push(c1.get());
        credits.tracked_push(c2.get());
        credits.tracked_push(c3.get());
        namespaces_differ_all(r, &observed, credits);
        // The lemma speaks of the sequence; the pass speaks of the readings.
        assert(observed[1] == o2);
        assert(observed[2] == o3);
    }
    let tracked atom_lvl0 = r.borrow_atom();
    let ret;
    open_atomic_invariant!(atom_lvl0 => state_lvl0 => {
        let tracked payload_lvl0;
        proof {
            state_lvl0.read_with_observed(o1);
            payload_lvl0 = state_lvl0.borrow_payload(atom_lvl0.constant());
        }
        let tracked reader_lvl1 = payload_lvl0.reader.tracked_borrow(0);
        ret = read_level2(ptr_lvl3, Tracked(reader_lvl1), Tracked(o2), Tracked(o3));
    });
    ret
}

// What one pass opens: its root's namespace, and its child's at every level it descends. Unlike
// `chain_namespaces` this includes the deepest child, because the pass ends by reading it.
spec fn level_namespaces(
    r: &Reader<PTEntry, Extra>,
    observed: Seq<&Observed<PTEntry>>,
) -> ISet<int> {
    ISet::new(
        |n: int|
            n == r.namespace() || exists|j: int|
                0 <= j < observed.len() && (#[trigger] observed[j]).payload().reader[0].namespace()
                    == n,
    )
}

// Dropping the first level leaves its child's namespace, which the next pass opens as its root.
proof fn level_namespaces_pop_front(
    r: &Reader<PTEntry, Extra>,
    child: &Reader<PTEntry, Extra>,
    observed: Seq<&Observed<PTEntry>>,
)
    requires
        observed.len() > 0,
        child.namespace() == observed[0].payload().reader[0].namespace(),
        forall|j: int|
            0 <= j < observed.len() ==> (#[trigger] observed[j]).payload().reader[0].namespace()
                != r.namespace(),
    ensures
        level_namespaces(child, observed.drop_first()) =~= level_namespaces(r, observed).remove(
            r.namespace(),
        ),
{
    broadcast use vstd::iset::group_iset_lemmas;

    let tail = observed.drop_first();
    assert forall|n: int| #[trigger] level_namespaces(child, tail).contains(n) implies
        level_namespaces(r, observed).remove(r.namespace()).contains(n) by {
        if n == child.namespace() {
            assert(observed[0].payload().reader[0].namespace() == n);
        } else {
            let j = choose|j: int|
                0 <= j < tail.len() && (#[trigger] tail[j]).payload().reader[0].namespace() == n;
            assert(observed[j + 1].payload().reader[0].namespace() == n);
        }
    }
    assert forall|n: int| #[trigger] level_namespaces(r, observed).remove(r.namespace()).contains(n)
        implies level_namespaces(child, tail).contains(n) by {
        let j = choose|j: int|
            0 <= j < observed.len() && (#[trigger] observed[j]).payload().reader[0].namespace()
                == n;
        if j > 0 {
            assert(tail[j - 1].payload().reader[0].namespace() == n);
        }
    }
}

// `observed` records a descent from `r`, one reading per level, each level present.
spec fn chain_from(r: &Reader<PTEntry, Extra>, observed: Seq<&Observed<PTEntry>>) -> bool {
    &&& observed.len() > 0 ==> r.has_observed(*observed[0]) && observed[0].value().present()
    &&& forall|i: int|
        0 <= i < observed.len() - 1 ==> (#[trigger] observed[i + 1]).id()
            == observed[i].payload().reader[0].obs_id() && observed[i + 1].value().present()
}

// No two levels of the descent share a namespace, so each can be opened inside the last.
spec fn chain_namespaces_distinct(
    r: &Reader<PTEntry, Extra>,
    observed: Seq<&Observed<PTEntry>>,
) -> bool {
    &&& forall|i: int|
        0 <= i < observed.len() ==> (#[trigger] observed[i]).payload().reader[0].namespace()
            != r.namespace()
    &&& forall|i: int, j: int|
        #![trigger observed[i], observed[j]]
        0 <= j < i < observed.len() ==> observed[i].payload().reader[0].namespace()
            != observed[j].payload().reader[0].namespace()
}

// The same pass with its mask handed in as a set instead of spelled out, which is what a caller
// that carries its own mask around needs. `ISet` is the type `opens_invariants` expects.
#[verifier::atomic]
fn read_level_3(
    ptr_lvl3: *mut usize,
    Tracked(r): Tracked<&Reader<PTEntry, Extra>>,
    Tracked(o1): Tracked<&Observed<PTEntry>>,
    Tracked(o2): Tracked<&Observed<PTEntry>>,
    Tracked(o3): Tracked<&Observed<PTEntry>>,
    Ghost(ns): Ghost<ISet<int>>,
) -> (out: (usize, Tracked<Observed<PTEntry>>, Tracked<IsExposed>))
    requires
        ns === iset![
            r.namespace(),
            o1.payload().reader[0].namespace(),
            o2.payload().reader[0].namespace(),
            o3.payload().reader[0].namespace(),
        ],
        r.has_observed(*o1),
        o1.value().present(),
        o2.id() == o1.payload().reader[0].obs_id(),
        o2.value().present(),
        o3.id() == o2.payload().reader[0].obs_id(),
        o3.value().present(),
        ptr_lvl3@.addr == o3.value().next(),
        ptr_lvl3@.provenance == o3.payload().provenance@,
    ensures
        out.1@.id() == o3.payload().reader[0].obs_id(),
        out.1@.value() === out.0.into_spec(),
        out.2@@ == out.1@.payload().provenance@,
    opens_invariants
        ns,
    no_unwind
{
    read_level3(ptr_lvl3, Tracked(r), Tracked(o1), Tracked(o2), Tracked(o3))
}

// Depth 2: read a grandchild. Three passes, each one level deeper, because rebuilding a pointer
// is not atomic, so a level is reached only by restarting from the root and descending further.
fn walk_level2(ptr_lvl0: *mut usize, Tracked(r): Tracked<&Reader<PTEntry, Extra>>)
    requires
        r.ptr() == ptr_lvl0,
{
    let (entry_lvl0, Tracked(o1), Tracked(prov_lvl0)) = read_level0(ptr_lvl0, Tracked(r));
    let entry_lvl0: PTEntry = entry_lvl0.into();
    if !entry_lvl0.present() {
        return;
    }
    let ptr_lvl1: *mut usize =
        vstd::raw_ptr::with_exposed_provenance(entry_lvl0.next(), Tracked(prov_lvl0));
    let (entry_lvl1, Tracked(o2), Tracked(prov_lvl1)) =
        read_level1(ptr_lvl1, Tracked(r), Tracked(&o1));
    let entry_lvl1: PTEntry = entry_lvl1.into();
    if !entry_lvl1.present() {
        return;
    }
    let ptr_lvl2: *mut usize =
        vstd::raw_ptr::with_exposed_provenance(entry_lvl1.next(), Tracked(prov_lvl1));
    let (_entry_lvl2, _, _) = read_level2(ptr_lvl2, Tracked(r), Tracked(&o1), Tracked(&o2));
}

// Depth 3. The nesting inside these calls cannot be made recursive: the
// recursive call would sit in an `open_atomic_invariant!` body, so it would need
// `#[verifier::atomic]`, which Verus rejects on recursive functions. `pt::walk` recurses
// because publishing reaches a child reader without holding the parent open.
fn walk_level3(ptr_lvl0: *mut usize, Tracked(r): Tracked<&Reader<PTEntry, Extra>>)
    requires
        r.ptr() == ptr_lvl0,
{
    let (entry_lvl0, Tracked(o1), Tracked(prov_lvl0)) = read_level0(ptr_lvl0, Tracked(r));
    let entry_lvl0: PTEntry = entry_lvl0.into();
    if !entry_lvl0.present() {
        return;
    }
    let ptr_lvl1: *mut usize =
        vstd::raw_ptr::with_exposed_provenance(entry_lvl0.next(), Tracked(prov_lvl0));
    let (entry_lvl1, Tracked(o2), Tracked(prov_lvl1)) =
        read_level1(ptr_lvl1, Tracked(r), Tracked(&o1));
    let entry_lvl1: PTEntry = entry_lvl1.into();
    if !entry_lvl1.present() {
        return;
    }
    let ptr_lvl2: *mut usize =
        vstd::raw_ptr::with_exposed_provenance(entry_lvl1.next(), Tracked(prov_lvl1));
    let (entry_lvl2, Tracked(o3), Tracked(prov_lvl2)) =
        read_level2(ptr_lvl2, Tracked(r), Tracked(&o1), Tracked(&o2));
    let entry_lvl2: PTEntry = entry_lvl2.into();
    if !entry_lvl2.present() {
        return;
    }
    let ptr_lvl3: *mut usize =
        vstd::raw_ptr::with_exposed_provenance(entry_lvl2.next(), Tracked(prov_lvl2));
    let (_entry_lvl3, _, _) =
        read_level3(ptr_lvl3, Tracked(r), Tracked(&o1), Tracked(&o2), Tracked(&o3));
}

/// PROPERTY 1, through the contract: a read taken while holding an `Observed` token returns a
/// value reachable from the one that token names.
fn example_read_moves_forward(
    ptr: *mut usize,
    Tracked(r): Tracked<&Reader<PTEntry, Extra>>,
    Tracked(past): Tracked<Observed<PTEntry>>,
)
    requires
        r.ptr() == ptr,
        r.has_observed(past),
{
    let ghost was = past.snapshot();
    let (value, Tracked(now)) = PTEntry::read(ptr, Tracked(r), Tracked(Some(&past)));
    proof {
        // Whatever a concurrent writer did, it moved us forward and not back.
        assert(PTEntry::reachable(was, now.snapshot()));
    }
}

} // verus!
