use super::*;

verismo_simple! {

pub open spec fn spec_valid_range(real: (usize_s, usize_s), max: usize_s) -> (usize_s, usize_s) {
    let (start, size) = real;
    let valid_start = if start < max {
        start
    } else {
        max
    };

    let valid_size = if max <= start {
        usize_s::spec_constant(0)
    } else if size < (max - start) as usize_s {
        size
    } else {
        (max - start) as usize_s
    };
    (valid_start, valid_size)
}

pub trait MemRangeInterface {
    spec fn self_wf(&self) -> bool;

    spec fn real_wf(r: (usize_s, usize_s)) -> bool;

    proof fn proof_constant_real_wf(r: (usize_s, usize_s))
    ensures
        r.is_constant() ==> Self::real_wf(r);

    fn real_range(&self) -> (ret: (usize_s, usize_s))
    requires
        self.self_wf(),
    ensures
        ret === self.spec_real_range(),
        Self::real_wf(ret);

    fn end_max() -> (ret: usize_s)
    ensures
        ret == Self::spec_end_max(),
        ret.is_constant();

    spec fn spec_end_max() -> usize_t;

    spec fn spec_real_range(&self) -> (usize_s, usize_s);

    spec fn spec_set_range(self, r: (usize_s, usize_s)) -> Self where Self: core::marker::Sized;

    fn update_range(&mut self, r: (usize_s, usize_s)) where Self: core::marker::Sized
    requires
        Self::real_wf(r),
        old(self).self_wf(),
        r.0.wf(),
        r.1.wf(),
    ensures
        self.self_wf(),
        self.spec_real_range() === r,
        (*old(self)).spec_set_range(r) === *self;
}

impl MemRangeInterface for (usize_s, usize_s) {
    #[verifier(inline)]
    open spec fn self_wf(&self) -> bool {
        &&& self.0.wf()
        &&& self.1.wf()
    }

    open spec fn real_wf(r: (usize_s, usize_s)) -> bool {
        r.self_wf()
    }

    proof fn proof_constant_real_wf(r: (usize_s, usize_s)) {}

    #[inline]
    fn real_range(&self) -> (ret: (usize_s, usize_s))
    {
        *self
    }

    #[inline]
    fn end_max() -> (ret: usize_s)
    {
        VM_MEM_SIZE as usize_s
    }

    #[verifier(inline)]
    open spec fn spec_end_max() -> usize_t {
        VM_MEM_SIZE as usize_t
    }

    #[verifier(inline)]
    open spec fn spec_real_range(&self) -> (usize_s, usize_s) {
        *self
    }

    #[verifier(inline)]
    open spec fn spec_set_range(self, r: (usize_s, usize_s)) -> Self {
        r
    }

    #[inline]
    fn update_range(&mut self, r: (usize_s, usize_s))
    {
        *self = r;
    }
}

impl MemRangeInterface for (usize_t, usize_t) {
    #[verifier(inline)]
    open spec fn self_wf(&self) -> bool {
        true
    }

    open spec fn real_wf(r: (usize_s, usize_s)) -> bool {
        r.is_constant()
    }

    proof fn proof_constant_real_wf(r: (usize_s, usize_s)) {}

    #[inline]
    fn real_range(&self) -> (ret: (usize_s, usize_s))
    {
        (self.0.into(), self.1.into())
    }

    #[inline]
    fn end_max() -> (ret: usize_s)
    {
        VM_MEM_SIZE as usize_s
    }

    #[verifier(inline)]
    open spec fn spec_end_max() -> usize_t {
        VM_MEM_SIZE as usize_t
    }

    #[verifier(inline)]
    open spec fn spec_real_range(&self) -> (usize_s, usize_s) {
        (self.0.vspec_cast_to(), self.1.vspec_cast_to())
    }

    #[verifier(inline)]
    open spec fn spec_set_range(self, r: (usize_s, usize_s)) -> Self {
        (r.0.vspec_cast_to(), r.1.vspec_cast_to())
    }

    #[inline]
    fn update_range(&mut self, r: (usize_s, usize_s))
    {
        *self = (r.0.into(), r.1.into());
        proof{
            r.0@.proof_constant();
            r.1@.proof_constant();
            assert(self.spec_real_range().0@ === r.0@);
            assert(self.spec_real_range().1@ === r.1@);
        }
    }
}

pub open spec fn range_speclt<T: MemRangeInterface>() -> spec_fn(T, T) -> bool {
    |v1: T, v2: T|
    v1.spec_real_range().0 < v2.spec_real_range().0 ||
        ((v1.spec_real_range().0 == v2.spec_real_range().0 &&
        v1.spec_real_range().1 < v2.spec_real_range().1))
}

pub trait GeneratedMemRangeInterface {
    spec fn spec_max() -> nat;

    spec fn spec_sec_max() -> usize_s;

    spec fn spec_range(&self) -> (int, nat);

    spec fn spec_aligned_range(&self) -> (int, nat);

    spec fn spec_valid_range(&self) -> (usize_s, usize_s);

    spec fn spec_valid_end(&self) -> usize_s;

    spec fn spec_start(&self) -> int;

    spec fn spec_end(&self) -> int;

    spec fn spec_cmp_max_requires(&self) -> bool;

    spec fn spec_lt_requires(&self, other: &Self) -> bool;

    spec fn spec_check_disjoint_requires(&self, other: &Self) -> bool;

    spec fn wf_range(&self) -> bool;

    spec fn speclt() -> spec_fn(Self, Self) -> bool where Self: core::marker::Sized;

    fn less(&self, other: &Self) -> (ret: bool) where Self: core::marker::Sized
    requires
        self.spec_lt_requires(other)
    ensures
        ret == Self::speclt()(*self, *other);

    fn start(&self) -> (ret: usize_s)
    requires
        self.spec_cmp_max_requires()
    ensures
        ret == self.spec_range().0,
        ret.is_constant(),
        ret <= Self::spec_max(),
        ret.wf();

    fn end(&self) -> (ret: usize_s)
    requires
        self.spec_cmp_max_requires()
    ensures
        ret == self.spec_range().end(),
        ret.is_constant(),
        ret <= Self::spec_max(),
        ret.wf();

    fn aligned_start(&self) -> (ret: usize_s)
    requires
        self.spec_cmp_max_requires()
    ensures
        ret == self.spec_aligned_range().0,
        ret.is_constant(),
        ret <= Self::spec_max(),
        ret as int % PAGE_SIZE!() == 0,
        ret.wf();

    fn size(&self) -> (ret: usize_s)
    requires
        self.spec_cmp_max_requires()
    ensures
        ret == self.spec_range().1,
        ret.is_constant(),
        ret <= Self::spec_max(),
        ret.wf();

    fn check_disjoint(&self, other: &Self) -> (ret: bool)
    requires
        self.spec_check_disjoint_requires(other),
        self.spec_cmp_max_requires(),
        other.spec_cmp_max_requires(),
    ensures
        ret === range_disjoint_(self.spec_range(), other.spec_range());

    fn check_inside(&self, other: &Self) -> (ret: bool)
    requires
        self.spec_check_disjoint_requires(other),
        self.spec_cmp_max_requires(),
        other.spec_cmp_max_requires(),
    ensures
        ret === inside_range(self.spec_range(), other.spec_range());
}

impl<T: MemRangeInterface> GeneratedMemRangeInterface for T {
    open spec fn spec_max() -> nat {
        Self::spec_end_max() as nat
    }

    open spec fn spec_sec_max() -> usize_s {
        usize_s::spec_constant(Self::spec_end_max())
    }

    open spec fn spec_cmp_max_requires(&self) -> bool {
        &&& self.spec_real_range().0.is_constant()
        &&& self.spec_real_range().1.is_constant()
        &&& Self::spec_sec_max().is_constant()
        &&& self.self_wf()
    }

    #[verifier(inline)]
    open spec fn speclt() -> spec_fn(Self, Self) -> bool {
        range_speclt::<T>()
    }

    open spec fn spec_lt_requires(&self, other: &Self) -> bool {
        &&& self.spec_real_range().0.is_constant()
        &&& self.spec_real_range().1.is_constant()
        &&& other.spec_real_range().0.is_constant()
        &&& other.spec_real_range().1.is_constant()
        &&& Self::spec_sec_max().is_constant()
        &&& self.self_wf()
        &&& other.self_wf()
    }

    open spec fn spec_check_disjoint_requires(&self, other: &Self) -> bool {
        &&& self.spec_real_range().0.is_constant()
        &&& self.spec_real_range().1.is_constant()
        &&& other.spec_real_range().0.is_constant()
        &&& other.spec_real_range().1.is_constant()
        &&& Self::spec_sec_max().is_constant()
        &&& self.self_wf()
        &&& other.self_wf()
    }

    open spec fn spec_range(&self) -> (int, nat) {
        (self.spec_valid_range().0 as int, self.spec_valid_range().1 as nat)
    }

    open spec fn spec_aligned_range(&self) -> (int, nat) {
        let start = self.spec_range().0;
        let end  = self.spec_range().end();
        range(spec_align_down(start, PAGE_SIZE!()), spec_align_up(end, PAGE_SIZE!()))
    }

    open spec fn spec_valid_range(&self) -> (usize_s, usize_s) {
        spec_valid_range(self.spec_real_range(), Self::spec_sec_max())
    }

    open spec fn spec_valid_end(&self) -> usize_s {
        (self.spec_valid_range().0 + self.spec_valid_range().1) as usize_s
    }

    open spec fn wf_range(&self) -> bool {
        &&& self.spec_valid_range().0 == self.spec_real_range().0
        &&& self.spec_valid_range().1 == self.spec_real_range().1
        &&& self.spec_valid_range().1 != 0
        &&& self.spec_real_range().0.is_constant()
        &&& self.spec_real_range().1.is_constant()
        &&& self.spec_range().end() <= Self::spec_max()
    }

    open spec fn spec_start(&self) -> int {
        self.spec_range().0
    }

    open spec fn spec_end(&self) -> int {
        self.spec_range().end()
    }

    fn less(&self, other: &Self) -> bool {
        assert(self.spec_real_range().0.is_constant());
        assert(other.spec_real_range().0.is_constant());
        assert(self.spec_real_range().1.is_constant());
        assert(other.spec_real_range().1.is_constant());
        if self.real_range().0 < other.real_range().0 {
            true
        } else {
            if self.real_range().0 == other.real_range().0 {
                self.real_range().1 < other.real_range().1
            } else {
                false
            }
        }
    }

    fn start(&self) -> (ret: usize_s)
    {
        assert(self.spec_real_range().0.is_constant());
        if self.real_range().0 < Self::end_max() {
            self.real_range().0
        } else {
            Self::end_max()
        }
    }

    fn size(&self) -> (ret: usize_s)
    {
        let (start, size) = self.real_range();
        assert(start.is_constant());
        assert(size.is_constant());
        if !(start < Self::end_max()) {
            0
        } else if size < Self::end_max() - start {
            size
        } else {
            Self::end_max() - start
        }
    }

    #[inline]
    fn end(&self) -> (ret: usize_s)
    {
        self.start() + self.size()
    }

    fn aligned_start(&self) -> (ret: usize_s)
    {
        page_align_down(self.start())
    }

    fn check_disjoint(&self, other: &Self) -> (ret: bool)
    {
        assert(self.spec_real_range().0.is_constant());
        assert(other.spec_real_range().0.is_constant());
        assert(self.spec_real_range().1.is_constant());
        assert(other.spec_real_range().1.is_constant());
        !(self.start() < other.end()) || !(other.start() < self.end()) || self.size() == 0 || other.size() == 0
    }

    fn check_inside(&self, other: &Self) -> bool {
        &&& other.start() <= self.start()
        &&& self.start() < other.end()
        &&& self.end() <= other.end()
    }
}
}

verismo_simple! {
pub open spec fn to_range_fn<T: MemRangeInterface>() -> spec_fn(T) -> (int, nat) {
    |v: T| v.spec_range()
}

pub open spec fn to_page_aligned_range_fn() -> spec_fn((int, nat)) -> (int, nat) {
    |v: (int, nat)|
        range(spec_align_down(v.0, PAGE_SIZE!()), spec_align_up(v.end(), PAGE_SIZE!()))
}

pub trait MemRangeSeqInterface {
    spec fn to_valid_ranges(&self) -> Set<(int, nat)>;
    spec fn to_aligned_ranges(&self) -> Set<(int, nat)>;
    spec fn to_range_seq(&self) -> Seq<(int, nat)>;
    spec fn to_aligned_range_seq(&self) -> Seq<(int, nat)>;
    spec fn to_valid_ranges_internal(&self) -> Set<(int, nat)>;
    spec fn to_aligned_ranges_internal(&self) -> Set<(int, nat)>;
    spec fn to_aligned_ranges_internal2(&self) -> Set<(int, nat)>;
    spec fn has_aligned_ranges_internal(&self, r: (int, nat)) -> bool;
    proof fn lemma_align_ranges_reveal(&self)
    ensures
        self.to_aligned_ranges_internal() =~~= self.to_aligned_ranges(),
        self.to_aligned_ranges_internal2() =~~= self.to_aligned_ranges();

    proof fn lemma_valid_ranges_reveal(&self)
    ensures
        self.to_valid_ranges_internal() =~~= self.to_valid_ranges();
}

pub open spec fn empty_ranges() -> Set<(int, nat)> {
    Set::new(|r: (int, nat)| r.1 == 0)
}

impl<T: MemRangeInterface> MemRangeSeqInterface for Seq<T>
{
    open spec fn to_range_seq(&self) -> Seq<(int, nat)> {
        seq_uop(*self, to_range_fn())
    }

    open spec fn to_aligned_range_seq(&self) -> Seq<(int, nat)> {
        seq_uop(self.to_range_seq(), to_page_aligned_range_fn())
    }

    open spec fn to_valid_ranges(&self) -> Set<(int, nat)> {
        let s = self.to_range_seq();
        //set_uop(self.to_set(), to_range_fn()).difference(empty_ranges())
        s.to_set().difference(empty_ranges())
    }

    open spec fn to_aligned_ranges(&self) -> Set<(int, nat)>
    {
        /*let s = self.to_aligned_range_seq();
        //set_uop(self.to_set(), to_page_aligned_range_fn()).difference(empty_ranges())
        s.to_set().difference(empty_ranges())*/
        self.to_aligned_ranges_internal()
    }

    open spec fn to_valid_ranges_internal(&self) -> Set<(int, nat)> {
        //let s = self.to_range_seq();
        Set::new(|r: (int, nat)| r.1 != 0 &&
            exists |i: int| 0 <= i && i < self.len() &&
                (#[trigger]self[i]).spec_range() === r)
        //s.to_set().difference(empty_ranges())
    }

    open spec fn has_aligned_ranges_internal(&self, r: (int, nat)) -> bool {
        r.1 != 0 &&
        exists |i: int|
            0<= i && i < self.len() &&
            (#[trigger]self[i]).spec_aligned_range() === r &&
            self[i].spec_range().1 != 0
    }

    open spec fn to_aligned_ranges_internal(&self) -> Set<(int, nat)>
    {
        Set::new(|r: (int, nat)|
            self.has_aligned_ranges_internal(r)
        )
    }

    open spec fn to_aligned_ranges_internal2(&self) -> Set<(int, nat)>
    {
        set_uop(self.to_valid_ranges(), to_page_aligned_range_fn())
    }

    proof fn lemma_align_ranges_reveal(&self)
    {
        assert forall |v|
            self.to_aligned_ranges_internal().contains(v) == self.to_aligned_ranges().contains(v)
        by {
            if self.to_aligned_ranges_internal().contains(v) {
                assert (self.has_aligned_ranges_internal(v));
                let i = choose |i: int| 0 <= i && i < self.len() &&
                    self[i].spec_aligned_range() === v &&
                    self[i].spec_range().1 != 0;
                assert(self[i].spec_aligned_range() === v);
                assert(v.1 != 0);
                assert(self.to_aligned_ranges_internal().contains(self[i].spec_aligned_range()));
                assert(self.to_set().contains(self[i]));
                assert(self.to_aligned_range_seq()[i] === (v));
                assert(self.to_aligned_ranges().contains(v));
            }
            if self.to_aligned_ranges().contains(v) {
                assert(self.to_aligned_ranges_internal().contains(v));
            }
        }

        assert forall |v|
            self.to_aligned_ranges_internal().contains(v) == self.to_aligned_ranges_internal2().contains(v)
        by {
            if self.to_aligned_ranges_internal().contains(v) {
                assert (self.has_aligned_ranges_internal(v));
                let i = choose |i: int| 0 <= i && i < self.len() &&
                    self[i].spec_aligned_range() === v && self[i].spec_range().1 != 0;
                assert(self[i].spec_aligned_range() === v);
                assert(v.1 != 0);
                assert(0 <= i && i < self.len());
                assert(self.to_valid_ranges().contains(self[i].spec_range())) by {
                    self.lemma_valid_ranges_reveal();
                    assert(self[i].spec_range().1 != 0);
                    assert(self.to_valid_ranges_internal().contains(self[i].spec_range()));
                }
                assert(to_page_aligned_range_fn()(self[i].spec_range()) === v);
            }

            if self.to_aligned_ranges_internal2().contains(v) {
                assert (exists |i: int| 0<= i && i < self.len() &&
                to_page_aligned_range_fn()(self[i].spec_range()) === v);
                let i = choose |i: int| 0 <= i && i < self.len() &&
                to_page_aligned_range_fn()(self[i].spec_range()) === v;
                assert(to_page_aligned_range_fn()(self[i].spec_range()) === v);
                assert(to_page_aligned_range_fn()(self[i].spec_range()) === self[i].spec_aligned_range());
                assert(self.to_aligned_ranges_internal().contains(v));
            }
        }
    }

    proof fn lemma_valid_ranges_reveal(&self){
        assert forall |v|
            self.to_valid_ranges_internal().contains(v) == self.to_valid_ranges().contains(v)
        by {
            if self.to_valid_ranges_internal().contains(v) {
                let i = choose |i: int| 0 <= i && i < self.len() &&
                    self[i].spec_range() === v;
                assert(self[i].spec_range() === v);
                assert(v.1 != 0);
                assert(self.to_valid_ranges_internal().contains(self[i].spec_range()));
                assert(self.to_set().contains(self[i]));
                assert(self.to_range_seq()[i] === (v));
                assert(self.to_valid_ranges().contains(v));
            }
            if self.to_valid_ranges().contains(v) {
            }
        }
    }
}

proof fn lemma_to_valid_ranges_push(s: Seq<(int, nat)>, v: (int, nat))
ensures
    v.1 != 0 ==> s.push(v).to_set().difference(empty_ranges()) =~~= s.to_set().difference(empty_ranges()).insert(v),
    v.1 == 0 ==> s.push(v).to_set().difference(empty_ranges()) =~~= s.to_set().difference(empty_ranges())
{
    s.to_multiset_ensures();
    seq_to_multi_set_to_set(s);
    seq_to_multi_set_to_set(s.push(v));
    assert(s.push(v).to_multiset() === s.to_multiset().insert(v));
    assert(s.to_multiset().insert(v).dom() =~~= s.to_multiset().dom().insert(v));
    assert(s.push(v).to_set() =~~= s.to_set().insert(v));
    if v.1 == 0 {
        assert(empty_ranges().contains(v));
    } else {
        assert(!empty_ranges().contains(v));
    }
}

pub open spec fn mem_range_formatted<T: MemRangeInterface>(ret_seq: Seq<T>) -> bool {
    &&& seq_is_sorted(ret_seq, range_speclt())
    &&& forall |i: int| 0 <= i < ret_seq.len() ==> (#[trigger]ret_seq[i]).wf_range()
    &&& forall |i: int| 0 <= i < ret_seq.len() ==> ret_seq.to_valid_ranges().contains(#[trigger]ret_seq[i].spec_range())
    &&& forall |i: int, j: int| 0 <= i < j < ret_seq.len() ==>
        (#[trigger]ret_seq[i]).spec_range().0 <= (#[trigger]ret_seq[j]).spec_range().0 &&
        (ret_seq[i]).spec_range().end() <= (ret_seq[j]).spec_range().0
}

pub proof fn mem_range_formatted_is_disjoint<T: MemRangeInterface>(ret_seq: Seq<T>)
requires
    mem_range_formatted(ret_seq),
ensures
    forall |i: int, j: int| 0 <= i < j < ret_seq.len()
        ==> range_disjoint_((#[trigger]ret_seq[i]).spec_range(), (#[trigger]ret_seq[j]).spec_range())
{
    assert forall |i: int, j: int| 0 <= i < ret_seq.len() && 0 <= j < ret_seq.len() && i != j
    implies range_disjoint_((#[trigger]ret_seq[i]).spec_range(), (#[trigger]ret_seq[j]).spec_range())
    by {
        if i < j {
            assert((#[trigger]ret_seq[i]).spec_range().0 <= (#[trigger]ret_seq[j]).spec_range().0 &&
            (ret_seq[i]).spec_range().end() <= (ret_seq[j]).spec_range().0);
        } else {
            assert(j < i);
            assert((#[trigger]ret_seq[j]).spec_range().0 <= (#[trigger]ret_seq[i]).spec_range().0 &&
            (ret_seq[j]).spec_range().end() <= (ret_seq[i]).spec_range().0);
        }
    }
}

pub open spec fn format_range_ensures<T: MemRangeInterface>(ret_seq: Seq<T>, prev: Seq<T>, ri: nat) -> bool {
    let n = prev.len();
    let wi = ret_seq.len();
    &&& (wi <= ri <= n)
    &&& (ri == n) ==> (ret_seq.to_valid_ranges() === prev.to_valid_ranges())
    &&& mem_range_formatted(ret_seq)
    &&& forall |i| 0 <= i < wi as int ==> is_format_entry(ret_seq[i], prev)
}

pub open spec fn is_format_entry<T: MemRangeInterface>(entry: T, oldself: Seq<T>) -> bool {
    &&& (exists |j| entry === oldself[j].spec_set_range(entry.spec_real_range()) &&
                    0 <= j && j < oldself.len())
    //&&& entry.spec_real_range().0.is_constant()
    //&&& entry.spec_real_range().1.is_constant()
}
}
verus! {

impl<T: MemRangeInterface + Copy, const N: usize_t> Array<T, N> {
    pub fn format_range(&mut self, len: usize_t) -> (ret_lens: (usize_t, usize_t))
        requires
            (len).is_constant(),
            forall|i| 0 <= i < (len as int) ==> (#[trigger] old(self)@[i]).self_wf(),
            0 <= (len as int) <= old(self)@.len(),
            forall|i|
                0 <= i < (len as int) ==> (#[trigger] old(
                    self,
                )@[i]).spec_real_range().0.is_constant() && old(
                    self,
                )@[i].spec_real_range().1.is_constant(),
    //forall |e| old(self)@.take((len) as int).to_set().contains(e) ==> e.spec_real_range().0.is_constant() && e.spec_real_range().1.is_constant(),

        ensures
            ret_lens.0.is_constant(),
            ret_lens.1.is_constant(),
            old(self)@.len() == self@.len(),
            ret_lens.1 <= ret_lens.0,
            ret_lens.0 <= self@.len(),
            forall|i| 0 <= i < (len as int) ==> (#[trigger] self@[i]).self_wf(),
            format_range_ensures(
                self@.take(ret_lens.1 as int),
                old(self)@.take(len as int),
                ret_lens.0 as nat,
            ),
            forall|i: int| (ret_lens.1 as int) <= i < self@.len() ==> old(self)@.contains(self@[i]),
    {
        let n = len;
        if n == 0 {
            assert(seq_is_sorted(self@.take(n as int), range_speclt::<T>()));
            return (0, 0);
        }
        let ghost speclt = range_speclt::<T>();
        let ghost oldself = self@;
        let ghost oldseq = self@.take(n as int);
        let less = |v1: T, v2: T| -> (ret: bool)
            requires
                v1.spec_lt_requires(&v2),
            ensures
                ret == speclt(v1, v2),
            { v1.less(&v2) };
        proof {
            seq_to_multi_set_to_set(oldseq);
            assert forall|x, y|
                oldseq.to_set().contains(x) && oldseq.to_set().contains(
                    y,
                ) implies #[trigger] less.requires((x, y)) by {
                assert(x.spec_real_range().0.is_constant());
                assert(x.spec_real_range().1.is_constant());
                assert(y.spec_real_range().0.is_constant());
                assert(y.spec_real_range().1.is_constant());
                assert(T::spec_sec_max().is_constant());
                assert(x.spec_lt_requires(&y));
            }
        }
        self.sort(0, n, less, Ghost(speclt));
        proof {
            seq_to_multi_set_to_set(self@.take(n as int));
            assert(self@.take(n as int).to_set() =~~= oldseq.to_set());
            assert forall|e| self@.take(n as int).to_set().contains(e) implies (
            e.spec_real_range().0.is_constant() && e.spec_real_range().1.is_constant()) by {
                assert(oldseq.to_set().contains(e));
            }
            assert(oldself.take(n as int).to_range_seq().to_multiset() === self@.take(
                n as int,
            ).to_range_seq().to_multiset()) by {
                proof_seq_to_seq_eq_multiset(
                    oldself.take(n as int),
                    self@.take(n as int),
                    to_range_fn(),
                );
            }
            seq_to_multi_set_to_set(oldself.take(n as int).to_range_seq());
            seq_to_multi_set_to_set(self@.take(n as int).to_range_seq());
            assert(oldself.take(n as int).to_valid_ranges() === self@.take(
                n as int,
            ).to_valid_ranges());
            assert(self@.take(n as int) =~~= self@.take(n as int).take(n as int));
            self@.take(n as int).to_multiset_ensures();
            oldself.take(n as int).to_multiset_ensures();
            assert forall|i| 0 <= i < (n as int) implies (#[trigger] self@[i]).self_wf() by {
                let e = self@[i];
                assert(self@.take(n as int)[i] === e);
                assert(self@.take(n as int).to_multiset().count(e) > 0);
                assert(oldself.take(n as int).contains(e));
                let j = choose|j: int| 0 <= j < (n as int) && oldself.take(n as int)[j] === e;
                assert(0 <= j < (n as int));
                assert(oldself[j] === oldself.take(n as int)[j]);
            }
        }
        // read index
        let mut ri: usize = 0;
        // write index
        let mut wi: usize = 0;
        let ghost prev = self@.take(n as int);
        let ghost prevself = self@;
        let ghost remap: Seq<int> = Seq::empty();
        while ri < n
            invariant
                ri.is_constant(),
                wi.is_constant(),
                n.is_constant(),
                ri <= n,
                wi <= ri,
                n <= self@.len(),
                n == prev.len(),
                speclt === range_speclt::<T>(),
                forall|i| 0 <= i < (n as int) ==> (#[trigger] self@[i]).self_wf(),
                forall|i: int| 0 <= i < (n as int) ==> prev[i] === prevself[i],
                forall|i: int| (wi as int) <= i < self@.len() ==> self@[i] === prevself[i],
                forall|e|
                    self@.take(n as int).to_set().contains(e) ==> (
                    e.spec_real_range().0.is_constant() && e.spec_real_range().1.is_constant()),
                seq_is_sorted(prev, speclt),
                seq_is_sorted(self@.take(wi as int), speclt),
                forall|i: int| 0 <= i < (wi as int) ==> (#[trigger] self@[i]).wf_range(),
                self@.take(wi as int).to_valid_ranges() =~~= prev.take(ri as int).to_valid_ranges(),
                forall|i: int, j: int|
                    0 <= i < j < (wi as int) ==> (#[trigger] self@[i]).spec_range().0 <= (
                    #[trigger] self@[j]).spec_range().0 && (self@[i]).spec_range().end() <= (
                    self@[j]).spec_range().0,
                seq_is_sorted(remap, |v1: int, v2: int| v1 < v2),
                remap.len() == wi as int,
                forall|i| 0 <= i < remap.len() ==> 0 <= #[trigger] remap[i] < (ri as int),
                forall|i|
                    0 <= i < (wi as int) ==> self@[i] === prev[remap[i]].spec_set_range(
                        self@[i].spec_real_range(),
                    ),
            ensures
                wi.is_constant(),
                ri.is_constant(),
                forall|i| 0 <= i < (n as int) ==> (#[trigger] self@[i]).self_wf(),
                forall|e|
                    self@.take(n as int).to_set().contains(e) ==> (
                    e.spec_real_range().0.is_constant() && e.spec_real_range().1.is_constant()),
                (wi as int) <= (ri as int) <= (n as int),
                forall|i: int| (wi as int) <= i < (n as int) ==> self@[i] === prev[i],
                forall|i: int| (wi as int) <= i < self@.len() ==> self@[i] === prevself[i],
                self@.take(wi as int).to_valid_ranges() =~~= prev.take(ri as int).to_valid_ranges(),
                seq_is_sorted(self@.take(wi as int), speclt),
                forall|i: int| 0 <= i < (wi as int) ==> (#[trigger] self@[i]).wf_range(),
                forall|i: int, j: int|
                    0 <= i < j < (wi as int) ==> (#[trigger] self@[i]).spec_range().0 <= (
                    #[trigger] self@[j]).spec_range().0 && (self@[i]).spec_range().end() <= (
                    self@[j]).spec_range().0,
                ri != n ==> 0 < (wi as int) < (n as int) && self@[wi as int].spec_start()
                    < self@[wi as int - 1].spec_end(),
                seq_is_sorted(remap, |v1: int, v2: int| v1 < v2),
                remap.len() == wi as int,
                forall|i| 0 <= i < remap.len() ==> 0 <= #[trigger] remap[i] < (ri as int),
                forall|i|
                    0 <= i < wi as int ==> self@[i] === prev[remap[i]].spec_set_range(
                        self@[i].spec_real_range(),
                    ),
        {
            let ghost aset = self@.take(n as int).to_set();
            let ghost subs = self@.take(n as int);
            let ghost prev_self = self@;
            let ghost v = self@[ri as int];
            proof {
                let ghost u = self@[wi as int];
                assert(v === prev[ri as int]);
                assert(u === prev[wi as int]);
                let ghost prev_u = self@[wi as int - 1];
                let ghost next_u = self@[wi as int + 1];
                let ghost next_v = self@[ri as int + 1];
                assert(v === subs[ri as int]);
                assert(aset.contains(v));
                assert(u === subs[wi as int]);
                assert(aset.contains(u));
                assert(!range_speclt()(v, u));
                if ri as int + 1 < n as int {
                    assert(v === prev[ri as int]);
                    assert(next_v === prev[ri as int + 1]);
                    assert(!range_speclt()(next_v, v));
                    assert(!range_speclt()(next_v, u));
                }
                if wi > 0 {
                    assert(prev_u === subs[wi as int - 1]);
                    assert(aset.contains(prev_u));
                }
                let prev_sub = prev.take(ri as int);
                let prev_next_sub = prev.take(ri as int + 1);
                assert(prev_next_sub =~~= prev_sub.push(v));
                assert(prev_next_sub.to_range_seq() =~~= prev_sub.to_range_seq().push(
                    v.spec_range(),
                ));
                // prove valid range set when there is an empty range.
                if v.spec_range().1 == 0 {
                    assert(v.spec_range().1 == 0);
                    assert(prev_sub.to_valid_ranges() =~~= prev_next_sub.to_valid_ranges()) by {
                        //lemma_to_valid_ranges_push(prev_sub.to_range_seq(), v.spec_range());
                        prev_sub.lemma_valid_ranges_reveal();
                        prev_next_sub.lemma_valid_ranges_reveal();
                        assert(!prev_next_sub.to_valid_ranges_internal().contains(v.spec_range()));
                        assert(!prev_sub.to_valid_ranges_internal().contains(v.spec_range()));
                        assert(prev_sub.to_valid_ranges_internal()
                            =~~= prev_next_sub.to_valid_ranges_internal()) by {
                            let s1 = prev_sub.to_valid_ranges_internal();
                            let s2 = prev_next_sub.to_valid_ranges_internal();
                            assert forall|r: (int, nat)| s1.contains(r) == s2.contains(r) by {
                                if s1.contains(r) {
                                    assert(r.1 != 0);
                                    let i = choose|i|
                                        prev_sub[i].spec_range() === r && 0 <= i && i
                                            < prev_sub.len();
                                    assert(prev_sub[i].spec_range() === r);
                                    assert(0 <= i && i < prev_next_sub.len());
                                    assert(prev_next_sub[i].spec_range() === r);
                                    assert(s2.contains(r));
                                }
                                if s2.contains(r) {
                                    assert(r.1 != 0);
                                    let i = choose|i|
                                        prev_next_sub[i].spec_range() === r && 0 <= i && i
                                            < prev_next_sub.len();
                                    assert(prev_next_sub[i].spec_range() === r);
                                    assert(0 <= i && i < prev_next_sub.len());
                                    assert(i != ri as int);
                                    assert(0 <= i && i < prev_sub.len());
                                    assert(s1.contains(r));
                                }
                            }
                        }
                    }
                }
                // prove sorted subrange

                proof_sorted_subrange(prev, speclt, ri as int, n as int);
                proof_sorted_subrange(prev, speclt, ri as int + 1, n as int);
                // prove unchanged right seq
                if ri as int + 1 < n as int {
                    assert(prev_self.subrange(wi as int + 1, n as int) =~~= prev_self.subrange(
                        wi as int,
                        n as int,
                    ).subrange(1, n as int - wi as int));
                    assert(prev.subrange(wi as int + 1, n as int) =~~= prev.subrange(
                        wi as int,
                        n as int,
                    ).subrange(1, n as int - wi as int));
                    assert(self@.subrange(wi as int + 1, n as int) =~~= prev.subrange(
                        wi as int + 1,
                        n as int,
                    ));
                }
                assert forall|i| 0 <= i < wi as int implies self@[i]
                    === prev[remap[i]].spec_set_range(self@[i].spec_real_range()) by {
                    assert(self@[i] === prev_self[i]);
                }
            }
            let mut entry = *self.index(ri);
            assert(self@[ri as int].self_wf());
            if entry.size().reveal_value() == 0 {
                ri = ri + 1;
                continue ;
            }
            let start = entry.start();
            let size = entry.size();
            proof {
                T::proof_constant_real_wf((start, size));
            }
            entry.update_range((start, size));
            if wi > 0 {
                assert(self@[wi as int - 1].self_wf());
                if start.reveal_value() < self.index(wi - 1).end().reveal_value() {
                    break ;
                }
            }
            self.update(wi, entry);
            ri = ri + 1;
            wi = wi + 1;
            proof {
                remap = remap.push(ri as int - 1);
                assert(remap.len() == wi as int);
                assert(prev[remap[wi as int - 1]] === v);
                assert forall|i| 0 <= i < wi as int implies self@[i]
                    === prev[remap[i]].spec_set_range(self@[i].spec_real_range()) by {
                    if i < wi as int - 1 {
                        assert(self@[i] === prev_self[i]);
                    }
                    assert(prev[remap[wi as int - 1]] === v);
                }
                let newseq = self@;
                assert(n <= newseq.len());
                assert forall|e| newseq.take(n as int).to_set().contains(e) implies (
                e.spec_real_range().0.is_constant() && e.spec_real_range().1.is_constant()) by {
                    let newsub = newseq.take(n as int);
                    assert(newsub.to_set().contains(e));
                    assert(newsub.contains(e));
                    let i = choose|i: int| (newsub[i] === e && 0 <= i < (newsub.len() as int));
                    assert(newsub[i] === e);
                    assert(0 <= i < (newsub.len() as int));
                    assert(newseq[i] === newsub[i]);
                    if (subs[i] === e) {
                        assert(subs.to_set().contains(e));
                    } else {
                        assert(e === entry);
                    }
                }
                self@.take(wi as int).to_range_seq().to_multiset_ensures();
                seq_to_multi_set_to_set(self@.take(wi as int).to_range_seq());
                assert(self@.take(wi as int).to_valid_ranges() =~~= prev.take(
                    ri as int,
                ).to_valid_ranges()) by {
                    assert(self@.take(wi as int - 1) =~~= prev_self.take(wi as int - 1));
                    lemma_to_valid_ranges_push(
                        self@.take(wi as int - 1).to_range_seq(),
                        entry.spec_range(),
                    );
                    lemma_to_valid_ranges_push(
                        prev.take(ri as int - 1).to_range_seq(),
                        entry.spec_range(),
                    );
                    assert(self@.take(wi as int).to_range_seq() =~~= self@.take(
                        wi as int - 1,
                    ).to_range_seq().push(entry.spec_range()));
                    assert(prev.take(ri as int).to_range_seq() =~~= prev.take(
                        ri as int - 1,
                    ).to_range_seq().push(entry.spec_range()));
                }
                proof_sorted_subrange(prev, speclt, ri as int, n as int);
            }
        }
        proof {
            if ri == n {
                assert(self@.take(wi as int).to_valid_ranges() === prev.take(
                    n as int,
                ).to_valid_ranges());
                assert(oldself.take(n as int).to_valid_ranges() === prev.take(
                    n as int,
                ).to_valid_ranges());
                assert(self@.take(wi as int).to_valid_ranges() === oldself.take(
                    n as int,
                ).to_valid_ranges());
            }
            assert forall|i| 0 <= i < wi as int implies is_format_entry(
                self@[i],
                oldself.take(n as int),
            ) by {
                let k = remap[i];
                assert(self@[i] === prev[k].spec_set_range(self@[i].spec_real_range()));
                assert(k < ri as int);
                assert(oldself.subrange(0, n as int).to_multiset() =~~= prev.to_multiset());
                prev.to_multiset_ensures();
                assert(prev.to_multiset().contains(prev[k]));
                assert(oldself.subrange(0, n as int).to_multiset().contains(prev[k]));
                oldself.subrange(0, n as int).to_multiset_ensures();
                assert(exists|j| oldself[j] === prev[k] && 0 <= j < (n as int));
                let j = choose|j| oldself[j] === prev[k] && 0 <= j < (n as int);
                assert(oldself[j] === prev[k]);
                assert(exists|j|
                    0 <= j < (n as int) && self@[i] === oldself.take(n as int)[j].spec_set_range(
                        self@[i].spec_real_range(),
                    )) by {
                    assert(0 <= j < (n as int));
                    assert(self@[i] === oldself[j].spec_set_range(self@[i].spec_real_range()));
                }
                assert(is_format_entry(self@[i], oldself.take(n as int)));
            }
            assert forall|i: int| (wi as int) <= i < self@.len() implies oldself.contains(
                self@[i],
            ) by {
                assert(prevself[i] === self@[i]);
                assert(prevself.contains(self@[i]));
                /*prevself.take(n as int).to_multiset_ensures();
                oldself.take(n as int).to_multiset_ensures();
                assert(prevself.take(n as int).to_multiset().count(self@[i]) ===
                    oldself.take(n as int).to_multiset().count(self@[i]));*/
                prevself.to_multiset_ensures();
                oldself.to_multiset_ensures();
                assert(prevself.to_multiset().count(self@[i]) === oldself.to_multiset().count(
                    self@[i],
                ));
            }
        }
        proof {
            self@.take(wi as int).lemma_valid_ranges_reveal();
        }
        (ri, wi)
    }
}

} // verus!
