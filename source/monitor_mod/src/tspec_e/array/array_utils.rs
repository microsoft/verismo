use super::*;

verus! {

#[verifier(inline)]
pub open spec fn spec_swap<T>(s: Seq<T>, i: int, j: int) -> Seq<T> {
    s.update(i, s[j]).update(j, s[i])
}

} // verus!
verus! {

impl<T: Copy, const N: IndexType> Array<T, N> {
    pub fn swap(&mut self, i: usize, j: usize)
        requires
            i < Self::spec_len(),
            j < Self::spec_len(),
            i.is_constant(),
            j.is_constant(),
        ensures
            forall|k: int|
                (0 <= k < self@.len() && k != i as int && k != j as int) ==> self@[k] === old(
                    self,
                )@[k],
            self@[i as int] === old(self)@[j as int],
            self@[j as int] === old(self)@[i as int],
            self@ =~~= spec_swap(old(self)@, i as int, j as int),
    {
        if i == j {
            assert(i as int == j as int);
            assert(self@ === old(self)@);
            return ;
        }
        let x1 = *self.index(i);
        let x2 = *self.index(j);
        proof {
            assert(x1 === old(self)@[i as int]);
            assert(x2 === old(self)@[j as int]);
        }
        self.update(j, x1);
        self.update(i, x2);
        proof {
            assert forall|k: int|
                (0 <= k < self@.len() && k != i as int && k != j as int) implies self@[k] === old(
                self,
            )@[k] by {}
        }
    }

    pub fn reverse(&mut self, start: usize, end: usize)
        requires
            start.is_constant(),
            end.is_constant(),
            0 <= start as int <= end as int <= Self::spec_len(),
        ensures
            forall|k: int|
                start as int <= k < end as int ==> self@[k] === old(self)@[end as int + start as int
                    - 1 - k],
            forall|k: int|
                0 <= k < start as int || end as int <= k < Self::spec_len() ==> self@[k] === old(
                    self,
                )@[k],
    {
        if end < 1 || start >= end - 1 {
            return ;
        }
        let mut i: usize = start;
        let mut j: usize = end - 1;
        while i < j
            invariant
                i as int <= j as int + 1,
                start as int <= i as int,
                j as int <= end as int - 1,
                end as int - 1 - j as int == i as int - start as int,
                0 <= (start as int) < (end as int) <= Self::spec_len(),
                forall|k: int|
                    start as int <= k < (i as int) || (j as int) < k < end as int ==> self@[k]
                        === old(self)@[end as int + start as int - 1 - k],
                forall|k: int|
                    i as int <= k <= j as int || 0 <= k < start as int || end as int <= k
                        < Self::spec_len() ==> self@[k] === old(self)@[k],
                i.is_constant(),
                j.is_constant(),
        {
            assert(i <= j);
            assert(j < Self::spec_len());
            self.swap(i, j);
            i = i + 1;
            j = j - 1;
        }
    }

    pub fn memset(&mut self, elem: T)
        requires
            old(self)@.len() > 0,
        ensures
            forall|j| 0 <= j < self@.len() ==> self@[j] === elem,
    {
        let mut i = 0;
        while i < self.len()
            invariant
                i.is_constant(),
                0 <= (i as int) <= self@.len(),
                forall|j: int| 0 <= j < (i as int) ==> self@[j] === elem,
        {
            self.set(i, elem);
            i = i + 1;
        }
    }
}

} // verus!
