use vstd::prelude::*;
use vstd::set_lib;

use super::*;

verus! {
pub trait MapAsSeq<T> {
    spec fn is_seq(&self, n: nat) -> bool;
}

impl<T> MapAsSeq<T> for Map<nat, T>
{
    open spec fn is_seq(&self, n: nat) -> bool{
        forall |k: nat| k < n ==> self.contains_key(k)
    }
}
    pub proof fn tracked_seq_remove<T>(tracked m: &mut Map<nat, T>, i: nat, n: nat) -> (tracked ret: T)
    requires
        old(m).is_seq(n),
        i < n,
    ensures
        forall |k: nat| k < i ==> m[k] === old(m)[k] && m.contains_key(k),
        forall |k: nat| i <= k < (n - 1) ==> m[k] === old(m)[k + 1] && m.contains_key(k),
        ret === old(m)[i],
    {
        let oldm = *m;
        let tracked ret = m.tracked_remove(i);
        let convert = |j: nat| if j < i {j} else {(j+1) as nat};
        let key_map = Map::<nat, nat>::new(
            |j: nat| 0 <= j < (n - 1),
            |j: nat| convert(j)
        );
        assert forall |j: nat|
            key_map.contains_key(j)
        implies
            m.contains_key(convert(j))
        by {
            assert(oldm.contains_key(j));
            assert(oldm.contains_key(j + 1));
        }
        m.tracked_map_keys_in_place(
            key_map
        );
        ret
    }

    pub proof fn tracked_seq_insert<T>(tracked m: &mut Map<nat, T>, i: nat, tracked v: T, n: nat)
    requires
        old(m).is_seq(n),
        i <= n,
    ensures
        m[i] === v,
        m.contains_key(i),
        forall |k: nat| k < i ==> m[k] === old(m)[k] && m.contains_key(k),
        forall |k: nat| i + 1 <= k < (n + 1) ==> m[k] === old(m)[(k - 1) as nat] && m.contains_key(k),
    {
        let oldm = *m;
        let tracked ret = m.tracked_insert(n, v);
        let convert = |j: nat|if j < i {
                        j
                    } else if j == i {
                        n
                    } else {
                        (j-1) as nat
                    };
        let key_map = Map::<nat, nat>::new(
            |j: nat| 0 <= j < n + 1,
            |j: nat| convert(j)
        );
        assert forall |j: nat|
            key_map.contains_key(j)
        implies
            m.contains_key(convert(j))
        by {
            if j < i {
                assert(oldm.contains_key(j));
            }
            if j > i {
                assert(oldm.contains_key((j - 1) as nat));
            }
        }
        m.tracked_map_keys_in_place(
            key_map
        );
        ret
    }
}
