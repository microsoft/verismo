use core::ops::Index;

use super::*;
use crate::vbox::MutFnTrait;

verus! {
// DO not use secret as index.
impl<T, const N: IndexType> Array<T, N> {
    verus! {
        #[inline(always)]
        pub fn const_len() -> (ret: usize_t)
        ensures
            ret == Self::spec_len(),
        {
            Self::trusted_len()
        }

        #[inline(always)]
        pub fn len(&self) -> (ret: usize)
        ensures
            ret == Self::spec_len(),
            ret.is_constant(),
        {
            Self::trusted_len()
        }

        pub fn index(&self, index: usize) -> (ret: &T)
        requires
            index < self@.len(),
            index.is_constant(),
        ensures
            ret === &self.spec_index(index as int)
        {
            &self.trusted_index(index)
        }
    }

    verus! {
        pub fn index2(&self, index: usize) -> (ret: &T)
        requires
            index < self@.len(),
        ensures
            ret === &self.spec_index(index as int)
        {
            &self.trusted_index(index)
        }
    }
}

impl<T, const N: IndexType> Array<T, N> {
    verus! {
        pub fn update(&mut self, index: usize, elem: T) -> (ret: T)
        requires
            index < old(self).view().len(),
            index.is_constant(),
            //old(self).wf(),
            //elem.wf(),
        ensures
            self@ === old(self)@.update(index as int, self@[index as int]),
            self@[index as int] === elem,
            ret === old(self).spec_index(index as int),
            //self.wf(),
        {
            self.trusted_update(index, elem)
            //assert(self@[index as int].wf());
            /*assert(self@.wf()) by {
                assert forall |i: int| 0 <= i < self@.len()
                implies (#[trigger]self@[i]).wf()
                by {}
            }*/
        }
    }
}
impl<T, const N: IndexType> Array<T, N> {
    verus! {
        pub fn set(&mut self, index: usize_t, elem: T)
        requires
            index < old(self).view().len(),
            index.is_constant(),
        ensures
            self@ === old(self)@.update(index as int, elem),
        {
            self.trusted_update(index, elem);
        }
    }

    verus! {
        pub fn set2(&mut self, index: usize, elem: T)
        requires
            index < old(self).view().len(),
        ensures
            self@ === old(self)@.update(index as int, elem),
        {
            self.trusted_update(index, elem);
        }
    }
}

verus! {
    pub struct ArrayUpdate<T> {
        pub index: usize,
        pub val: T
    }
    impl<T, const N: usize_t, 'a> MutFnTrait<'a, ArrayUpdate<T>, T> for Array<T, N>
    {
        open spec fn spec_update_requires(&self, params: ArrayUpdate<T>) -> bool {
            let ArrayUpdate{index, val} = params;
            &&& index < N
        }

        open spec fn spec_update(&self, prev: &Self, params: ArrayUpdate<T>, ret: T) -> bool {
            let ArrayUpdate{index, val} = params;
            &&& self@[index as int] === val
            &&& ret === prev@[index as int]
            &&& self@ === prev@.update(index as int, self@[index as int])
        }

        fn box_update(&'a mut self, params: ArrayUpdate<T>) -> (ret: T)
        {
            self.trusted_update(params.index, params.val)
        }
    }
}

verus! {
    impl<T: Default + SpecDefault, const N: IndexType> Array<T, N>
    {
        // User must update back to help verus get the updated element back
        pub fn take(&mut self, index: usize) -> (ret: T)
            requires
                index < old(self)@.len(),
                index.is_constant(),
            ensures
                ret === old(self).spec_index(index as int),
                self@ === old(self)@.update(index as int, self@[index as int]),
                self@[index as int] === T::spec_default(),
        {
            let ret = self.update(index, crate::tspec_e::default::default());
            ret

        }

        pub fn take_end(&mut self, index: usize, elem: T)
        requires
            (index as int) < old(self)@.len(),
            index.is_constant(),
        ensures
            self@ === old(self)@.update(index as int, self@[index as int]),
            self@[index as int] === elem,
        {
            self.update(index, elem);
        }
    }
}
}
