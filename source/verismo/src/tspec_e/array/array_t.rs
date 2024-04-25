//mod s;
//mod sec;
//pub use s::*;
use super::*;

verus! {

impl<T: Default + core::marker::Copy, const N: IndexType> Default for Array<T, N> {
    #[verifier::external_body]
    fn default() -> Self {
        Array { array: [Default::default();N] }
    }
}

} // verus!
verus! {

impl<T: core::marker::Copy, const N: usize> Clone for Array<T, N> {
    #[verifier(external_body)]
    fn clone(&self) -> (ret: Self)
        ensures
            ret === *self,
    {
        let new = self.array;
        Array { array: new }
    }
}

} // verus!
verus! {

impl<T, const N: IndexType> Array<T, N> {
    pub spec fn _spec_index(&self, i: int) -> T;

    pub open spec fn view(&self) -> Seq<T> {
        Seq::new(Self::spec_len(), |i| self._spec_index(i))
    }

    #[verifier(inline)]
    pub open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
}

impl<T: core::marker::Copy, const N: IndexType> Array<T, N> {
    #[verifier(external_body)]
    pub const fn new(elem: T) -> (ret: Self)
        ensures
            ret@ =~~= Seq::new(N as nat, |i| elem),
    {
        let new = [elem;N];
        Array { array: new }
    }
}

} // verus!
use core::ops::Index;
verus! {

impl<T, const N: IndexType> Array<T, N> {
    pub open spec fn spec_len() -> nat {
        N as nat
    }

    #[verifier(external_body)]
    pub fn trusted_len() -> (ret: IndexType)
        ensures
            ret as nat == Self::spec_len(),
    {
        N
    }

    #[verifier(external_body)]
    pub fn trusted_index(&self, index: usize) -> (ret: &T)
        requires
            index < self@.len(),
        ensures
            *ret === self.spec_index(index as int),
    {
        &self.array[index]
    }

    #[verifier(external_body)]
    pub fn trusted_update(&mut self, index: usize, elem: T) -> (ret: T)
        requires
            0 <= index < old(self)@.len(),
        ensures
            self@ === old(self)@.update(index as int, elem),
            ret === old(self)@[index as int],
    {
        core::mem::replace(&mut self.array[index], elem)
    }
}

impl<T: IsConstant + WellFormed, const N: IndexType> Array<T, N> {
    #[verifier(external_body)]
    pub fn as_slice<'a>(&'a self) -> (ret: &'a [T])
        ensures
            self@ === ret@,
    {
        &self.array
    }
}

/*impl<T: Default + SpecDefault, const N: IndexType> Array<T, N>
    {
        // User must update back to help verus get the updated element back
        pub fn trusted_take(&mut self, index: usize) -> (ret: T)
            requires
                0<= index < old(self)@.len(),
            ensures
                ret === old(self).spec_index(index as int),
                self@ === old(self)@.update(index as int, T::spec_default())
        {
            self.trusted_update(index, crate::tspec_e::default::default())
        }
    }*/
} // verus!
