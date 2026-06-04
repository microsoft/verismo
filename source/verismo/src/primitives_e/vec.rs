use alloc::vec::Vec;

use super::*;
use crate::vbox::*;

// `WellFormed`/`IsConstant`/`VTypeCast`/`SpecSize` impls for `Vec<T>` were
// moved into `verismo_tspec::vec_spec` to satisfy Rust's orphan rule (both
// trait and type are now foreign to verismo). What remains here is the
// `MutFnTrait` plumbing that genuinely depends on `vbox`.

verus! {

pub struct PushParam<T> {
    pub val: T,
}

impl<'a, T> MutFnTrait<'a, PushParam<T>, bool> for Vec<T> {
    open spec fn spec_update_requires(&self, params: PushParam<T>) -> bool {
        true
    }

    open spec fn spec_update(&self, prev: &Self, params: PushParam<T>, ret: bool) -> bool {
        self@ === prev@.push(params.val)
    }

    fn box_update(&'a mut self, params: PushParam<T>) -> (ret: bool) {
        self.push(params.val);
        true
    }
}

struct RemoveParam {
    i: usize,
}

impl<'a, T> MutFnTrait<'a, RemoveParam, T> for Vec<T> {
    closed spec fn spec_update_requires(&self, params: RemoveParam) -> bool {
        0 <= params.i < self.len()
    }

    closed spec fn spec_update(&self, prev: &Self, params: RemoveParam, ret: T) -> bool {
        let i = params.i as int;
        &&& self@ === prev@.remove(i)
        &&& ret == prev@[i]
    }

    fn box_update(&'a mut self, params: RemoveParam) -> (ret: T) {
        self.remove(params.i)
    }
}

impl<T> VBox<Vec<T>> {
    pub fn remove(&mut self, i: usize) -> (ret: T)
        requires
            0 <= i < old(self)@.len(),
        ensures
            self.snp().is_vmpl0_private() ==> self@@ === old(self)@@.remove(i as int),
            self.only_val_updated(*old(self)),
            ret === old(self)@@[i as int],
    {
        self.box_update(RemoveParam { i })
    }

    pub fn push(&mut self, val: T)
        ensures
            self.snp().is_vmpl0_private() ==> self@@ === old(self)@@.push(val),
            self.only_val_updated(*old(self)),
    {
        self.box_update(PushParam { val });
    }
}

} // verus!
