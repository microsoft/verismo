use alloc::vec::Vec;

use super::*;
use crate::vbox::*;

verus! {
impl<T: WellFormed> WellFormed for Vec<T> {
    open spec fn wf(&self) -> bool {
        &&& self@.wf()
    }
}

impl<T: IsConstant + WellFormed> IsConstant for Vec<T> {
    open spec fn is_constant(&self) -> bool {
        self@.is_constant()
    }

    open spec fn is_constant_to(&self, vmpl: nat) -> bool {
        &&& self@.is_constant_to(vmpl)
    }
}

impl<T: ToSecSeq> VTypeCast<SecSeqByte> for Vec<T>
{
    open spec fn vspec_cast_to(self) -> SecSeqByte {
        self@.vspec_cast_to()
    }
}

impl<T: SpecSize> SpecSize for Vec<T> {
    open spec fn spec_size_def() -> nat;
}

pub struct PushParam <T>{
    pub val: T
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

struct RemoveParam{
    i: usize
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
        self.snp().is_vmpl0_private() ==>
            self@@ === old(self)@@.remove(i as int),
        self.only_val_updated(*old(self)),
        ret === old(self)@@[i as int],
    {
        self.box_update(RemoveParam{i})
    }

    pub fn push(&mut self, val: T)
    ensures
        self.snp().is_vmpl0_private() ==>
            self@@ === old(self)@@.push(val),
        self.only_val_updated(*old(self)),
    {
        self.box_update(PushParam{val});
    }
}
}
