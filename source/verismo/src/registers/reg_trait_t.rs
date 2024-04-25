use super::*;

verus! {

pub trait AnyRegTrait<T: IsConstant + WellFormed> {
    spec fn reg_id(&self) -> RegName;

    spec fn write_extra_requires(&self, val: T, perm: RegisterPermValue<T>) -> bool;

    spec fn read_extra_requires(&self, perm: RegisterPermValue<T>) -> bool;

    fn read<'a>(&self, Tracked(perm): Tracked<&RegisterPerm>) -> (ret: T)
        requires
            perm.id() === self.reg_id(),
            perm.wf(),
            self.read_extra_requires(perm.view::<T>()),
        ensures
            ((!perm.view::<T>().shared()) || (perm.view::<T>().shared() && !spec_attack())
                ==> perm.view::<T>().value() === ret),
            (perm.view::<T>().shared() ==> (ret.wf() && ret.is_constant())),
    ;

    fn write(&self, value: T, Tracked(perm): Tracked<&mut RegisterPerm>)
        requires
            old(perm).view::<T>().id === self.reg_id(),
            old(perm).wf(),
            self.write_extra_requires(value, old(perm)@),
        ensures
            (perm).view::<T>().spec_write_value(old(perm)@, value),
            perm.wf(),
    ;
}

} // verus!
