use vstd::prelude::*;

verus! {
    use super::name::*;
    use super::points_to::*;
    use super::value::*;

    /// Generic execution contract for a single machine register.
    pub trait AnyRegTrait<T> {
        /// The register this implementor reads/writes.
        spec fn reg_id(&self) -> RegName;

        /// The `RegisterValue` corresponding to `value` for this register.
        spec fn reg_value(&self, value: T) -> RegisterValue;

        /// Every value produced by `reg_value` is structurally tagged with `reg_id`.
        proof fn reg_value_id(&self, value: T)
            ensures self.reg_value(value).register_id() == self.reg_id();

        /// Read the current value of this register from its token.
        fn read(&self, Tracked(token): Tracked<&RegisterPointsTo>) -> (result: T)
            requires token.register_id() == self.reg_id(),
            ensures token.value() == self.reg_value(result);

        /// Write a new value to this register's token.
        fn write(&self, value: T, Tracked(token): Tracked<&mut RegisterPointsTo>)
            requires old(token).register_id() == self.reg_id(),
            ensures final(token).value() == self.reg_value(value),
                    final(token).register_id() == old(token).register_id();
    }
}
