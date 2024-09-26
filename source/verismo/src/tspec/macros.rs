#[macro_export]
macro_rules! AsInt {
    ($val: expr) => {
        spec_cast_integer::<_, int>($val)
    };
}

#[macro_export]
macro_rules! AsNat {
    ($val: expr) => {
        spec_cast_integer::<_, nat>($val)
    };
}

#[macro_export]
macro_rules! addr2const {
    ($addr:expr, $t: ty) => {
        unsafe { &*($addr as *const $t) }
    };
}

#[macro_export]
macro_rules! addr2mut {
    ($addr:expr, $t: ty) => {
        unsafe { &mut *($addr as *mut $t) }
    };
}

#[macro_export]
macro_rules! struct2addr {
    ($data:expr) => {
        unsafe { &$data as *const _ as u64 }
    };
}

#[macro_export]
macro_rules! BITS_RANGE_MASK {
    ($first: expr, $last: expr) => {
        ((BIT!($last - $first + 1) - 1) << $first)
    };
}

#[macro_export]
macro_rules! BIT_FIELD_MAX_VAL {
    ($first: expr, $last: expr) => {
        BIT!($last - $first + 1)
    };
}

#[macro_export]
macro_rules! DEFINE_BITS_FIELD_GET {
    ($name: ident, $first: expr, $last: expr, $ty: tt) => {
        paste::paste! {
                                    #[inline]
                                    pub const fn [<get_ $name>](&self) -> $ty {
                                        ensures(|ret: $ty| ret == self.[<spec_get_ $name>]());
                                        let mask = BITS_RANGE_MASK!($first, $last);
                                        (self.value & mask) >> $first
                                    }
                                    verus!{
            pub open spec fn [<spec_get_ $name>](&self) -> $ty {
                let mask = BITS_RANGE_MASK!($first, $last);
                (self.value & mask) >> $first
            }
        }
                                }
    };
}

#[macro_export]
macro_rules! DEFINE_BIT_FIELD_GET {
    ($name: ident, $bit: expr) => {
        paste::paste! {
                                                verismo_non_secret!{
                                                    #[inline]
                                                    pub fn [<is_ $name>](&self) -> (ret: bool)
                                                    requires
                                                        $bit < 64
                                                    ensures
                                                        ret === self.[<spec_is_ $name>]()
                                                    {
                                                        bit_check(self.value, $bit)
                                                    }
                                                }

                                                verus!{
            #[verifier(inline)]
            pub open spec fn [<spec_is_ $name>](&self) -> bool
            {
                spec_has_bit_set(self.value.vspec_cast_to(), $bit)
            }
        }
                                            }
    };
}

#[macro_export]
macro_rules! DEFINE_BITS_FIELD_CONST {
    ($tyname: tt, $name: ident, $first: expr, $last: expr, $ty: tt) => {
        paste::paste! {
                                        pub const fn [<set_ $name>](&self, val: $ty) -> Self {
                                            requires([val < BIT_FIELD_MAX_VAL!($first, $last)]);
                                            ensures(|ret: $tyname|
                                                [builtin::equal(ret, self.[<spec_set_ $name>](val))]
                                            );
                                            let mask = BITS_RANGE_MASK!($first, $last);
                                            let value = self.value;
                                            let value = (value & !mask) | (val << $first);
                                            $tyname{value}
                                        }

                                       verus!{
        pub open spec fn [<spec_set_ $name>](&self, val: $ty) -> Self {
            let mask = BITS_RANGE_MASK!($first, $last);
            let value = self.value;
            let value = (value & !mask) | (val << ($first as $ty));
            $tyname{value}
        }
        }
                                   }
    };
}

#[macro_export]
macro_rules! DEFINE_BITS_FIELD {
    ($tyname: tt, $name: ident, $first: expr, $last: expr, $ty: tt) => {
        DEFINE_BITS_FIELD_CONST!($tyname, $name, $first, $last, $ty);

        DEFINE_BITS_FIELD_GET!($name, $first, $last, $ty);
    };
}
