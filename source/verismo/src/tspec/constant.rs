#[macro_export]
macro_rules! def_const_macro {
    ($($name:ident = $value:expr)+) => {
        $(
            #[allow(unused_attributes)]
            #[macro_export]
            macro_rules! $name {
                () => {
                    ($value)
                }
            }
        )+
    };
}

#[macro_export]
macro_rules! macro_const_int {
    ($($(#[$attr:meta])* $vis:vis const $name:ident : $type:ty = $value:expr ;)+) => {
        $(
            builtin_macros::verus!{
            #[allow(unused_attributes)]
            $( #[$attr] )* $vis const $name : $type = $value;
            }
#[allow(unused_attributes)]
            $( #[$attr] )*
            macro_rules! $name {
                () => {
                    builtin::spec_cast_integer::<_, int>($value)
                }
            }
        )+
    };
}
