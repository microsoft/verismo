use super::*;

verismo! {
pub fn sizeof<T: SpecSize>() -> (ret: usize)
ensures
    ret == spec_size::<T>()
{
    usize_s::constant(core::mem::size_of::<T>())
}

#[verifier(external_fn_specification)]
pub fn ex_size_of<T>() -> (size: usize)
    ensures size == spec_size::<T>()
{
    core::mem::size_of::<T>()
}

}
