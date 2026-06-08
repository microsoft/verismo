use super::*;

verismo! {
pub fn sizeof<T: SpecSize>() -> (ret: usize)
ensures
    ret == spec_size::<T>()
{
    usize_s::constant(core::mem::size_of::<T>())
}

}
