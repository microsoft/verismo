use super::*;
verismo_simple! {
pub struct VCell<T> {
    ucell: T,
}

impl<T> VCell<T> {
    pub const fn new(val: T) -> Self
    {
        VCell {
            ucell: val
        }
    }
}
}
