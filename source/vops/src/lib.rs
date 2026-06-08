#![no_std]

pub trait VLt<Rhs> {
    fn lt(&self, rhs: &Rhs) -> bool
    where
        Self: core::marker::Sized;
}
pub trait VLe<Rhs> {
    fn le(&self, rhs: &Rhs) -> bool
    where
        Self: core::marker::Sized;
}
pub trait VGt<Rhs> {
    fn gt(&self, rhs: &Rhs) -> bool
    where
        Self: core::marker::Sized;
}
pub trait VGe<Rhs> {
    fn ge(&self, rhs: &Rhs) -> bool
    where
        Self: core::marker::Sized;
}
pub trait VEq<Rhs> {
    fn eq(&self, rhs: &Rhs) -> bool
    where
        Self: core::marker::Sized;
}
