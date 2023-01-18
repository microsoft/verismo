use super::*;
use crate::tspec::*;

verus! {
    impl CryptoMask
    {
        pub spec fn get_mask<T>(&self) -> T;
    }
}

verus! {
    pub trait SpecEncrypt<T> {
        // crypto_mask is an unknown value to any entity.
        // crypto_mask ensures that the security of crypto is not broken.
        spec fn encrypt(&self, plain: T,  crypto_mask: T) -> Encrypted<Self, T>
        where Self: core::marker::Sized;

        // It is used to allow spec_decrypt return value not related to cipher.
        spec fn decrypt(&self, cipher: Encrypted<Self, T>) -> T
        where Self: core::marker::Sized;
    }


    impl<K, T> SpecEncrypt<T> for SymKey<K> {
        open spec fn encrypt(&self, plain: T, crypto_mask: T) -> Encrypted<Self, T>
        {
            Encrypted{
                data: plain,
                key: *self,
                crypto_mask: crypto_mask,
            }
        }

        open spec fn decrypt(&self, cipher: Encrypted<Self, T>) -> T
        {
            if cipher.key === *self {
                cipher.data
            } else {
                cipher.crypto_mask
            }
        }
    }


    pub trait SpecSignature<T> {
        spec fn spec_sign(&self) -> T
        where Self: core::marker::Sized;

        spec fn spec_verify(&self) -> bool
        where Self: core::marker::Sized;
    }
}
