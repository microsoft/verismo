use crate::tspec::*;

pub mod encdec;

verus! {
// crypto_mask is unknown and a perfect secret;
// key is the secret an attacker would like to know
// but would be reused for multiple plaintext.
// plaintext from victim is also a secret input.
// plaintext from attacker is attacker-controller inputs.
//
// Without crypto_mask, encryption does not hold noninterference property when considering the secret plaintext.
//
// With crypto_mask, we can recover the noninterference property by assuming decrypt will return a value related to crypto_mask.

pub struct CryptoMask(pub int);

pub struct SymKey<T> {
    pub key: T,
}

pub struct Encrypted<K, T> {
    pub data: T,
    pub key: K,
    pub crypto_mask: T,
}
}
