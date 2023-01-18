use super::*;
verismo! {
    #[verifier(external_body)]
    pub fn default<T: Default + SpecDefault>() -> (ret: T)
    ensures
        ret === T::spec_default(),
    {
        T::default()
    }
}
