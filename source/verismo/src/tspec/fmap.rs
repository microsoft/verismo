use super::*;

verus! {

#[derive(SpecGetter, SpecSetter)]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
pub struct FMap<K, V> {
    map: Map<K, V>,
}

impl<K, V> FMap<K, V> {
    #[verifier(external_body)]
    pub broadcast proof fn axiom_inv(&self, id: K)
        ensures
            (#[trigger] self.spec_map()[id]) === self.spec_map()[id],
            #[trigger] self.spec_map().dom().contains(id),
    {
    }

    #[verifier(inline)]
    pub open spec fn ext_equal(&self, other: Self) -> bool {
        self.spec_map() =~~= (other.spec_map())
    }

    #[verifier(external_body)]
    pub broadcast proof fn axiom_equal(&self, other: Self)
        ensures
            #[trigger] (*self =~~= other) == equal(*self, other),
            #[trigger] self.spec_map() =~~= (other.spec_map()) == equal(*self, other),
    {
    }

    #[verifier(inline)]
    pub open spec fn update(&self, fv: spec_fn(K) -> V) -> Self {
        self.spec_set_map(Map::new(|K| true, |k: K| fv(k)))
    }

    #[verifier(inline)]
    pub open spec fn insert(&self, k: K, v: V) -> Self {
        self.spec_set_map(self.spec_map().insert(k, v))
    }

    #[verifier(inline)]
    pub open spec fn dom(&self) -> Set<K> {
        self.spec_map().dom()
    }

    #[verifier(inline)]
    pub open spec fn union(&self, add: Map<K, V>) -> Self {
        self.spec_set_map(self.spec_map().union_prefer_right(add))
    }

    #[verifier(inline)]
    pub open spec fn spec_index(&self, k: K) -> V {
        self.spec_map().spec_index(k)
    }
}

} // verus!
