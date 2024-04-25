use super::*;

verus! {

impl TLB {
    /// Load an entry
    #[verifier(inline)]
    pub open spec fn to_mem_map(&self, memid: MemID) -> MemMap<GuestVir, GuestPhy> {
        MemMap { db: self.spec_db()[memid] }
    }

    #[verifier(inline)]
    pub open spec fn load(&self, idx: TLBIdx, entry: SpecGuestPTEntry) -> Self {
        self.spec_set_db(self.spec_db().insert(idx.0, self.db[idx.0].insert(idx.1, entry)))
    }

    /// Remove an entry
    #[verifier(inline)]
    pub open spec fn invlpg(&self, idx: TLBIdx) -> Self {
        self.spec_set_db(self.spec_db().insert(idx.0, self.db[idx.0].remove(idx.1)))
    }

    /// Remove all entries for memid
    #[verifier(inline)]
    pub open spec fn flush_memid(&self, memid: MemID) -> Self {
        self.spec_set_db(self.spec_db().insert(memid, Map::empty()))
    }
}

} // verus!
