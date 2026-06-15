use bitflags_verus::*;

bitflags_verus! {
    #[derive(Copy, Clone, Debug, Default)]
    pub struct PageFlags: usize {
        const PRESENT  = 1 << 0;
        const WRITABLE = 1 << 1;
        const USER     = 1 << 2;
        const ACCESSED = 1 << 5;
        const DIRTY    = 1 << 6;
    }
}

verus! {

broadcast use bitflags_verus::bitflags_bit_lemmas_usize;

proof fn test_union(a: PageFlags, b: PageFlags) {
    let c = a.union(b);
    assert(c@ == a@ | b@);
}

proof fn test_intersection(a: PageFlags, b: PageFlags) {
    let c = a.intersection(b);
    assert(c@ == a@ & b@);
}

proof fn test_difference(a: PageFlags, b: PageFlags) {
    let c = a.difference(b);
    assert(c@ == a@ & !b@);
}

proof fn test_symmetric_difference(a: PageFlags, b: PageFlags) {
    let c = a.symmetric_difference(b);
    assert(c@ == a@ ^ b@);
}

proof fn test_complement(a: PageFlags) {
    let c = a.complement();
    assert(c@ == (!a@) & PageFlags::all()@);
}

proof fn test_contains(flags: PageFlags, check: PageFlags) {
    assert(flags.contains(check) == ((flags@ & check@) == check@));
}

proof fn test_empty() {
    let e = PageFlags::empty();
    assert(e@ == 0usize);
}

proof fn test_from_bits_retain(bits: usize) {
    let f = PageFlags::from_bits_retain(bits);
    assert(f@ == bits);
}

proof fn test_from_bits_truncate(bits: usize) {
    let f = PageFlags::from_bits_truncate(bits);
    assert(f@ == (bits & PageFlags::all()@));
}

fn test_insert_remove() {
    let mut p = PageFlags::empty();
    p.insert(PageFlags::PRESENT);
    p.insert(PageFlags::WRITABLE);
    proof {
        assert(p@ == (0usize | PageFlags::PRESENT@) | PageFlags::WRITABLE@);
    }
    assert(p.contains(PageFlags::WRITABLE));

    let old_view = p.bits();
    p.remove(PageFlags::WRITABLE);
    proof {
        assert(p@ == old_view & !PageFlags::WRITABLE@);
        assert(p@ & PageFlags::WRITABLE@ == 0usize);
    }
}

fn test_operators() {
    let a = PageFlags::PRESENT;
    let b = PageFlags::USER;
    let c = a | b;
    proof { assert(c@ == a@ | b@); }
    let d = c & a;
    proof { assert(d@ == c@ & a@); }
    let e = c - b;
    proof { assert(e@ == c@ & !b@); }
}

fn test_toggle() {
    let mut p = PageFlags::PRESENT;
    let old_view = p.bits();
    let mask = PageFlags::PRESENT | PageFlags::WRITABLE;
    p.toggle(mask);
    proof {
        assert(p@ == old_view ^ mask@);
    }
}

fn test_set() {
    let mut p = PageFlags::empty();
    p.set(PageFlags::ACCESSED, true);
    proof {
        assert(p@ == 0usize | PageFlags::ACCESSED@);
    }
    let old_view = p.bits();
    p.set(PageFlags::ACCESSED, false);
    proof {
        assert(p@ == old_view & !PageFlags::ACCESSED@);
    }
}

} // verus!
