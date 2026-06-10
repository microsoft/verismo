use bitflags_verus::*;

bitflags_verus! {
    #[derive(Copy, Clone, Debug, Default)]
    pub struct Caps: isize {
        const NET   = 1 << 0;
        const DISK  = 1 << 1;
        const ADMIN = 1 << 2;
    }
}

verus! {

broadcast use bitflags_verus::bitflags_bit_lemmas_isize;

proof fn test_union(a: Caps, b: Caps) {
    let c = a.union(b);
    assert(c@ == a@ | b@);
}

proof fn test_intersection(a: Caps, b: Caps) {
    let c = a.intersection(b);
    assert(c@ == a@ & b@);
}

proof fn test_difference(a: Caps, b: Caps) {
    let c = a.difference(b);
    assert(c@ == a@ & !b@);
}

proof fn test_symmetric_difference(a: Caps, b: Caps) {
    let c = a.symmetric_difference(b);
    assert(c@ == a@ ^ b@);
}

proof fn test_complement(a: Caps) {
    let c = a.complement();
    assert(c@ == (!a@) & Caps::all()@);
}

proof fn test_contains(flags: Caps, check: Caps) {
    assert(flags.contains(check) == ((flags@ & check@) == check@));
}

proof fn test_empty() {
    let e = Caps::empty();
    assert(e@ == 0isize);
}

proof fn test_from_bits_retain(bits: isize) {
    let f = Caps::from_bits_retain(bits);
    assert(f@ == bits);
}

proof fn test_from_bits_truncate(bits: isize) {
    let f = Caps::from_bits_truncate(bits);
    assert(f@ == (bits & Caps::all()@));
}

fn test_insert_remove() {
    let mut p = Caps::empty();
    p.insert(Caps::NET);
    p.insert(Caps::DISK);
    proof {
        assert(p@ == (0isize | Caps::NET@) | Caps::DISK@);
    }
    assert(p.contains(Caps::DISK));

    let old_view = p.bits();
    p.remove(Caps::DISK);
    proof {
        assert(p@ == old_view & !Caps::DISK@);
        assert(p@ & Caps::DISK@ == 0isize);
    }
}

fn test_operators() {
    let a = Caps::NET;
    let b = Caps::ADMIN;
    let c = a | b;
    proof { assert(c@ == a@ | b@); }
    let d = c & a;
    proof { assert(d@ == c@ & a@); }
    let e = c - b;
    proof { assert(e@ == c@ & !b@); }
}

fn test_toggle() {
    let mut p = Caps::NET;
    let old_view = p.bits();
    let mask = Caps::NET | Caps::DISK;
    p.toggle(mask);
    proof {
        assert(p@ == old_view ^ mask@);
    }
}

fn test_set() {
    let mut p = Caps::empty();
    p.set(Caps::ADMIN, true);
    proof {
        assert(p@ == 0isize | Caps::ADMIN@);
    }
    let old_view = p.bits();
    p.set(Caps::ADMIN, false);
    proof {
        assert(p@ == old_view & !Caps::ADMIN@);
    }
}

} // verus!
