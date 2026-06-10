use bitflags_verus::*;

bitflags_verus! {
    #[derive(Copy, Clone, Debug, Default)]
    pub struct Status32: i32 {
        const ACTIVE  = 1 << 0;
        const PENDING = 1 << 1;
        const ERROR   = 1 << 2;
    }
}

bitflags::bitflags! {
    #[derive(Copy, Clone, Debug, Default)]
    pub struct Status32_2: i32 {
        const ACTIVE  = 1 << 0;
        const PENDING = 1 << 1;
        const ERROR   = 1 << 2;
    }
}

verus! {

broadcast use bitflags_verus::bitflags_bit_lemmas_i32;

proof fn test_union(a: Status32, b: Status32) {
    let c = a.union(b);
    assert(c@ == a@ | b@);
}

proof fn test_intersection(a: Status32, b: Status32) {
    let c = a.intersection(b);
    assert(c@ == a@ & b@);
}

proof fn test_difference(a: Status32, b: Status32) {
    let c = a.difference(b);
    assert(c@ == a@ & !b@);
}

proof fn test_symmetric_difference(a: Status32, b: Status32) {
    let c = a.symmetric_difference(b);
    assert(c@ == a@ ^ b@);
}

proof fn test_complement(a: Status32) {
    let c = a.complement();
    assert(c@ == (!a@) & Status32::all()@);
}

proof fn test_contains(flags: Status32, check: Status32) {
    assert(flags.contains(check) == ((flags@ & check@) == check@));
}

proof fn test_empty() {
    let e = Status32::empty();
    assert(e@ == 0i32);
}

proof fn test_from_bits_retain(bits: i32) {
    let f = Status32::from_bits_retain(bits);
    assert(f@ == bits);
}

proof fn test_from_bits_truncate(bits: i32) {
    let f = Status32::from_bits_truncate(bits);
    assert(f@ == (bits & Status32::all()@));
}

fn test_insert_remove() {
    let mut p = Status32::empty();
    p.insert(Status32::ACTIVE);
    p.insert(Status32::PENDING);
    proof {
        assert(p@ == (0i32 | Status32::ACTIVE@) | Status32::PENDING@);
    }
    assert(p.contains(Status32::PENDING));

    let old_view = p.bits();
    p.remove(Status32::PENDING);
    proof {
        assert(p@ == old_view & !Status32::PENDING@);
        assert(p@ & Status32::PENDING@ == 0i32);
    }
}
fn test_operators() {
    let a = Status32::ACTIVE;
    let b = Status32::ERROR;
    let c = a | b;
    proof { assert(c@ == a@ | b@); }

    let d = c & a;
    proof { assert(d@ == c@ & a@); }
    let e = c - b;
    proof { assert(e@ == c@ & !b@); }
}

fn test_toggle() {
    let mut p = Status32::ACTIVE;
    let old_view = p.bits();
    let mask = Status32::ACTIVE | Status32::PENDING;
    p.toggle(mask);
    proof {
        assert(p@ == old_view ^ mask@);
    }
}

fn test_set() {
    let mut p = Status32::empty();
    p.set(Status32::ERROR, true);
    proof {
        assert(p@ == 0i32 | Status32::ERROR@);
    }
    let old_view = p.bits();
    p.set(Status32::ERROR, false);
    proof {
        assert(p@ == old_view & !Status32::ERROR@);
    }
}

} // verus!
