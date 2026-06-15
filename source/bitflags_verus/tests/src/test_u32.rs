use bitflags_verus::*;

bitflags_verus! {
    #[derive(Copy, Clone, Debug, Default)]
    pub struct Perms32: u32 {
        const READ    = 1 << 0;
        const WRITE   = 1 << 1;
        const EXECUTE = 1 << 2;
    }
}

verus! {

broadcast use bitflags_verus::bitflags_bit_lemmas_u32;

proof fn test_union(a: Perms32, b: Perms32) {
    let c = a.union(b);
    assert(c@ == a@ | b@);
}

proof fn test_intersection(a: Perms32, b: Perms32) {
    let c = a.intersection(b);
    assert(c@ == a@ & b@);
}

proof fn test_difference(a: Perms32, b: Perms32) {
    let c = a.difference(b);
    assert(c@ == a@ & !b@);
}

proof fn test_symmetric_difference(a: Perms32, b: Perms32) {
    let c = a.symmetric_difference(b);
    assert(c@ == a@ ^ b@);
}

proof fn test_complement(a: Perms32) {
    let c = a.complement();
    assert(c@ == (!a@) & Perms32::all()@);
}

proof fn test_contains(flags: Perms32, check: Perms32) {
    assert(flags.contains(check) == ((flags@ & check@) == check@));
}

proof fn test_empty() {
    let e = Perms32::empty();
    assert(e@ == 0u32);
}

proof fn test_from_bits_retain(bits: u32) {
    let f = Perms32::from_bits_retain(bits);
    assert(f@ == bits);
}

proof fn test_from_bits_truncate(bits: u32) {
    let f = Perms32::from_bits_truncate(bits);
    assert(f@ == (bits & Perms32::all()@));
}

fn test_insert_remove() {
    let mut p = Perms32::empty();
    p.insert(Perms32::READ);
    p.insert(Perms32::WRITE);
    proof {
        assert(p@ == (0u32 | Perms32::READ@) | Perms32::WRITE@);
    }
    assert(p.contains(Perms32::WRITE));

    let old_view = p.bits();
    p.remove(Perms32::WRITE);
    proof {
        assert(p@ == old_view & !Perms32::WRITE@);
        assert(p@ & Perms32::WRITE@ == 0u32);
    }
}

fn test_operators() {
    let a = Perms32::READ;
    let b = Perms32::WRITE;
    let c = a | b;
    proof { assert(c@ == a@ | b@); }
    let d = c & a;
    proof { assert(d@ == c@ & a@); }
    let e = c - b;
    proof { assert(e@ == c@ & !b@); }
}

fn test_toggle() {
    let mut p = Perms32::READ;
    let old_view = p.bits();
    let mask = Perms32::READ | Perms32::WRITE;
    p.toggle(mask);
    proof {
        assert(p@ == old_view ^ mask@);
    }
}

fn test_set() {
    let mut p = Perms32::empty();
    p.set(Perms32::EXECUTE, true);
    proof {
        assert(p@ == 0u32 | Perms32::EXECUTE@);
    }
    let old_view = p.bits();
    p.set(Perms32::EXECUTE, false);
    proof {
        assert(p@ == old_view & !Perms32::EXECUTE@);
    }
}

} // verus!
