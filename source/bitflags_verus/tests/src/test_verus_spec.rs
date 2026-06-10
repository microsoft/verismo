use bitflags_verus::*;

bitflags_verus! {
    #[derive(Copy, Clone, Debug, Default)]
    pub struct Permissions: u32 {
        const READ    = 1 << 0;
        const WRITE   = 1 << 1;
        const EXECUTE = 1 << 2;
    }
}

verus! {
    broadcast use bitflags_verus::bitflags_bit_lemmas_u32;
}

#[verus_spec(
    ensures *final(perms) == spec_union(*old(perms), Permissions::READ),
)]
fn grant_read(perms: &mut Permissions) {
    perms.insert(Permissions::READ);
}

#[verus_spec(
    ensures *final(perms) == spec_difference(*old(perms), Permissions::WRITE),
)]
fn revoke_write(perms: &mut Permissions) {
    perms.remove(Permissions::WRITE);
}

#[verus_spec(ret =>
    ensures ret == ((perms@ & Permissions::EXECUTE@) == Permissions::EXECUTE@),
)]
fn has_execute(perms: &Permissions) -> bool {
    perms.contains(Permissions::EXECUTE)
}
