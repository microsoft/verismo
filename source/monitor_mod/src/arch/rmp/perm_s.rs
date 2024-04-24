use crate::arch::entities::VMPL;
use crate::tspec::*;

verus! {

#[is_variant]
pub enum Perm {
    Read,
    Write,
    ExeU,
    ExeS,
    Shadow,
}

pub type PagePerm = Set<Perm>;

impl IntValue for PagePerm {
    open spec fn as_int(&self) -> int {
        let v1: int = if self.contains(Perm::Read) {
            1
        } else {
            0
        };
        let v2: int = if self.contains(Perm::Write) {
            2
        } else {
            0
        };
        let v3: int = if self.contains(Perm::ExeU) {
            4
        } else {
            0
        };
        let v4: int = if self.contains(Perm::ExeS) {
            8
        } else {
            0
        };
        let v5: int = if self.contains(Perm::Shadow) {
            16
        } else {
            0
        };
        v1 + v2 + v3 + v4 + v5
    }

    open spec fn from_int(val: int) -> Set<Perm> {
        let ret = Set::empty();
        let ret = if val % 2 == 1 {
            ret.insert(Perm::Read)
        } else {
            ret
        };
        let ret = if (val / 2) % 2 == 1 {
            ret.insert(Perm::Write)
        } else {
            ret
        };
        let ret = if (val / 4) % 2 == 1 {
            ret.insert(Perm::ExeU)
        } else {
            ret
        };
        let ret = if (val / 8) % 2 == 1 {
            ret.insert(Perm::ExeS)
        } else {
            ret
        };
        let ret = if (val / 16) % 2 == 1 {
            ret.insert(Perm::Shadow)
        } else {
            ret
        };
        ret
    }
}

} // verus!
//#[derive(SpecGetter)]
pub type RmpPerm = Map<VMPL, PagePerm>;

verus! {

/// VMPL0 gets full permission by default, other VMPLs have none.
#[verifier(inline)]
pub open spec fn rmp_perm_init() -> RmpPerm {
    Map::new(
        |vmpl: VMPL| true,
        |vmpl: VMPL|
            if vmpl.is_VMPL0() {
                PagePerm::full()
            } else {
                PagePerm::empty()
            },
    )
}

#[verifier(inline)]
pub open spec fn rmp_perm_is_init(p: RmpPerm) -> bool {
    &&& p[VMPL::VMPL0] === PagePerm::full()
    &&& p[VMPL::VMPL1] === PagePerm::empty()
    &&& p[VMPL::VMPL2] === PagePerm::empty()
    &&& p[VMPL::VMPL3] === PagePerm::empty()
}

#[verifier(inline)]
pub open spec fn rmp_perm_is_valid(p: RmpPerm) -> bool {
    &&& p.index(VMPL::VMPL0) === PagePerm::full()
    &&& p.dom() === Set::full()
}

#[verifier(external_body)]
pub broadcast proof fn rmp_perm_track_dom(p: RmpPerm, vmpl: VMPL)
    ensures
        p.dom().contains(vmpl),
{
}

} // verus!
