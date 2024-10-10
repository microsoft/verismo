use super::*;
use crate::debug::VPrintAtLevel;
use crate::global::{spec_ALLOCATOR, spec_CONSOLE, spec_PT};
use crate::pgtable_e::*;
use crate::snp::mem::*;

macro_rules! BIT8 {
    ($x: expr) => {
        (1u8 << ($x))
    };
}

verismo_simple! {

#[derive(SpecGetter, SpecSetter, Copy, VClone)]
#[repr(C, align(1))]
pub struct GhcbVmsa {
    pub reserved_0: Array<u8, 0x0CB>,
    #[def_offset]
    pub cpl: u8, // 0x0CBh
    pub reserved_2: Array<u8, 0x12c>, // 0x1F8 - 0xcb - 1

    #[def_offset]
    pub rax: u64, // 0x1f8

    pub reserved2: Array<u8, 0x108>, // (0x308 - 0x1F8 - 8)

    #[def_offset]
    pub rcx: u64, // 0x308
    #[def_offset]
    pub rdx: u64,
    #[def_offset]
    pub rbx: u64,

    pub reserved3: Array<u8, 32>,
    #[def_offset]
    pub r8: u64,
    pub reserved4: Array<u8, 0x48>, // (0x390 - 0x308 - 24 - 40)

    #[def_offset]
    pub sw_exit_code: u64,
    #[def_offset]
    pub sw_exit_info_1: u64,
    #[def_offset]
    pub sw_exit_info_2: u64,
    #[def_offset]
    pub sw_scratch: u64,

    pub reserved5: Array<u8, 16>,

    #[def_offset]
    pub guest_error_code: u64,

    pub reserved_6: Array<u8, 32>,
    #[def_offset]
    pub xcr0: u64,
}

#[repr(C, align(1))]
#[derive(SpecSetter, SpecGetter)]
pub struct GhcbPage {
    #[def_offset]
    vmsa: GhcbVmsa,
    valid_bitmap: [u8; 16],
    reserved6: [u8; 1024],
    #[def_offset]
    shared_buffer: [u8; GHCB_BUFFER_SIZE],
    reserved7: [u8; 10],
    version: u16,
    #[def_offset]
    usage: u32,
}

impl VBox<GhcbPage> {
    pub fn set_usage_ext(&mut self, usage: u32)
    requires
        old(self).is_constant(),
        usage.is_constant(),
        old(self).ghcb_wf(),
    ensures
        self.is_constant(),
        self.only_val_updated(*old(self)),
        self@ === old(self)@.spec_set_usage(usage),
        self.ghcb_wf(),
    {
        self.set_usage(usage);
    }
}
}

verus! {

proof fn proof_ghcb_size()
    ensures
        spec_size::<GhcbPage>() == PAGE_SIZE!(),
        spec_size::<GhcbVmsa>() == 0x03f0,
        GhcbVmsa::spec_rax_offset() < 0x400,
        GhcbVmsa::spec_rcx_offset() < 0x400,
        GhcbVmsa::spec_rdx_offset() < 0x400,
        GhcbVmsa::spec_sw_exit_code_offset() < 0x400,
{
}

} // verus!
macro_rules! ghcb_fns {
    ($name: ident, $valty: tt) => {
        paste::paste! {verus!{
        #[inline]
        pub fn [<set_bitmap_ $name>](&mut self)
        requires
            old(self).is_constant(),
        ensures
            self.is_constant(),
            *self === old(self).spec_set_valid_bitmap(self.spec_valid_bitmap()),
            ensure_set_bitmap(self.spec_valid_bitmap()@, old(self).spec_valid_bitmap()@, GhcbVmsa::[<spec_ $name _offset>]()),
        {
            proof {proof_ghcb_size();}
            assert(GhcbVmsa::[<spec_ $name _offset>]() < 0x400);
            self.set_offset_valid(GhcbVmsa::[<_ $name _offset>]());
        }

        #[inline]
        pub fn [<is_ $name _valid>](&self) -> (ret: bool)
        requires
            self.is_constant(),
        ensures
            ret == ensures_offset_valid(self.spec_valid_bitmap()@, GhcbVmsa::[<spec_ $name _offset>]())
        {
            proof {proof_ghcb_size();}
            assert(GhcbVmsa::[<spec_ $name _offset>]() < 0x400);
            self.is_offset_valid(GhcbVmsa::[<_ $name _offset>]())
        }
        }
}
    };
}

macro_rules! ghcb_fns_u64 {
    ($name: ident) => {
        ghcb_fns! {$name, u64}
    };
}

macro_rules! ghcb_box_fn {
($fnname: ident, $inputty: ident, $checkname: ident, $fieldt: ty, $fieldname: ident) => {
    paste::paste! {
    verus!{
        pub struct $fnname;
        pub type $inputty = ($fnname, $fieldt);
    }
    verus!{
    impl VBox<GhcbPage> {
        pub fn $fieldname(self) -> (ret: ($fieldt, Self))
        requires
            self.ghcb_wf(),
        ensures
            ret.1.spec_eq(self),
        {
            let (ghcb_ptr, Tracked(mut ghcb_perm)) = self.into_raw();
            assert(ghcb_perm@.snp() === SwSnpMemAttr::shared());
            let (val, Tracked(ghcb_perm)) = ghcb_ptr.vmsa().$fieldname().copy_with::<GhcbPage>(Tracked(ghcb_perm));
            let ghcb = VBox::from_raw(ghcb_ptr.to_usize(), Tracked(ghcb_perm));
            (val.into(), ghcb)
        }
    }}
    verismo_simple! {
    impl GhcbPage {
        pub closed spec fn [<ensures_set_ $fieldname>](&self, prev: Self, params: $inputty) -> bool {
            &&& self.vmsa.$fieldname == params.1
            &&& *self === prev.spec_set_valid_bitmap(self.valid_bitmap).spec_set_vmsa(self.vmsa)
            &&& ensures_offset_valid(self.valid_bitmap@, GhcbVmsa::[<spec_ $fieldname _offset>]())
        }
    }
    impl<'a> MutFnTrait<'a, $inputty, bool> for GhcbPage {
        open spec fn spec_update_requires(&self, params: $inputty) -> bool {
            &&&self.is_constant()
            &&&params.1.is_constant()
        }

        open spec fn spec_update(&self, prev: &Self, params: $inputty, ret: bool) -> bool {
            &&& self.is_constant()
            &&& self.[<ensures_set_ $fieldname>](*prev, params)
            &&& ret
        }

        #[inline]
        fn box_update(&'a mut self, params: $inputty) -> (ret: bool)
        {
            self.[<set_bitmap_ $fieldname>]();
            self.vmsa.$fieldname = params.1.into();
            true
        }
    }

    pub struct $checkname;

    impl<'a> BorrowFnTrait<'a, $checkname, bool> for GhcbPage {
        fn box_borrow(&'a self, params: $checkname) -> (ret: bool)
        {
            proof {proof_ghcb_size();}
            assert(GhcbVmsa::[<spec_ $fieldname _offset>]() < 0x400);
            self.is_offset_valid(GhcbVmsa::[<_ $fieldname _offset>]())
        }

        open spec fn spec_borrow_requires(&self, params: $checkname) -> bool {
            self.is_constant()
        }

        closed spec fn spec_borrow_ensures(&self, params: $checkname, ret: bool) -> bool {
            ret == ensures_offset_valid(self.spec_valid_bitmap()@, GhcbVmsa::[<spec_ $fieldname _offset>]())
        }
    }
    }
}
}
}

verus! {

pub closed spec fn ensures_offset_valid(cur: Seq<u8_s>, offset: nat) -> bool {
    let i: int = ((offset / 8) / 8) as int;
    let bit: u8 = ((offset / 8) % 8) as u8;
    let bits: u8 = cur[i].vspec_cast_to();
    bits & BIT8!(bit) != 0
}

pub closed spec fn ensure_set_bitmap(cur: Seq<u8_s>, prev: Seq<u8_s>, offset: nat) -> bool {
    let i: int = ((offset / 8) / 8) as int;
    let bit: u8 = ((offset / 8) % 8) as u8;
    let bits: u8 = cur[i].vspec_cast_to();
    let prev_bits: u8 = prev[i].vspec_cast_to();
    &&& forall|j| 0 <= j < 16 && j != i ==> cur[j] === prev[j]
    &&& bits == (prev_bits | BIT8!(bit))
    &&& ensures_offset_valid(cur, offset)
}

#[verifier(bit_vector)]
proof fn lemma_bit8_set2(val: u8, b1: u8, b2: u8)
    requires
        0 <= b1 < 8,
        0 <= b2 < 8,
    ensures
        b1 != b2 ==> (val & (1 << b1) != 0) == ((val | (1 << b2)) & (1 << b1) != 0),
        (val | (1 << b2)) & (1 << b2) != 0,
{
}

#[verifier(bit_vector)]
proof fn lemma_bit8_setbit(val: u8, b1: u8)
    requires
        0 <= b1 < 8,
    ensures
        (val | (1 << b1)) & (1 << b1) != 0,
{
}

proof fn proof_bit8_setbit()
    ensures
        forall|val: u8, b1: u8| 0 <= b1 < 8 ==> (val | (1 << b1)) & (1 << b1) != 0,
        forall|val: u8, b1: u8, b2: u8|
            0 <= b1 < 8 && 0 <= b2 < 8 ==> ((val | (1 << b2)) & (1 << b1) != 0) == ((val & (1 << b1)
                != 0) || (b1 == b2)),
{
    assert forall|val: u8, b1: u8| 0 <= b1 < 8 implies (val | (1 << b1)) & (1 << b1) != 0 by {
        lemma_bit8_setbit(val, b1)
    }
    assert forall|val: u8, b1: u8, b2: u8| 0 <= b1 < 8 && 0 <= b2 < 8 implies ((val | (1 << b2)) & (
    1 << b1) != 0) == ((val & (1 << b1) != 0) || b1 == b2) by {
        lemma_bit8_set2(val, b1, b2);
    }
}

} // verus!
verus! {

impl GhcbPage {
    pub closed spec fn ensure_clear(&self) -> bool {
        forall|i| 0 <= i < 16 ==> self.valid_bitmap@[i] === u8_s::spec_constant(0)
    }

    pub fn clear(&mut self)
        requires
            old(self).is_constant(),
        ensures
            self.is_constant(),
            self.ensure_clear(),
            *self === old(self).spec_set_valid_bitmap(self.spec_valid_bitmap()),
    {
        // Clear valid bitmap
        self.valid_bitmap.memset(0u8.into());
    }

    pub fn set_offset_valid(&mut self, offset: usize)
        requires
            old(self).is_constant(),
            offset < 0x400,
        ensures
            self.is_constant(),
            ensure_set_bitmap(
                self.spec_valid_bitmap()@,
                old(self).spec_valid_bitmap()@,
                offset as nat,
            ),
            ensures_offset_valid(self.spec_valid_bitmap()@, offset as nat),
            *self === old(self).spec_set_valid_bitmap(self.spec_valid_bitmap()),
    {
        let i: usize = ((offset / 8) / 8) as u8 as usize;
        assert(i == (offset / 8) / 8);
        let bit: u8 = ((offset / 8) % 8) as u8;
        let oldv: u8 = (*self.valid_bitmap.index(i)).into();
        let newv = oldv | BIT8!(bit);
        proof {
            lemma_bit8_setbit(oldv, bit);
        }
        self.valid_bitmap.set(i, newv.into());
    }

    pub fn is_offset_valid(&self, offset: usize) -> (ret: bool)
        requires
            self.is_constant(),
            offset < 0x400,
        ensures
            ret == ensures_offset_valid(self.spec_valid_bitmap()@, offset as nat),
    {
        let idx: usize = ((offset / 8) / 8) as usize;
        let bit: u8 = ((offset / 8) % 8) as u8;
        let v: u8 = (*self.valid_bitmap.index(idx)).into();
        (v & BIT8!(bit)) != 0
    }
}

} // verus!
verus! {

impl GhcbPage {
    ghcb_fns_u64!{rax}

    ghcb_fns_u64!{rbx}

    ghcb_fns_u64!{rcx}

    ghcb_fns_u64!{rdx}

    ghcb_fns_u64!{r8}

    ghcb_fns!{cpl, u8}

    ghcb_fns_u64!{sw_exit_code}

    ghcb_fns_u64!{sw_exit_info_1}

    ghcb_fns_u64!{sw_exit_info_2}

    ghcb_fns_u64!{sw_scratch}
}

} // verus!
use crate::vbox::MutFnTrait;

verus! {

pub struct FillGhcbFn;

pub type FillGhcb = (FillGhcbFn, u64, u64, u64);

impl GhcbPage {
    closed spec fn ensure_fill_ghcb(&self, params: FillGhcb) -> bool {
        &&& self.vmsa.sw_exit_code@.val == params.1
        &&& self.vmsa.sw_exit_info_1@.val == params.2
        &&& self.vmsa.sw_exit_info_2@.val == params.3
        &&& ensures_offset_valid(self.spec_valid_bitmap()@, GhcbVmsa::spec_sw_exit_code_offset())
        &&& ensures_offset_valid(self.spec_valid_bitmap()@, GhcbVmsa::spec_sw_exit_info_1_offset())
        &&& ensures_offset_valid(self.spec_valid_bitmap()@, GhcbVmsa::spec_sw_exit_info_2_offset())
    }
}

impl<'a> MutFnTrait<'a, FillGhcb, bool> for GhcbPage {
    open spec fn spec_update_requires(&self, params: FillGhcb) -> bool {
        self.is_constant()
    }

    closed spec fn spec_update(&self, prev: &Self, params: FillGhcb, ret: bool) -> bool {
        &&& self.is_constant()
        &&& self.ensure_fill_ghcb(params)
        &&& ret
    }

    fn box_update(&'a mut self, params: FillGhcb) -> (ret: bool) {
        self.usage = GHCB_DEFAULT_USAGE.into();
        self.version = GHCB_VERSION_1.into();
        self.set_bitmap_sw_exit_code();
        self.vmsa.sw_exit_code = params.1.into();
        self.set_bitmap_sw_exit_info_1();
        self.vmsa.sw_exit_info_1 = params.2.into();
        self.set_bitmap_sw_exit_info_2();
        self.vmsa.sw_exit_info_2 = params.3.into();
        proof {
            proof_bit8_setbit();
        }
        true
    }
}

} // verus!
verus! {

pub struct GhcbClear;

impl<'a> MutFnTrait<'a, GhcbClear, bool> for GhcbPage {
    open spec fn spec_update_requires(&self, params: GhcbClear) -> bool {
        self.is_constant()
    }

    open spec fn spec_update(&self, prev: &Self, params: GhcbClear, ret: bool) -> bool {
        &&& self.is_constant()
        &&& forall|i| 0 <= i < 16 ==> self.spec_valid_bitmap()@[i] === u8_s::spec_constant(0)
        &&& *self === prev.spec_set_valid_bitmap(self.spec_valid_bitmap())
        &&& ret
    }

    fn box_update(&'a mut self, params: GhcbClear) -> (ret: bool) {
        self.clear();
        true
    }
}

} // verus!
//($fnname: ident, $inputty: ident, $fieldt: ty, $fieldname: ident)
ghcb_box_fn! {GhcbSetRcxFn, GhcbSetRcx, GhcbCheckRcx, u64 ,rcx}
ghcb_box_fn! {GhcbSetRaxFn, GhcbSetRax, GhcbCheckRax, u64, rax}
ghcb_box_fn! {GhcbSetRdxFn, GhcbSetRdx, GhcbCheckRdx, u64, rdx}
ghcb_box_fn! {GhcbSetSwScratchFn, GhcbSetSwScratch, GhcbCheckSwScratch, u64, sw_scratch}
ghcb_box_fn! {GhcbSetR8Fn, GhcbSetR8, GhcbCheckR8x, u64, r8}
ghcb_box_fn! {GhcbSetCplFn, GhcbSetCpl, GhcbCheckCpl, u8, cpl}

verus! {

pub closed spec fn _ghcb_wf(id: int, snp: SwSnpMemAttr) -> bool {
    open_ghcb_wf(id, snp)
}

pub open spec fn open_ghcb_wf(id: int, snp: SwSnpMemAttr) -> bool {
    &&& snp === SwSnpMemAttr::shared()
    &&& id % PAGE_SIZE!() == 0
}

impl VBox<GhcbPage> {
    pub open spec fn ghcb_wf(&self) -> bool {
        &&& self@.is_constant()
        &&& _ghcb_wf(self.id(), self.snp())
    }

    pub proof fn proof_ghcb_wf(&self)
        ensures
            self.ghcb_wf() == (open_ghcb_wf(self.id(), self.snp()) && self@.is_constant()),
    {
    }

    pub fn ghcb_change_page_state_via_pg(
        self,
        ppage: u64,
        npages: u64,
        op: PageOps,
        Tracked(page_perms): Tracked<&mut Map<int, SnpPointsToRaw>>,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
    ) -> (ret: VBox<GhcbPage>)
        requires
            self.ghcb_wf(),
            (*old(cs)).inv(),
            spec_valid_page_state_change(ppage, npages as nat),
            requires_pages_perms(*old(page_perms), ppage as int, npages as nat),
            forall|i|
                ppage <= i < (ppage + npages) ==> old(page_perms).contains_key(i) && (
                #[trigger] old(page_perms)[i])@.wf_range((i.to_addr(), PAGE_SIZE as nat)),
        ensures
            ret.only_val_updated(self),
            ret.ghcb_wf(),
            cs.inv(),
            cs.only_lock_reg_coremode_updated((*old(cs)), set![], set![]),
            ensure_pages_perm_change_state(
                *old(page_perms),
                *page_perms,
                ppage as int,
                npages as nat,
                op,
            ),
            forall|i|
                ppage <= i < (ppage + npages) ==> #[trigger] page_perms.contains_key(i)
                    && ensure_page_perm_change_state(old(page_perms)[i], page_perms[i], i, op),
    {
        let (ghcb_ptr, Tracked(ghcbpage_perm)) = self.into_raw();
        let tracked mut ghcbpage_perm0 = Map::tracked_empty();
        proof {
            ghcbpage_perm0.tracked_insert(0, ghcbpage_perm);
        }
        ghcb_change_page_state_via_pg(
            ghcb_ptr.clone(),
            ppage,
            npages,
            op,
            Tracked(page_perms),
            Tracked(&mut ghcbpage_perm0),
            Tracked(cs),
        );
        VBox::from_raw(ghcb_ptr.to_usize(), Tracked(ghcbpage_perm0.tracked_remove(0)))
    }

    pub fn alloc_ghcb_handle(Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (ghcb: Self)
        requires
            (*old(cs)).inv(),
        ensures
            ghcb.ghcb_wf(),
            cs.inv(),
            cs.only_lock_reg_coremode_updated(
                (*old(cs)),
                set![GHCB_REGID()],
                set![spec_ALLOCATOR().lockid(), spec_PT().lockid()],
            ),
    {
        let ghost cs1 = *cs;
        let ghcb = GhcbHandle::new_aligned_uninit(PAGE_SIZE, Tracked(cs));
        let ghost cs2 = *cs;
        let (ghcb_ptr, Tracked(ghcb_perm)) = ghcb.into_raw();
        let tracked mut ghcb_perm = ghcb_perm.tracked_into_raw();
        let Tracked(ghcb_perm) = init_ghcb_page(ghcb_ptr.clone(), Tracked(ghcb_perm), Tracked(cs));
        proof {
            let ghost cs3 = *cs;
            cs1.lemma_update_prop(
                cs2,
                cs3,
                set![],
                set![spec_ALLOCATOR().lockid()],
                set![GHCB_REGID()],
                set![spec_PT().lockid()],
            );
            assert(set![spec_ALLOCATOR().lockid()].union(set![spec_PT().lockid()])
                =~~= set![spec_ALLOCATOR().lockid(), spec_PT().lockid()]);
        }
        VBox::from_raw(ghcb_ptr.to_usize(), Tracked(ghcb_perm.trusted_into()))
    }

    pub fn new_ghcb_handle(
        ghcb_ptr: SnpPPtr<GhcbPage>,
        Tracked(page_perm): Tracked<SnpPointsToRaw>,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
    ) -> (ghcb: Self)
        requires
            page_perm@.wf_const_default((ghcb_ptr.id(), PAGE_SIZE as nat)),
            ghcb_ptr.is_constant(),
            ghcb_ptr.id() % PAGE_SIZE!() == 0,
            (*old(cs)).inv(),
        ensures
            ghcb.ghcb_wf(),
    {
        let Tracked(ghcb_perm) = init_ghcb_page(ghcb_ptr.clone(), Tracked(page_perm), Tracked(cs));
        VBox::from_raw(ghcb_ptr.to_usize(), Tracked(ghcb_perm.trusted_into()))
    }

    pub fn ghcb_page_proto(
        self,
        exit: &mut u64,
        exit1: &mut u64,
        exit2: &mut u64,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
    ) -> (ret: (SvmStatus, Self))
        requires
            (*old(cs)).inv(),
            self.ghcb_wf(),
        ensures
            ret.1.only_val_updated(self),
            ret.1.ghcb_wf(),
            cs.inv(),
            cs.only_lock_reg_coremode_updated((*old(cs)), set![], set![]),
    {
        let ghost oldcs = *cs;
        let tracked mut ghcb_msr_perm = cs.snpcore.regs.tracked_remove(GHCB_REGID());
        let ghost oldghcb_msr_perm = ghcb_msr_perm;
        let mut ghcb = self;
        let ghcb_addr = ghcb.get_const_addr() as u64;
        if !MSR_GHCB().read(Tracked(&ghcb_msr_perm)).eq(&ghcb_addr) {
            proof {
                cs.snpcore.regs.tracked_insert(GHCB_REGID(), ghcb_msr_perm);
            }
            vc_terminate(SM_TERM_NO_GHCB, Tracked(&mut cs.snpcore));
        }
        ghcb.box_update((FillGhcbFn, *exit, *exit1, *exit2));
        let (ghcb_ptr, Tracked(mut ghcbpage_perm)) = ghcb.into_raw();
        let tracked mut op_ghcbpage_perm = Some(ghcbpage_perm.tracked_into_raw());
        vmgexit(
            Tracked(&mut ghcb_msr_perm),
            Tracked(&mut cs.snpcore.coreid),
            Tracked(&mut op_ghcbpage_perm),
        );
        if !MSR_GHCB().read(Tracked(&ghcb_msr_perm)).eq(&ghcb_ptr.as_u64()) {
            proof {
                cs.snpcore.regs.tracked_insert(GHCB_REGID(), ghcb_msr_perm);
            }
            vc_terminate(SM_TERM_NO_GHCB, Tracked(&mut cs.snpcore));
        }
        proof {
            cs.snpcore.regs.tracked_insert(GHCB_REGID(), ghcb_msr_perm);
            assert(cs.snpcore.regs[GHCB_REGID()] === (*old(cs)).snpcore.regs[GHCB_REGID()]);
            assert(cs.snpcore.regs =~~= (*old(cs)).snpcore.regs);
            assert(cs.only_lock_reg_coremode_updated((*old(cs)), set![], set![]));
            ghcbpage_perm = op_ghcbpage_perm.tracked_unwrap().tracked_into();
        }
        let ghost prevcs = *cs;
        // HV-shared memory should be copied or moved and cannot be borrowed.
        let (exit_info_1, Tracked(ghcbpage_perm)) = ghcb_ptr.vmsa().sw_exit_info_1().copy_with::<
            GhcbPage,
        >(Tracked(ghcbpage_perm));
        let (exit_info_2, Tracked(ghcbpage_perm)) = ghcb_ptr.vmsa().sw_exit_info_2().copy_with::<
            GhcbPage,
        >(Tracked(ghcbpage_perm));
        let (sw_exit_code, Tracked(ghcbpage_perm)) = ghcb_ptr.vmsa().sw_exit_code().copy_with::<
            GhcbPage,
        >(Tracked(ghcbpage_perm));
        let exit_info_1: u64 = exit_info_1.into();
        let exit_info_2: u64 = exit_info_2.into();
        let ghcb = VBox::from_raw(ghcb_addr as usize, Tracked(ghcbpage_perm));
        let err = if (exit_info_1 & 0xffffffff) == 1 {
            let vec = SVM_EVTINJ_VEC_MASK!(exit_info_2);
            let ty = SVM_EVTINJ_TYPE_MASK!(exit_info_2);
            let valid = SVM_EVTINJ_IS_VALID!(exit_info_2);
            if valid && (ty == SVM_EVTINJ_TYPE_EXEPT) && (vec == SVM_EVTINJ_VEC_X86_TRAP_GP || vec
                == SVM_EVTINJ_VEC_X86_TRAP_UD) {
                SvmStatus::Exception
            } else {
                SvmStatus::VmmError
            }
        } else {
            *exit = sw_exit_code.into();
            *exit1 = exit_info_1;
            *exit2 = exit_info_2;
            SvmStatus::Ok
        };
        new_strlit("ghcb_page_proto\n").leak_debug();
        (err, ghcb)
    }

    pub fn ghcb_read_msr(self, reg: u32, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (ret: (
        u64,
        Self,
    ))
        requires
            self.ghcb_wf(),
            (*old(cs)).inv(),
        ensures
            cs.inv(),
            cs.only_lock_reg_coremode_updated((*old(cs)), set![], set![]),
            ret.1.only_val_updated(self),
            ret.1.ghcb_wf(),
    {
        let mut ghcb = self;
        ghcb.box_update(GhcbClear);
        ghcb.box_update((GhcbSetRcxFn, reg as u64));
        let mut exit_code = SVM_EXIT_MSR;
        let mut exit_info1 = 0;
        let mut exit_info2 = 0;
        let (resp, mut ghcb) = ghcb.ghcb_page_proto(
            &mut exit_code,
            &mut exit_info1,
            &mut exit_info2,
            Tracked(cs),
        );
        let mut rax: u64 = 0;
        let mut rdx: u64 = 0;
        match resp {
            SvmStatus::Ok => {
                // Cannot borrow Hv-shared memory. Copy to private.
                let (ghcb_ptr, Tracked(ghcb_perm)) = ghcb.into_raw();
                let (ax, Tracked(ghcb_perm)) = ghcb_ptr.vmsa().rax().copy_with::<GhcbPage>(
                    Tracked(ghcb_perm),
                );
                let (dx, Tracked(ghcb_perm)) = ghcb_ptr.vmsa().rax().copy_with::<GhcbPage>(
                    Tracked(ghcb_perm),
                );
                rax = ax.into();
                rdx = dx.into();
                ghcb = VBox::from_raw(ghcb_ptr.to_usize(), Tracked(ghcb_perm));
            },
            _ => {
                vc_terminate(SM_TERM_GHCB_RESP_INVALID, Tracked(&mut cs.snpcore));
            },
        }
        return ((rax as u32 as u64) | ((rdx as u32 as u64) << 32u64), ghcb);
    }

    pub fn ghcb_write_msr(
        self,
        reg: u32,
        val: u64,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
    ) -> (ret: Self)
        requires
            self.ghcb_wf(),
            (*old(cs)).inv(),
        ensures
            ret.only_val_updated(self),
            ret.ghcb_wf(),
            cs.inv(),
            cs.only_lock_reg_coremode_updated((*old(cs)), set![], set![]),
    {
        let mut ghcb = self;
        ghcb.box_update(GhcbClear);
        ghcb.box_update((GhcbSetRcxFn, reg as u64));
        ghcb.box_update((GhcbSetRaxFn, val as u32 as u64));
        ghcb.box_update((GhcbSetRdxFn, (val >> 32u64)));
        let mut exit_code = SVM_EXIT_MSR;
        let mut exit_info1 = 1;
        let mut exit_info2 = 0;
        let (resp, ghcb) = ghcb.ghcb_page_proto(
            &mut exit_code,
            &mut exit_info1,
            &mut exit_info2,
            Tracked(cs),
        );
        match resp {
            SvmStatus::Ok => {},
            _ => {
                vc_terminate(SM_TERM_GHCB_RESP_INVALID, Tracked(&mut cs.snpcore));
            },
        }
        ghcb
    }

    pub fn ghcb_guest_request(
        self,
        req_gpa: u64,
        resp_gpa: u64,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
    ) -> (ret: Self)
        requires
            (*old(cs)).inv(),
            self.ghcb_wf(),
        ensures
            ret.only_val_updated(self),
            ret.ghcb_wf(),
            cs.inv(),
            cs.only_lock_reg_coremode_updated((*old(cs)), set![], set![]),
    {
        let mut ghcb = self;
        ghcb.box_update(GhcbClear);
        let (ghcb_ptr, Tracked(ghcbpage_perm)) = ghcb.into_raw();
        let mut exit_code = SVM_EXIT_SNP_GUEST_REQUEST;
        let mut exit_info1 = req_gpa;
        let mut exit_info2 = resp_gpa;
        let tracked mut ghcbpage_perm0 = Map::tracked_empty();
        proof {
            ghcbpage_perm0.tracked_insert(0, ghcbpage_perm);
        }
        let resp = ghcb_page_proto(
            ghcb_ptr.clone(),
            &mut exit_code,
            &mut exit_info1,
            &mut exit_info2,
            Tracked(&mut ghcbpage_perm0),
            Tracked(cs),
        );
        match resp {
            SvmStatus::Ok => {
                if exit_code != SVM_EXIT_SNP_GUEST_REQUEST {
                    vc_terminate(SM_TERM_GHCB_RESP_INVALID, Tracked(&mut cs.snpcore));
                }
            },
            _ => {
                vc_terminate(SM_TERM_GHCB_RESP_INVALID, Tracked(&mut cs.snpcore));
            },
        }
        VBox::from_raw(ghcb_ptr.to_usize(), Tracked(ghcbpage_perm0.tracked_remove(0)))
    }
}

fn init_ghcb_page(
    ghcb_ptr: SnpPPtr<GhcbPage>,
    Tracked(page_perm): Tracked<SnpPointsToRaw>,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
) -> (ghcb_perm: Tracked<SnpPointsToRaw>)
    requires
        page_perm@.wf_const_default((ghcb_ptr.id(), PAGE_SIZE as nat)),
        ghcb_ptr.is_constant(),
        ghcb_ptr.id() % PAGE_SIZE!() == 0,
        (*old(cs)).inv(),
    ensures
        ghcb_perm@@.wf_shared((ghcb_ptr.id(), PAGE_SIZE as nat)),
        cs.inv(),
        cs.snpcore.ghcb_value() == ghcb_ptr.id(),
        cs.only_lock_reg_coremode_updated((*old(cs)), set![GHCB_REGID()], set![spec_PT().lockid()]),
{
    let ghcb_page: u64 = ghcb_ptr.as_u64().to_page();
    assert((ghcb_page as int).to_addr() == ghcb_ptr.id());
    let tracked mut page_perm0 = Map::tracked_empty();
    let ghost old_page_perm = page_perm;
    proof {
        page_perm0.tracked_insert(0, page_perm);
    }
    early_mk_shared(ghcb_page, Tracked(cs), Tracked(&mut page_perm0));
    let tracked mut ghcb_perm = page_perm0.tracked_remove(0);
    mem_set_zeros(ghcb_ptr.to_usize(), PAGE_SIZE, Tracked(&mut ghcb_perm));
    ghcb_register_ghcb(vn_to_pn(ghcb_page, Tracked(&ghcb_perm)) as usize, Tracked(&mut cs.snpcore));
    proof {
        crate::snp::mem::lemma_mk_shared_default_to_shared(old_page_perm@, ghcb_perm@);
    }
    Tracked(ghcb_perm)
}

} // verus!
use crate::vbox::*;
verus! {

pub fn ghcb_page_proto(
    ghcb_ptr: SnpPPtr<GhcbPage>,
    exit: &mut u64,
    exit1: &mut u64,
    exit2: &mut u64,
    Tracked(ghcbpage_perm0): Tracked<&mut Map<int, SnpPointsTo<GhcbPage>>>,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
) -> (ret: SvmStatus)
    requires
        (*old(cs)).inv(),
        old(ghcbpage_perm0).contains_key(0),
        old(ghcbpage_perm0)[0]@.wf_shared(ghcb_ptr.id()),
        ghcb_ptr.is_constant(),
    ensures
        ghcbpage_perm0.contains_key(0),
        ghcbpage_perm0[0]@.only_val_updated(old(ghcbpage_perm0)[0]@),
        ghcbpage_perm0[0]@.wf_shared(ghcb_ptr.id()),
        cs.inv(),
        cs.only_lock_reg_coremode_updated((*old(cs)), set![], set![]),
{
    let ghost oldcs = *cs;
    let tracked mut ghcb_msr_perm = cs.snpcore.regs.tracked_remove(GHCB_REGID());
    let ghost oldghcb_msr_perm = ghcb_msr_perm;
    let tracked ghcbpage_perm = ghcbpage_perm0.tracked_remove(0);
    if !MSR_GHCB().read(Tracked(&ghcb_msr_perm)).eq(&ghcb_ptr.as_u64()) {
        proof {
            cs.snpcore.regs.tracked_insert(GHCB_REGID(), ghcb_msr_perm);
        }
        vc_terminate(SM_TERM_NO_GHCB, Tracked(&mut cs.snpcore));
    }
    let mut ghcb: VBox<GhcbPage> = VBox::from_raw(ghcb_ptr.to_usize(), Tracked(ghcbpage_perm));
    ghcb.box_update((FillGhcbFn, *exit, *exit1, *exit2));
    let (ghcb_ptr, Tracked(mut ghcbpage_perm)) = ghcb.into_raw();
    let tracked mut op_ghcbpage_perm = Some(ghcbpage_perm.tracked_into_raw());
    vmgexit(
        Tracked(&mut ghcb_msr_perm),
        Tracked(&mut cs.snpcore.coreid),
        Tracked(&mut op_ghcbpage_perm),
    );
    if !MSR_GHCB().read(Tracked(&ghcb_msr_perm)).eq(&ghcb_ptr.as_u64()) {
        proof {
            cs.snpcore.regs.tracked_insert(GHCB_REGID(), ghcb_msr_perm);
        }
        vc_terminate(SM_TERM_NO_GHCB, Tracked(&mut cs.snpcore));
    }
    proof {
        assert(ghcb_msr_perm.val::<u64_s>() === oldghcb_msr_perm.val::<u64_s>());
        assert(ghcb_msr_perm.view::<u64_s>() === oldghcb_msr_perm.view::<u64_s>());
        cs.snpcore.regs.tracked_insert(GHCB_REGID(), ghcb_msr_perm);
        assert(cs.snpcore.regs[GHCB_REGID()] === (*old(cs)).snpcore.regs[GHCB_REGID()]);
        assert(cs.snpcore.regs =~~= (*old(cs)).snpcore.regs);
        assert(cs.only_lock_reg_coremode_updated((*old(cs)), set![], set![]));
        ghcbpage_perm = op_ghcbpage_perm.tracked_unwrap().tracked_into();
    }
    let ghost prevcs = *cs;
    // HV-shared memory should be copied or moved and cannot be borrowed.
    let (exit_info_1, Tracked(ghcbpage_perm)) = ghcb_ptr.vmsa().sw_exit_info_1().copy_with::<
        GhcbPage,
    >(Tracked(ghcbpage_perm));
    let (exit_info_2, Tracked(ghcbpage_perm)) = ghcb_ptr.vmsa().sw_exit_info_2().copy_with::<
        GhcbPage,
    >(Tracked(ghcbpage_perm));
    let (sw_exit_code, Tracked(ghcbpage_perm)) = ghcb_ptr.vmsa().sw_exit_code().copy_with::<
        GhcbPage,
    >(Tracked(ghcbpage_perm));
    let exit_info_1: u64 = exit_info_1.into();
    let exit_info_2: u64 = exit_info_2.into();
    proof {
        ghcbpage_perm0.tracked_insert(0, ghcbpage_perm);
    }
    if (exit_info_1 & 0xffffffff) == 1 {
        let vec = SVM_EVTINJ_VEC_MASK!(exit_info_2);
        let ty = SVM_EVTINJ_TYPE_MASK!(exit_info_2);
        let valid = SVM_EVTINJ_IS_VALID!(exit_info_2);
        if valid && (ty == SVM_EVTINJ_TYPE_EXEPT) && (vec == SVM_EVTINJ_VEC_X86_TRAP_GP || vec
            == SVM_EVTINJ_VEC_X86_TRAP_UD) {
            SvmStatus::Exception
        } else {
            SvmStatus::VmmError
        }
    } else {
        *exit = sw_exit_code.into();
        *exit1 = exit_info_1;
        *exit2 = exit_info_2;
        SvmStatus::Ok
    }
}

} // verus!
