use alloc::boxed::Box;

use super::*;
use crate::addr_e::{AddrTrait, OnePage, PageTrait, SpecAddrTrait, SpecPageTrait};
use crate::allocator::VeriSMoAllocator;
use crate::arch::addr_s::PAGE_SIZE;
use crate::global::*;
use crate::lock::{LockPermRaw, MapLockContains, MapRawLockTrait};
use crate::registers::CoreIdPerm;
use crate::snp::ghcb::*;
use crate::snp::SnpCoreSharedMem;

verus! {

#[verifier(external_body)]
#[verifier::reject_recursive_types_in_ground_variants(T)]
pub struct VBox<T> {
    pub b: Box<T>,
}

impl<T: IsConstant> IsConstant for VBox<T> {
    open spec fn is_constant(&self) -> bool {
        &&& self.view().is_constant()
    }

    open spec fn is_constant_to(&self, vmpl: nat) -> bool {
        &&& self.view().is_constant_to(vmpl)
    }
}

pub closed spec fn spec_box_size() -> nat;

impl<T> SpecSize for VBox<T> {
    open spec fn spec_size_def() -> nat {
        spec_box_size()
    }
}

impl<T> VTypeCast<SecSeqByte> for VBox<T> {
    closed spec fn vspec_cast_to(self) -> SecSeqByte;
}

impl<T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> VBox<T> {
    pub fn set(self, other: Self) -> (ret: Self)
        requires
            self.wf(),
            other.wf(),
        ensures
            ret@ === other@,
            self.snp() === ret.snp(),
            ret.only_val_updated(self),
    {
        proof {
            proof_cast_from_seq_unique(other@);
        }
        let (dest, Tracked(dest_perm)) = self.into_raw();
        let (src, Tracked(src_perm)) = other.into_raw();
        let tracked mut src_perm = src_perm.tracked_into_raw();
        let tracked mut dest_perm = dest_perm.tracked_into_raw();
        mem_copy(
            src.to_usize(),
            dest.to_usize(),
            size_of::<T>(),
            Tracked(&mut src_perm),
            Tracked(&mut dest_perm),
        );
        let other = VBox::<T>::from_raw(src.to_usize(), Tracked(src_perm.tracked_into()));
        VBox::from_raw(dest.to_usize(), Tracked(dest_perm.tracked_into()))
    }

    pub fn to<T2: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>>(self) -> (ret: VBox<
        T2,
    >)
        requires
            spec_size::<T>() == spec_size::<T2>(),
            is_castable::<T, T2>(self@),
            self.wf(),
        ensures
            self.snp() === ret.snp(),
            self.id() == ret.id(),
            VTypeCast::<SecSeqByte>::vspec_cast_to(self@) === VTypeCast::<
                SecSeqByte,
            >::vspec_cast_to(ret@),
            ret.wf(),
    {
        let (ptr, Tracked(perm0)) = self.into_raw();
        let tracked raw = perm0.tracked_into_raw();
        let tracked perm = raw.tracked_into();
        proof {
            assert(perm@.wf());
            proof_into_is_constant::<T, SecSeqByte>(perm0@.get_value());
            proof_into_is_constant::<SecSeqByte, T2>(raw@.bytes());
        }
        VBox::from_raw(ptr.to_usize(), Tracked(perm))
    }
}

impl<T: IsConstant + WellFormed> VBox<T> {
    pub open spec fn is_page(&self) -> bool {
        &&& self.id() % (PAGE_SIZE as int) == 0
        &&& self.wf()
    }

    pub open spec fn is_shared_page(&self) -> bool {
        &&& self.is_page()
        &&& self.snp() === SwSnpMemAttr::shared()
    }

    pub open spec fn is_default_page(&self) -> bool {
        &&& self.is_page()
        &&& self.snp() === SwSnpMemAttr::spec_default()
    }

    pub open spec fn is_vmsa_page(&self) -> bool {
        &&& self.is_page()
        &&& self.snp() === SwSnpMemAttr::vmsa()
    }
}

impl<T: IsConstant + WellFormed> WellFormed for VBox<T> {
    open spec fn wf(&self) -> bool {
        &&& inv_snp_value(self.snp(), self.view())
        &&& self.id().spec_valid_addr_with(spec_size::<T>())
    }
}

impl<T> VBox<T> {
    pub closed spec fn view(&self) -> T;

    pub closed spec fn id(&self) -> int;

    pub closed spec fn snp(&self) -> SwSnpMemAttr;

    pub open spec fn spec_eq(self, other: Self) -> bool {
        &&& self.id() == other.id()
        &&& self.snp() == other.snp()
        &&& self.view() === other.view()
    }

    pub open spec fn only_val_updated(self, prev: Self) -> bool {
        &&& self.id() == prev.id()
        &&& self.snp() == prev.snp()
    }
}

impl<T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> VBox<T> {
    pub fn new_aligned_uninit(align: usize, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (ret:
        VBox<T>)
        requires
            (*old(cs)).inv_ac(),
            spec_bit64_is_pow_of_2(align as int),
            spec_size::<T>() >= VeriSMoAllocator::spec_minsize(),
        ensures
            (*cs).inv_ac(),
            (*cs).only_lock_reg_updated((*old(cs)), set![], set![spec_ALLOCATOR_lockid()]),
            ret.id() % (align as int) == 0,
            ret.id().spec_valid_addr_with(spec_size::<T>()),
            ret.snp() === SwSnpMemAttr::spec_default(),
            ret.wf(),
            ret@.is_constant(),
    {
        use crate::global::*;
        let tracked perm = cs.lockperms.tracked_remove(spec_ALLOCATOR_lockid());
        let tracked mut perm0 = Map::tracked_empty();
        proof {
            assert(!perm@.locked);
            assert(perm@.lockid() === spec_ALLOCATOR_lockid());
            assert(perm@.invfn.value_invfn() === VeriSMoAllocator::invfn());
            perm0.tracked_insert(0, perm);
        }
        let size = size_of::<T>();
        let result = ALLOCATOR().alloc_aligned(
            size,
            align,
            Tracked(&mut perm0),
            Tracked(&cs.snpcore.coreid),
        );
        proof {
            cs.lockperms.tracked_insert(spec_ALLOCATOR_lockid(), perm0.tracked_remove(0));
        }
        if result.is_err() {
            use crate::debug::VEarlyPrintAtLevel;
            new_strlit("\nfailed new_aligned_uninit\n").leak_debug();
            vc_terminate_debug(SM_TERM_MEM, Tracked(cs));
        }
        let (addr, Tracked(perm)) = result.unwrap();
        VBox::from_raw(addr, Tracked(perm.tracked_into()))
    }

    #[inline(always)]
    pub fn new_uninit(Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (ret: VBox<T>)
        requires
            (*old(cs)).lockperms.contains_vlock(spec_ALLOCATOR()),
            (*old(cs)).inv(),
            spec_size::<T>() >= VeriSMoAllocator::spec_minsize(),
        ensures
            (*cs).only_lock_reg_updated((*old(cs)), set![], set![spec_ALLOCATOR_lockid()]),
            (*cs).inv(),
            ret.id().spec_valid_addr_with(spec_size::<T>()),
            ret.snp() === SwSnpMemAttr::spec_default(),
            ret@.is_constant(),
    {
        VBox::new_aligned_uninit(1, Tracked(cs))
    }

    #[inline(always)]
    pub fn new_aligned(align: usize, val: T, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (ret:
        VBox<T>)
        requires
            (*old(cs)).inv_ac(),
            spec_bit64_is_pow_of_2(align as int),
            spec_size::<T>() >= VeriSMoAllocator::spec_minsize(),
            val.wf(),
        ensures
            (*cs).inv_ac(),
            (*cs).only_lock_reg_updated((*old(cs)), set![], set![spec_ALLOCATOR_lockid()]),
            ret.id() % (align as int) == 0,
            ret.snp() === SwSnpMemAttr::spec_default(),
            ret@ === val,
            ret.wf(),
    {
        let b = Self::new_aligned_uninit(align, Tracked(cs));
        let (ptr, Tracked(mut perm)) = b.into_raw();
        ptr.replace(Tracked(&mut perm), val);
        VBox::from_raw(ptr.to_usize(), Tracked(perm))
    }

    #[inline(always)]
    pub fn new_shared_page(
        align: usize,
        ghcb_h: GhcbHandle,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
    ) -> (ret: (VBox<T>, GhcbHandle))
        requires
            (*old(cs)).inv_ac(),
            ghcb_h.ghcb_wf(),
            spec_bit64_is_pow_of_2(align as int),
            align > 0,
            align % PAGE_SIZE == 0,
            spec_size::<T>() == PAGE_SIZE,
        ensures
            (*cs).inv_ac(),
            (*cs).only_lock_reg_coremode_updated(
                (*old(cs)),
                set![],
                set![spec_ALLOCATOR_lockid(), spec_PT_lockid()],
            ),
            ret.0.is_shared_page(),
            ret.0@.is_constant(),
            ret.1.ghcb_wf(),
            ret.1.only_val_updated(ghcb_h),
    {
        let ghost cs1 = *cs;
        let onepage = VBox::<T>::new_aligned_uninit(align, Tracked(cs));
        proof {
            assert(onepage.id() % PAGE_SIZE as int == 0) by {
                proof_mod_propogate(onepage.id(), align as int, 0x1000);
            }
            assert(onepage.is_page());
        }
        let ghost cs2 = *cs;
        let ret = onepage.mk_shared_page(ghcb_h, Tracked(cs));
        proof {
            cs1.lemma_update_prop(
                cs2,
                *cs,
                set![],
                set![spec_ALLOCATOR_lockid()],
                set![],
                set![spec_PT_lockid()],
            );
            assert(set![spec_ALLOCATOR_lockid()].union(set![spec_PT_lockid()])
                =~~= set![spec_ALLOCATOR_lockid(), spec_PT_lockid()])
        }
        ret
    }

    #[inline(always)]
    pub fn new(v: T, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (ret: VBox<T>)
        requires
            (*old(cs)).lockperms.contains_vlock(spec_ALLOCATOR()),
            (*old(cs)).inv(),
            spec_size::<T>() >= VeriSMoAllocator::spec_minsize(),
            v.wf(),
        ensures
            cs.only_lock_reg_updated((*old(cs)), set![], set![spec_ALLOCATOR().lockid()]),
            cs.inv(),
            ret.id().spec_valid_addr_with(spec_size::<T>()),
            ret@ === v,
            ret.snp() === SwSnpMemAttr::spec_default(),
            ret.wf(),
    {
        VBox::new_aligned(1, v, Tracked(cs))
    }

    pub fn mk_shared_page(
        self,
        ghcb_h: GhcbHandle,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
    ) -> (ret: (VBox<T>, GhcbHandle))
        requires
            (*old(cs)).inv_ac(),
            ghcb_h.ghcb_wf(),
            self.is_default_page(),
            self@.is_constant(),
            spec_size::<T>() == PAGE_SIZE,
        ensures
            cs.inv_ac(),
            cs.only_lock_reg_coremode_updated((*old(cs)), set![], set![spec_PT_lockid()]),
            ret.0.is_shared_page(),
            ret.0@.is_constant(),
            ret.1.ghcb_wf(),
            ret.1.only_val_updated(ghcb_h),
    {
        let onepage = self;
        let (onepage, Tracked(mut perm)) = onepage.into_raw();
        let page: usize = onepage.to_usize().to_page();
        let tracked mut page_perms = Map::tracked_empty();
        let tracked prev_perm = perm.tracked_into_raw();
        proof {
            page_perms.tracked_insert(page as int, prev_perm);
            assert(page_perms.contains_key(page as int));
            let perm = page_perms[page as int];
            assert(perm@.wf_const_default(((page as int).to_addr(), PAGE_SIZE as nat)));
        }
        let ghcb_h = ghcb_h.mk_shared(page as u64, 1, Tracked(cs), Tracked(&mut page_perms));
        proof {
            crate::snp::mem::lemma_mk_shared_default_to_shared(
                prev_perm@,
                page_perms[page as int]@,
            );
        }
        let onepage = VBox::from_raw(
            page.to_addr(),
            Tracked(page_perms.tracked_remove(page as int).tracked_into()),
        );
        (onepage, ghcb_h)
    }
}

} // verus!
verismo_simple! {
impl<T: IsConstant + WellFormed + SpecSize> VBox<T> {
    #[verifier(external_body)]
    pub fn borrow<'a>(&'a self) -> (ret: &'a T)
    requires
        self.snp().is_vmpl0_private(),
    ensures
        self.snp().ensures_read(Some(self@), *ret)
    {
        &*self.b
    }

    #[verifier(external_body)]
    pub fn from_raw(ptr: usize, Tracked(perm): Tracked<SnpPointsTo<T>>)
        -> (res: VBox<T>)
    requires
        perm@.wf_not_null_at(ptr as int),
        perm@.value().is_Some(),
    ensures
        res@ === perm@.get_value(),
        res.id() == perm@.id(),
        res.snp() === perm@.snp(),
    {
        let mut ret: VBox<T>;
        unsafe {
            let raw = ptr as *mut T;
            ret = VBox {
                b: Box::<T>::from_raw(raw)
            }
        }
        ret
    }

    #[verifier(external_body)]
    pub fn into_raw(self) -> (ptr_perm: (SnpPPtr<T>, Tracked<SnpPointsTo<T>>))
    ensures
        ptr_perm.0.is_constant(),
        ptr_perm.1@@.get_value() === self@,
        ptr_perm.1@@.value().is_Some(),
        ptr_perm.1@@.wf_not_null_at(ptr_perm.0.id()),
        ptr_perm.1@@.snp() === self.snp(),
        self.id() == ptr_perm.0.id(),
    {
        let mut addr: usize;
        unsafe {
            let ptr = Box::into_raw(self.b);
            addr = (ptr as usize).into();
        }
        (SnpPPtr::from_usize(addr), Tracked::assume_new())
    }

    #[verifier(external_body)]
    pub fn get_const_addr(&self) -> (addr: usize_t)
    ensures
        self.id() == addr,
        self.id().spec_valid_addr_with(spec_size::<T>()),
    {
        let data_ref = &*self.b;
        unsafe {
            let addr = data_ref as *const _;
            (addr as usize)
        }
    }
}

pub trait MutFnTrait<'a, Params, Out> {
    spec fn spec_update_requires(&self, params: Params) -> bool;

    spec fn spec_update(&self, prev: &Self, params: Params, ret: Out) -> bool;

    fn box_update(&'a mut self, params: Params) -> (ret: Out)
    requires
        old(self).spec_update_requires(params)
    ensures
        self.spec_update(&*old(self), params, ret);
}

pub trait MutFnWithCSTrait<'a, T, Params, Out> {
    spec fn spec_update_cs_requires(&self, params: Params, cs: T) -> bool;

    spec fn spec_update_cs(&self, prev: &Self, params: Params, oldcs: T, ret: Out, cs: T) -> bool;

    fn box_update_cs(&'a mut self, params: Params, Tracked(cs): Tracked<&mut T>) -> (ret: Out)
    requires
        old(self).spec_update_cs_requires(params, *old(cs))
    ensures
        self.spec_update_cs(&*old(self), params, *old(cs), ret, *cs);
}

pub trait BorrowFnTrait<'a, Params, Out> {
    spec fn spec_borrow_requires(&self, params: Params) -> bool;

    spec fn spec_borrow_ensures(&self, params: Params, ret: Out) -> bool;

    fn box_borrow(&'a self, params: Params) -> (ret: Out)
    requires
        self.spec_borrow_requires(params)
    ensures
        self.spec_borrow_ensures(params, ret);
}

/*
impl MutFnTrait<'a, Out, F: Fn(T) -> F> for T {
    spec fn spec_update_requires(&self, call: F) -> bool
    {
        call.requires(*self)
    }

    spec fn spec_update(&self, prev: &Self, call: F, ret: ()) -> bool
    {
        call.ensures((*prev, ), (*self, ))
    }

    fn box_update(&'a mut self, call: F) -> (ret: ())
    {
        *self = call(*self)
    }
}
*/

impl<Params, Out, 'a, T: MutFnTrait<'a, Params, Out>> MutFnTrait<'a, Params, Out> for VBox<T> {
    open spec fn spec_update_requires(&self, params: Params) -> bool {
        self@.spec_update_requires(params)
    }

    open spec fn spec_update(&self, prev: &Self, params: Params, ret: Out) -> bool {
        &&& //self.snp().is_vmpl0_private() ==>
            self@.spec_update(&prev@, params, ret)
        &&& self.only_val_updated(*prev)
        //&&& exists |p| self@.spec_update(&p, params, ret)
        //&&& self.wf()
    }

    #[verifier(external_body)]
    fn box_update(&'a mut self, params: Params) -> (ret: Out)
    {
        self.b.box_update(params)
    }
}

impl<Params, T2, Out, 'a, T: MutFnWithCSTrait<'a, T2, Params, Out>> MutFnWithCSTrait<'a, T2, Params, Out> for VBox<T> {
    open spec fn spec_update_cs_requires(&self, params: Params, cs: T2) -> bool {
        self@.spec_update_cs_requires(params, cs)
    }

    open spec fn spec_update_cs(&self, prev: &Self, params: Params, oldcs: T2, ret: Out, cs: T2) -> bool {
        &&& //self.snp().is_vmpl0_private() ==>
            self@.spec_update_cs(&prev@, params, oldcs, ret, cs)
        &&& self.only_val_updated(*prev)
        //&&& exists |p| self@.spec_update(&p, params, ret)
        //&&& self.wf()
    }

    #[verifier(external_body)]
    fn box_update_cs(&'a mut self, params: Params, Tracked(cs): Tracked<&mut T2>) -> (ret: Out)
    {
        self.b.box_update_cs(params, Tracked(cs))
    }
}

impl<Params, Out: WellFormed + IsConstant, 'a, T: BorrowFnTrait<'a, Params, Out>> BorrowFnTrait<'a, Params, Out> for VBox<T> {
    open spec fn spec_borrow_requires(&self, params: Params) -> bool {
        self@.spec_borrow_requires(params)
    }

    open spec fn spec_borrow_ensures(&self, params: Params, ret: Out) -> bool {
        &&& (self.snp().is_vmpl0_private() ==>
            self@.spec_borrow_ensures(params, ret))
        &&& (!spec_attack() ==>
            self@.spec_borrow_ensures(params, ret))
        &&& inv_snp_value(self.snp(), ret)
    }

    #[verifier(external_body)]
    fn box_borrow(&'a self, params: Params) -> (ret: Out)
    {
        self.b.box_borrow(params)
    }
}
}
