use super::*;

verus! {

pub const INVALID_ADDR: usize = VM_MEM_SIZE + 1;

pub open spec fn spec_pa_to_va(pa: int) -> int {
    pa
}

pub open spec fn spec_va_to_pa(pa: int) -> int {
    pa
}

pub open spec fn spec_pn_to_vn(pn: int) -> int {
    pn
}

pub open spec fn spec_vn_to_pn(vn: int) -> int {
    vn
}

} // verus!
verismo_simple! {
pub trait SpecAddrTrait {
    spec fn spec_valid_addr_with(&self, size: nat) -> bool;
    spec fn to_page(&self) -> int;
    spec fn is_page_aligned(&self) -> bool;
}

pub trait SpecPageTrait {
    spec fn spec_valid_pn_with(&self, size: nat) -> bool;
    spec fn to_addr(&self) -> int;
}

pub trait AddrTrait<PageT> {
    spec fn spec_to_page(&self) -> PageT;
    spec fn addrt_to_int(v: PageT) -> int;
    spec fn spec_ensures_to_page(&self, ret: PageT) -> bool;
    spec fn spec_valid_addr_with(&self, size: nat) -> bool;
    spec fn spec_check_valid_addr_requires(&self, size: PageT) -> bool;

    fn check_valid_addr(&self, size: PageT) -> (ret: bool)
    requires
        self.spec_check_valid_addr_requires(size),
    ensures
        ret == self.spec_valid_addr_with(Self::addrt_to_int(size) as nat);

    fn to_page(&self) -> (ret: PageT)
    requires
        self.spec_valid_addr_with(0)
    ensures
        ret === self.spec_to_page(),
        self.spec_ensures_to_page(ret);
}

pub trait PageTrait<AddrT> {
    spec fn spec_to_addr(&self) -> AddrT;
    spec fn spec_ensures_to_addr(&self, ret: AddrT) -> bool;
    spec fn spec_valid_pn_with(&self, size: nat) -> bool;
    spec fn paget_to_int(v: AddrT) -> int;
    spec fn spec_check_valid_pn_requires(&self, size: AddrT) -> bool;

    fn check_valid_pn(&self, size: AddrT) -> (ret: bool)
    requires
        self.spec_check_valid_pn_requires(size),
    ensures
        ret == self.spec_valid_pn_with(Self::paget_to_int(size) as nat);

    fn to_addr(&self) -> (ret: AddrT)
    requires
        self.spec_valid_pn_with(0)
    ensures
        ret === self.spec_to_addr(),
        self.spec_ensures_to_addr(ret);
}
}

#[macro_export]
macro_rules! impl_addr_interface {
    ($basetype: ty) => {
        verus! {
        impl AddrTrait<$basetype> for $basetype {
            open spec fn spec_to_page(&self) -> $basetype {
                let s: $basetype = PAGE_SIZE.vspec_cast_to();
                *self / s
            }

            open spec fn addrt_to_int(v: $basetype) -> int {
                v.vspec_cast_to()
            }

            open spec fn spec_ensures_to_page(&self, ret: $basetype) -> bool {
                &&& ret.wf()
                &&& self.is_constant() ==> ret.is_constant()
                &&& Self::addrt_to_int(ret) ==  Self::addrt_to_int(*self) / PAGE_SIZE!()
            }

            open spec fn spec_valid_addr_with(&self, size: nat) -> bool {
                let start: int = (*self).vspec_cast_to();
                &&& start.spec_valid_addr_with(size)
                &&& self.wf()
            }

            open spec fn spec_check_valid_addr_requires(&self, size: $basetype) -> bool{
                &&& self.is_constant()
                &&& size.is_constant()
            }

            fn check_valid_addr(&self, size: $basetype) -> (ret: bool)
            {
                let addr: usize = (*self) as usize;
                let size: usize = size as usize;
                (size <= VM_MEM_SIZE) && (addr <= VM_MEM_SIZE - size)
            }

            fn to_page(&self) -> (ret: $basetype) {
                *self / (PAGE_SIZE as $basetype)
            }
        }
        }
    };
}

#[macro_export]
macro_rules! impl_page_interface {
    ($basetype: ty) => {
        verus! {
        impl PageTrait<$basetype> for $basetype {
            open spec fn spec_to_addr(&self) -> $basetype {
                (*self * (PAGE_SIZE as $basetype)).vspec_cast_to()
            }

            open spec fn paget_to_int(v: $basetype) -> int {
                v.vspec_cast_to()
            }

            open spec fn spec_ensures_to_addr(&self, ret: $basetype) -> bool {
                &&& ret.wf()
                &&& self.is_constant() ==> ret.is_constant()
                &&& Self::paget_to_int(ret) ==  Self::paget_to_int(*self) * PAGE_SIZE!()
            }

            open spec fn spec_valid_pn_with(&self, size: nat) -> bool {
                let start: int = (*self).vspec_cast_to();
                &&& start.spec_valid_pn_with(size)
                &&& self.wf()
            }

            open spec fn spec_check_valid_pn_requires(&self, size: $basetype) -> bool {
                &&& self.is_constant()
                &&& size.is_constant()
            }

            fn check_valid_pn(&self, size: $basetype) -> (ret: bool) {
                let addr: usize = (*self) as usize;
                let size: usize = size as usize;
                (size <= VM_PAGE_NUM) && (addr <= VM_PAGE_NUM - size)
            }

            fn to_addr(&self) -> (ret: $basetype)
            {
                (*self) * 0x1000
            }
        }
        }
    };
}

#[macro_export]
macro_rules! impl_addr_safe_interface {
    ($basetype: ty) => {
        verus! {
        impl AddrTrait<$basetype> for $basetype {
            open spec fn spec_to_page(&self) -> $basetype {
                let s: $basetype = PAGE_SIZE.vspec_cast_to();
                *self / s
            }

            open spec fn addrt_to_int(v: $basetype) -> int {
                v.vspec_cast_to()
            }

            open spec fn spec_ensures_to_page(&self, ret: $basetype) -> bool {
                &&& ret.wf()
                &&& self.is_constant() ==> ret.is_constant()
                &&& Self::addrt_to_int(ret) ==  Self::addrt_to_int(*self) / PAGE_SIZE!()
            }

            open spec fn spec_valid_addr_with(&self, size: nat) -> bool {
                let start: int = (*self).vspec_cast_to();
                &&& start.spec_valid_addr_with(size)
                &&& self.wf()
            }

            open spec fn spec_check_valid_addr_requires(&self, size: $basetype) -> bool{
                &&& self.is_constant()
                &&& size.is_constant()
            }

            fn check_valid_addr(&self, size: $basetype) -> (ret: bool)
            {
                let addr: usize = (*self).into();
                let size: usize = size.into();
                (size <= VM_MEM_SIZE) && (addr <= VM_MEM_SIZE - size)
            }

            fn to_page(&self) -> (ret: $basetype) {
                let s: $basetype = PAGE_SIZE.into();
                (*self).div(s)
            }
        }
        }
    };
}

#[macro_export]
macro_rules! impl_page_safe_interface {
    ($basetype: ty, $ptype: ty) => {
        verus! {
        impl PageTrait<$basetype> for $basetype {
            open spec fn spec_to_addr(&self) -> $basetype {
                (*self * (PAGE_SIZE).vspec_cast_to()).vspec_cast_to()
            }

            open spec fn paget_to_int(v: $basetype) -> int {
                v.vspec_cast_to()
            }

            open spec fn spec_ensures_to_addr(&self, ret: $basetype) -> bool {
                &&& ret.wf()
                &&& self.is_constant() ==> ret.is_constant()
                &&& Self::paget_to_int(ret) ==  Self::paget_to_int(*self) * PAGE_SIZE!()
            }

            open spec fn spec_valid_pn_with(&self, size: nat) -> bool {
                let start: int = (*self).vspec_cast_to();
                &&& start.spec_valid_pn_with(size)
                &&& self.wf()
            }

            open spec fn spec_check_valid_pn_requires(&self, size: $basetype) -> bool {
                &&& self.is_constant()
                &&& size.is_constant()
            }

            fn check_valid_pn(&self, size: $basetype) -> (ret: bool) {
                let addr: usize = (*self).into();
                let size: usize = size.into();
                (size <= VM_PAGE_NUM) && (addr <= VM_PAGE_NUM - size)
            }

            fn to_addr(&self) -> (ret: $basetype)
            {
                (*self).mul(PAGE_SIZE as $ptype)
            }
        }
        }
    };
}

verus! {

impl SpecPageTrait for int {
    open spec fn spec_valid_pn_with(&self, size: nat) -> bool {
        &&& 0 <= *self as int + (size as int) <= VM_PAGE_NUM
        &&& 0 <= *self as int <= VM_PAGE_NUM
    }

    open spec fn to_addr(&self) -> int {
        *self * (PAGE_SIZE!())
    }
}

impl SpecAddrTrait for int {
    open spec fn spec_valid_addr_with(&self, size: nat) -> bool {
        &&& 0 <= *self as int + (size as int) <= VM_MEM_SIZE
        &&& 0 <= *self as int <= VM_MEM_SIZE
    }

    open spec fn to_page(&self) -> int {
        *self / (PAGE_SIZE!())
    }

    open spec fn is_page_aligned(&self) -> bool {
        *self === self.to_page().to_addr()
    }
}

} // verus!
impl_addr_interface! {u64_t}
impl_page_interface! {u64_t}
impl_addr_interface! {usize_t}
impl_page_interface! {usize_t}

impl_addr_safe_interface! {usize_s}
impl_page_safe_interface! {usize_s, usize_t}

impl_addr_safe_interface! {u64_s}
impl_page_safe_interface! {u64_s, u64_t}
