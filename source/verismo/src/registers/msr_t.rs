use super::*;

verismo! {
pub struct Msr {
    pub reg: u32,
}

/*
#[inline(always)]
#[verifier(external_body)]
pub fn ghcb_vmgexit(value: u64_t) {
    let low = 0xff03u32;
    let high = 0u32;
    let reg: u32 = 0xc0010130u32;
    unsafe {
        asm!(
            "wrmsr",
            "rep",
            "vmmcall",
            in("ecx") reg,
            in("eax") low, in("edx") high,
            options(nostack, preserves_flags),
        );
    }
}
*/

impl Msr {
    #[inline(always)]
    #[verifier(external_body)]
    pub fn write_vmgexit(&self, value: u64_s,
        Tracked(perm): Tracked<&mut RegisterPerm>,
        Tracked(coreperm): Tracked<&mut CoreIdPerm>,
        Tracked(memperm): Tracked<&mut Option<SnpPointsToRaw>>)
    {
        let low: u32 = value.reveal_value() as u32;
        let high: u32 = (value.reveal_value() >> 32u64) as u32;
        let reg = self.reg.reveal_value();
        unsafe {
            asm!(
                "wrmsr",
                "rep vmmcall",
                in("ecx") reg,
                in("eax") low, in("edx") high,
                options(nostack, preserves_flags),
            );
        }
    }
}
impl AnyRegTrait<u64_s> for Msr {
    open spec fn reg_id(&self) -> RegName {
        RegName::MSR(self.reg as u32)
    }

    open spec fn write_extra_requires(&self, val: u64_s, perm: RegisterPermValue<u64_s>) -> bool {
        true
    }
    open spec fn read_extra_requires(&self,perm: RegisterPermValue<u64_s>) -> bool {
        true
    }

    #[inline(always)]
    #[verifier(external_body)]
    fn read(&self, Tracked(perm): Tracked<&RegisterPerm>) -> (ret: u64_s)
    {
        let (high, low): (u32, u32);
        let reg = self.reg.reveal_value();
        unsafe {
            asm!(
                "rdmsr",
                in("ecx") reg,
                out("eax") low, out("edx") high,
                options(nomem, nostack, preserves_flags),
            );
        }

        u64_s::constant((high as u64) << 32u64 | (low as u64))
    }

    #[inline(always)]
    #[verifier(external_body)]
    fn write(&self, value: u64_s, Tracked(perm): Tracked<&mut RegisterPerm>)
    {
        let low: u32 = value.reveal_value() as u32;
        let high: u32 = (value.reveal_value() >> 32u64) as u32;
        let reg = self.reg.reveal_value();
        unsafe {
            asm!(
                "wrmsr",
                in("ecx") reg,
                in("eax") low, in("edx") high,
                options(nostack, preserves_flags),
            );
        }
    }
}
}

pub type SegmentSelector = u16;

macro_rules! readreg_u64 {
    ($name:literal, $rname: ident) => {
        paste::paste! {
            verismo! {
                #[inline(always)]
                #[verifier(external_body)]
                fn read(&self, Tracked(perm): Tracked<&RegisterPerm>) -> (ret: u64_s)
                {
                    let value: u64;
                    unsafe {
                        asm!(
                            concat!("mov {},", $name),
                            out(reg) value,
                            options(nomem, nostack, preserves_flags)
                        );
                    }
                    u64_s::constant(value)
                }
            }
        }
    };
}

macro_rules! writereg_u64 {
    ($name:literal, $rname: ident) => {
        paste::paste! {
            verismo! {
                #[inline(always)]
                #[verifier(external_body)]
                fn write(&self, value: u64_s, Tracked(perm): Tracked<&mut RegisterPerm>)
                {
                    let val = value.reveal_value();
                    unsafe {
                        asm!(
                            concat!("mov ", $name, ", {}"),
                            in(reg) val,
                            options(nomem, nostack, preserves_flags)
                        );
                    }
                }
            }
        }
    };
}

macro_rules! impl_reg64 {
    ($($classname: ident, $name:literal, $rname: ident),*$(,)*) => {
    $(
        verismo_simple!{
        pub struct $classname;
        //pub const $rname: $classname = $classname;
        impl AnyRegTrait<u64_s> for $classname {
            open spec fn reg_id(&self) -> RegName {
                crate::arch::reg::RegName::$rname
            }
            open spec fn write_extra_requires(&self, val: u64_s, perm: RegisterPermValue<u64_s>) -> bool {
                true
            }
            open spec fn read_extra_requires(&self,perm: RegisterPermValue<u64_s>) -> bool {
                true
            }
            readreg_u64!{$name, $rname}
            writereg_u64!{$name, $rname}
        }}
    )*
    }
}

macro_rules! impl_reg16 {
    ($($classname: ident, $name:literal, $rname: ident),*$(,)*) => {
    $(
        verus!{
        pub struct $classname;
        }
        verismo!{
        impl AnyRegTrait<u16_s> for $classname {
            #[verifier(inline)]
            open spec fn reg_id(&self) -> RegName {
                RegName::$rname
            }

            open spec fn write_extra_requires(&self, val: u16_s, perm: RegisterPermValue<u16_s>) -> bool {
                true
            }
            open spec fn read_extra_requires(&self,perm: RegisterPermValue<u16_s>) -> bool {
                true
            }

            #[verifier(external_body)]
            #[inline(always)]
            fn read(&self, Tracked(perm): Tracked<&RegisterPerm>) -> (ret: u16_s)
            {
                let segment: u16;
                unsafe {
                    asm!(
                        concat!("mov {0:x}, ", $name),
                        out(reg) segment,
                        options(nomem, nostack, preserves_flags));
                }
                u16_s::constant(segment)
            }

            #[verifier(external_body)]
            #[inline(always)]
            fn write(&self, value: u16_s, Tracked(perm): Tracked<&mut RegisterPerm>)
            {
                let val = value.reveal_value();
                unsafe {
                    asm!(
                        concat!("mov ", $name, ", {0:x}"),
                        in(reg) val,
                        options(nomem, nostack, preserves_flags)
                    );
                }
            }
        }}
    )*
    }
}

verus! {

pub struct XCR0;

} // verus!
verismo! {
impl AnyRegTrait<u64_s> for XCR0 {
    #[verifier(inline)]
    open spec fn reg_id(&self) -> RegName {
        RegName::XCr0
    }

    open spec fn write_extra_requires(&self, val: u64_s, perm: RegisterPermValue<u64_s>) -> bool {
        true
    }

    open spec fn read_extra_requires(&self,perm: RegisterPermValue<u64_s>) -> bool {
        true
    }

    #[inline]
    #[verifier(external_body)]
    fn read(&self, Tracked(perm): Tracked<&RegisterPerm>) -> (ret: u64_s)
    {
        let (low, high): (u32, u32);
        unsafe {
            asm!(
                "xgetbv",
                in("ecx") 0,
                out("rax") low, out("rdx") high,
                options(nomem, nostack, preserves_flags),
            );
        }
        u64_s::constant((high as u64) << 32u64 | (low as u64))
    }

    #[inline]
    #[verifier(external_body)]
    fn write(&self, value: u64_s, Tracked(perm): Tracked<&mut RegisterPerm>) {
        let low = value.reveal_value() as u32;
        let high = (value.reveal_value() >> 32u64) as u32;

        unsafe {
            asm!(
                "xsetbv",
                in("ecx") 0,
                in("rax") low, in("rdx") high,
                options(nomem, nostack, preserves_flags),
            );
        }
    }
}
}

use crate::BIT64;
crate::macro_const! {
pub const CR4_OSFXSR: u64 = BIT64!(9u64);
pub const CR4_OSXMMEXCPT: u64 = BIT64!(10u64);
pub const CR4_OSXSAVE: u64 = BIT64!(18u64);
pub const CR4_PAE: u64 = BIT64!(5u64);

pub const XCR0_X87: u64 = BIT64!(0);
pub const XCR0_SSE: u64 = BIT64!(1);
pub const XCR0_AVX: u64 = BIT64!(2);
pub const XCR0_YMM: u64 = BIT64!(2);
pub const XCR0_BNDREG: u64 = BIT64!(3);
pub const XCR0_BNDCSR: u64 = BIT64!(4);
pub const XCR0_OPMASK: u64 = BIT64!(5);
pub const XCR0_ZMM_HI256: u64 = BIT64!(6);
pub const XCR0_HI16_ZMM: u64 = BIT64!(7);
}
impl_reg64! {
    CR0, "cr0", Cr0,
    CR3, "cr3", Cr3,
    CR4, "cr4", Cr4,
}

impl_reg16! {
    CS, "cs", Cs,
}

#[macro_export]
macro_rules! impl_dpr {
    ($($typename: ident, $point_type: ty,$name:literal, $rname: ident),*$(,)*) => {
    $(verismo_simple!{
    pub struct $typename;
    impl<'a> AnyRegTrait<$point_type> for $typename {
        open spec fn reg_id(&self) -> RegName {
            crate::arch::reg::RegName::$rname
        }

        open spec fn write_extra_requires(
            &self,
            val: $point_type,
            perm: RegisterPermValue<$point_type>) -> bool
        {
            &&& val.is_constant()
        }

        // Unused read.
        open spec fn read_extra_requires(
            &self,
            perm: RegisterPermValue<$point_type>) -> bool
        {
            true
        }

        // Dead code.
        #[verifier(external_body)]
        fn read(&self, Tracked(perm): Tracked<&RegisterPerm>) -> (ret: $point_type)
        {
            let mut dtp = $point_type::default();
            unsafe {
                //asm!("sidt [{}]", in(reg) &idt, options(nostack, preserves_flags));
                unsafe {
                    core::arch::asm!(
                        concat!("s", $name, " [{}]"),
                        in(reg) &dtp,
                        options(nostack, preserves_flags)
                    );
                }
            }
            dtp
        }

        #[verifier(external_body)]
        fn write(&self, value: $point_type, Tracked(perm): Tracked<&mut RegisterPerm>)
        {
            // asm!("lidt [{}]", in(reg) &value, options(readonly, nostack, preserves_flags));
            unsafe {
                core::arch::asm!(
                    concat!("l", $name, " [{}]"),
                    in(reg) &value,
                    options(readonly, nostack, preserves_flags)
                );
            }
        }
    }
    })*
}
}
