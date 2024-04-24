use super::*;
use crate::arch::reg::*;
use crate::registers::*;

verus! {

#[verifier::publish]
pub const GDT_KERNEL_CS: usize = 1;

#[verifier::publish]
pub const GDT_KERNEL_DS: usize = 3;

#[verifier::publish]
pub const GDTR_LIMIT: u32 = 0xffff_ffff;

#[verifier::publish]
pub const GDTR_BASE: u64 = 0;

} // verus!
verus! {

#[vbit_struct(DescriptorAttr0_7, u64)]
pub struct DescriptorAttr0_7Spec {
    #[vbits(0, 0)]
    pub accessed: u64,
    #[vbits(1, 1)]
    pub write: u64,
    #[vbits(2, 2)]
    pub conform: u64,
    #[vbits(3, 3)]
    pub exe: u64,
    #[vbits(4, 4)]
    pub sys: u64,
    #[vbits(5, 6)]
    pub dpl: u64,
    #[vbits(7, 7)]
    pub present: u64,
}

#[vbit_struct(DescriptorAttr8_11, u64)]
pub struct DescriptorAttr8_11Spec {
    #[vbits(0, 0)]
    pub avl: u64,
    #[vbits(1, 1)]
    pub long: u64,
    #[vbits(2, 2)]
    pub size32_or_16: u64,
    #[vbits(3, 3)]
    pub granularity: u64,
}

#[vbit_struct(Descriptor, u64)]
pub struct DescriptorSpec {
    #[vbits(0, 15)]
    pub limit0_15: u64,
    #[vbits(16, 39)]
    pub base0_23: u64,
    #[vbits(40, 47)]
    pub attr_0_7: u64,
    #[vbits(48, 51)]
    pub limit16_19: u64,
    #[vbits(52, 55)]
    pub attr_8_11: u64,
    #[vbits(56, 64)]
    pub base24_31: u64,
}

} // verus!
verus! {

impl Descriptor {
    pub const fn entry_cs_sys() -> Self {
        Self::empty().set_limit0_15(0xffff).set_limit16_19(0xf).set_base0_23(0).set_base24_31(
            0,
        ).set_attr_0_7(
            DescriptorAttr0_7::empty().set_dpl(0).set_sys(1).set_write(1).set_exe(1).set_present(
                1,
            ).value(),
        ).set_attr_8_11(
            DescriptorAttr8_11::empty().set_long(0).set_size32_or_16(1).set_granularity(1).value(),
        )
        //Descriptor { value: 0xcf9b000000ffff }

    }

    pub const fn entry_cs_user() -> Self {
        Self::entry_cs_sys().set_attr_0_7(
            DescriptorAttr0_7::new(Self::entry_cs_sys().get_attr_0_7()).set_dpl(3).value(),
        )
        //Descriptor { value: 0xcffb000000ffff }

    }

    pub const fn entry_ds_sys() -> Self {
        Self::entry_cs_sys().set_attr_0_7(
            DescriptorAttr0_7::new(Self::entry_cs_sys().get_attr_0_7()).set_exe(0).value(),
        )
        //Descriptor { value: 0xcf93000000ffff }

    }

    pub const fn entry_ds_user() -> Self {
        Self::entry_ds_sys().set_attr_0_7(
            DescriptorAttr0_7::new(Self::entry_cs_sys().get_attr_0_7()).set_dpl(3).value(),
        )
    }
}

} // verus!
verus! {

pub type GDT = Array<u64_s, 32>;

} // verus!
verismo_simple! {
    #[repr(C, packed)]
    #[derive(VDefault)]
    pub struct Gdtr {
        /// Size of the DT.
        pub limit: u16,
        /// Pointer to the memory region containing the DT.
        pub base: u64,
    }
}

crate::impl_dpr! {
    GdtBaseLimit, Gdtr, "gdt", GdtrBaseLimit,
}
