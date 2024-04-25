use super::*;

impl_secure_type! {(), type}
use vops::VEq;

verismo! {
    // Automatically Add derive(VTypeCast)
    #[repr(C, align(1))]
    struct S1 {
        pub a: (u64, u8),
        pub c: u8,
        pub b: u8,
    }// 9 + 1 + 1 = 11

    #[repr(C, align(1))]
    struct S2 {
        pub a: u64,
        pub b: usize,
        pub c: S1,
    }// 8 + 8 + 11 = 27

    #[repr(C, align(1))]
    struct S3 {
        pub c: S2,
    }// 8 + 8 + 11 = 27

    #[repr(C, align(1))]
    struct S4 {
        pub c: S3,
    }// 8 + 8 + 11 = 27

    proof fn test_type_size2()
    ensures
        S4::spec_size_def() == 27,
        //S4::spec_size_def() == 2,
    {
    }

    #[repr(C, align(1))]
    #[derive(VDefault)]
    pub struct S5 {
        pub a: Ghost<u64>,
        pub t: Tracked<u32>,
        pub c: u64,
    }

    proof fn test_default()
    ensures
        S5::spec_default().a === arbitrary(),
        S5::spec_default().c == 0,
    {}

    fn test_exe_default() -> (ret: S5)
    ensures
        ret.c == 0,
        ret.c@ == u64::spec_default(),
    {
        S5::default()
    }
}
