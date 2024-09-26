use vstd::slice::slice_index_get;

use super::ghcb::*;
use crate::arch::reg::RegName;
use crate::debug::VPrintAtLevel;
use crate::global::*;
use crate::registers::*;
use crate::snp::SnpCoreSharedMem;
use crate::tspec::*;
use crate::tspec_e::*;
use crate::{BIT32, BIT64};

verus! {

const SNP_CPUID_COUNT_MAX: usize = 64;

} // verus!
verismo_simple! {

#[repr(C, align(1))]
#[derive(VClone, Copy)]
pub struct RegABCD {
    pub eax: u32,
    pub ebx: u32,
    pub ecx: u32,
    pub edx: u32,
}

#[repr(C, align(1))]
#[derive(VClone, Copy)]
pub struct SnpCpuidFn {
    pub eax_in: u32,
    pub ecx_in: u32,
    pub xcr0_in: u64,
    pub xss_in: u64,
    pub rets: RegABCD,
    pub reserved: u64,
}

#[repr(C, align(1))]
#[derive(VClone, Copy)]
pub struct SnpCpuidTable {
    pub count: u32,
    pub reserved_1: u32,
    pub reserved_2: u64,
    pub fn_: Array<SnpCpuidFn, SNP_CPUID_COUNT_MAX>,
    pub reserved_3: [u8; 1008],
}
}

verus! {

impl SnpCpuidTable {
    pub proof fn lemma_size() -> (ret: nat)
        ensures
            (ret == spec_size::<SnpCpuidTable>()),
            ret == 0x1000,
    {
        let ret = spec_size::<SnpCpuidTable>();
        ret
    }
}

} // verus!
verus! {

//AMD 11.3.2 Enabling Extended SSE Instruction Execution
/*See linux/latest/source/arch/x86/include/asm/cpufeatures.h*/
/* CPUID level 0x00000001 (EDX), word 0 */
pub const X86_FEATURE_FXSR: u32 = BIT32!(24);

pub const X86_FEATURE_XMM: u32 = BIT32!(25);

//sse
pub const X86_FEATURE_XMM2: u32 = BIT32!(26);

//sse2
/* Intel-defined CPU features, CPUID level 0x00000001 (ECX), word 4 */

pub const X86_FEATURE_XMM3: u32 = BIT32!(0);

//sse3
pub const X86_FEATURE_PCLMULQDQ: u32 = BIT32!(1);

pub const X86_FEATURE_MOVBE: u32 = BIT32!(22);

pub const X86_FEATURE_AES: u32 = BIT32!(25);

pub const X86_FEATURE_XSAVE: u32 = BIT32!(26);

// XSAVE instruction enabled in the OS
pub const X86_FEATURE_OSXSAVE: u32 = BIT32!(27);

pub const X86_FEATURE_AVX: u32 = BIT32!(28);

//has_aesni && has_pclmulqdq && has_avx && has_sse && has_movbe
pub const EVERCRYPT_USED_FEATURES: u32 = X86_FEATURE_AES | X86_FEATURE_PCLMULQDQ | X86_FEATURE_AVX
    | X86_FEATURE_XMM3;

/* Intel-defined CPU features, CPUID level 0x00000007 (ECX), word 4 */

pub const X86_FEATURE_VPCLMULQDQ: u32 = BIT32!(10);

} // verus!
// return regflag if feature is set
macro_rules! feature {
    ($reg: ident, $feature: ident, $regflag: expr) => {
        if $reg & $feature == $feature {
            $regflag
        } else {
            0
        }
    };
}

verus! {

pub fn process_cpuid(eax: u32, ecx: u32, xcr0: u64, xss: u64, cpuid_table: &[SnpCpuidFn]) -> (ret:
    Option<RegABCD>)
    requires
        cpuid_table@.is_constant(),
    ensures
        ret.is_constant(),
        ret.is_Some() ==> exists|i|
            0 <= i < cpuid_table@.len() && cpuid_table@[i].eax_in@.val == eax
                && cpuid_table@[i].ecx_in@.val == ecx && ret.get_Some_0() === cpuid_table@[i].rets,
{
    let mut i: usize = 0;
    let mut ret = None;
    let n = cpuid_table.len();
    while i < n
        invariant_except_break
            cpuid_table@.is_constant(),
            n == cpuid_table@.len(),
            i.is_constant(),
            0 <= (i as int) <= n,
            forall|k: int|
                0 <= k < (i as int) ==> !(cpuid_table@[k].eax_in@.val == eax
                    && cpuid_table@[k].ecx_in@.val == ecx),
            ret.is_None(),
        ensures
            (0 <= (i as int) < n) == ret.is_Some(),
            (i == n) == ret.is_None(),
            ret.is_Some() ==> cpuid_table@[i as int].eax_in@.val == eax
                && cpuid_table@[i as int].ecx_in@.val == ecx && ret.get_Some_0()
                === cpuid_table@[i as int].rets,
    {
        let leaf = slice_index_get(cpuid_table, i);
        if (eax == leaf.eax_in.into()) && (ecx == leaf.ecx_in.into()) {
            ret = Some(leaf.rets);
            break ;
        }
        i = i + 1;
    }
    return ret;
}

} // verus!
verismo_simple! {
pub trait CryptoFeatures {
    spec fn has_avx_sse_features(&self) -> bool;
}

// hidden bit op
pub closed spec fn cr4_wf_for_crypto(cr4: u64) -> bool {
    true
    //cr4 & CR4_OSFXSR == CR4_OSFXSR
}

// hidden bit op
pub closed spec fn xcr0_wf_for_crypto(xcr0: u64) -> bool {
    xcr0 == (XCR0_X87 | XCR0_AVX | XCR0_SSE)
}

impl CryptoFeatures for Map<RegName, RegisterPerm> {
    // Reveal regs but hide bit ops.
    open spec fn has_avx_sse_features(&self) -> bool {
        let cr4: u64_s = self[RegName::Cr4]@.value();
        let xcr0: u64_s = self[RegName::XCr0]@.value();
        &&& cr4_wf_for_crypto(cr4 as u64_t)
        &&& xcr0_wf_for_crypto(xcr0 as u64_t)
    }
}
}

verus! {

/// Initialize AVX and SSE features for crypto
pub fn init_cpu_for_crypto(cpuid_page: &SnpCpuidTable, Tracked(cs): Tracked<&mut SnpCoreSharedMem>)
    requires
        old(cs).inv(),
        cpuid_page.is_constant(),
    ensures
        cs.inv(),
        cs.snpcore.regs.has_avx_sse_features(),
        cs.only_lock_reg_coremode_updated(
            *old(cs),
            set![RegName::Cr4, RegName::XCr0, GHCB_REGID()],
            set![spec_CONSOLE_lockid()],
        ),
{
    let cpuid_table = cpuid_page.fn_.as_slice();
    process_cpuid(0x8000_001f, 0, 0, 0, cpuid_table);
    let ret = process_cpuid(0x1, 0, 0, 0, cpuid_table);
    let mut feature_flg: u32 = 0;
    if let Some(RegABCD { ecx, .. }) = ret {
        let ecx: u32 = ecx.into();
        if (ecx & EVERCRYPT_USED_FEATURES) != EVERCRYPT_USED_FEATURES {
            proof {
                reveal_strlit("!EVERCRYPT_USED_FEATURES: ");
            }
            (new_strlit("!EVERCRYPT_USED_FEATURES: "), u32_s::new(ecx)).err(Tracked(cs));
            vc_terminate_debug(SM_EVERCRYPT_EXIT, Tracked(cs));
        }
        feature_flg = ecx;
    } else {
        vc_terminate_debug(SM_EVERCRYPT_EXIT, Tracked(cs));
    }
    let tracked mut cr4perm = cs.snpcore.regs.tracked_remove(RegName::Cr4);
    let mut reg = CR4.read(Tracked(&cr4perm));
    let fxsr: u64 = feature!(feature_flg, X86_FEATURE_FXSR, CR4_OSFXSR | CR4_OSXMMEXCPT);
    let xsave: u64 = feature!(feature_flg, X86_FEATURE_XSAVE, CR4_OSXSAVE);
    reg = reg.bitor(fxsr).bitor(xsave);
    CR4.write(reg, Tracked(&mut cr4perm));
    proof {
        cs.snpcore.regs.tracked_insert(RegName::Cr4, cr4perm);
    }
    // Check hardware support
    //let (eax, _, _, _)
    process_cpuid(0xd, 0, 0, 0, cpuid_table);
    let ret = process_cpuid(0x7, 0, 0, 0, cpuid_table);
    if let Some(RegABCD { ecx, .. }) = ret {
        let ecx: u32 = ecx.into();
        if ecx & X86_FEATURE_VPCLMULQDQ != X86_FEATURE_VPCLMULQDQ {
            proof {
                reveal_strlit("!X86_FEATURE_VPCLMULQDQ: ");
            }
            (new_strlit("!X86_FEATURE_VPCLMULQDQ: "), u32_s::new(ecx)).err(Tracked(cs));
            vc_terminate_debug(SM_EVERCRYPT_EXIT, Tracked(cs));
        }
    } else {
        vc_terminate_debug(SM_EVERCRYPT_EXIT, Tracked(cs));
    }
    let tracked mut xcr0perm = cs.snpcore.regs.tracked_remove(RegName::XCr0);
    // set up XFEATURE_MASK in xcr0
    let xcr0 = u64_s::new(XCR0_X87 | XCR0_AVX | XCR0_SSE);
    XCR0.write(xcr0, Tracked(&mut xcr0perm));
    proof {
        cs.snpcore.regs.tracked_insert(RegName::XCr0, xcr0perm);
        reveal_strlit("Crypto CPU init\n");
    }
    new_strlit("Crypto CPU init\n").info(Tracked(cs));
}

} // verus!
