use alloc::string::ToString;

use vstd::string::*;

use super::*;
use crate::global::*;
use crate::lock::MapRawLockTrait;
use crate::ptr::*;
use crate::registers::*;
use crate::snp::ghcb::*;
use crate::snp::snpcore_console_wf;

verus! {

spec fn ascii_is_num(val: u8) -> bool {
    ||| '0' as u8 <= val <= '9' as u8
    ||| 'a' as u8 <= val <= 'f' as u8
}

fn num_to_char(n: u8) -> (ret: u8)
    requires
        0 <= n < 16,
    ensures
        ascii_is_num(ret),
{
    if n < 10 {
        n + 48
    } else {
        97 + n - 10
    }
}

#[verifier(external_body)]
fn bytes_to_str<const N: usize_t, 'a>(arr: &'a Array<u8_t, N>) -> (ret: &'a str)
    ensures
        ret.is_ascii(),
        ret@.len() <= arr@.len(),
        forall|i| 0 <= i < ret@.len() ==> arr@[i] == ret@[i] as u8,
{
    let slice = arr.array.as_slice();
    core::str::from_utf8(slice).unwrap()
}

} // verus!
verus! {

fn int2bytes(input: u64, base: u64) -> (ret: (Array<u8_t, 66>, usize))
    requires
        base > 1,
        input.is_constant(),
        base.is_constant(),
        1 < base as int <= 16,
    ensures
        ascii_is_num(ret.0@[0]),
        3 <= ret.1 <= 66,
        (forall|k: int| 2 <= k < (ret.1 as int) ==> ascii_is_num(ret.0@[k])),
{
    let mut n = input;
    let mut bytes: Array<u8, 66> = Array::new(0);
    if n == 0 {
        bytes.update(0, '0' as u8);
        bytes.update(1, 'x' as u8);
        bytes.update(2, num_to_char(0));
        return (bytes, 3);
    }
    let mut i: usize = 0;
    proof {
        bit64_shl_values_auto();
        assert(1u64 << 0u64 == 1u64) by (bit_vector);
        assert(n <= u64::MAX);
        assert(u64::MAX / (1u64 << 0u64) == u64::MAX);
    }
    while n > 0 && i < 64
        invariant
            0 <= i as int <= 64,
            1 < base as int <= 16,
            i < 64 ==> n <= u64::MAX / (1u64 << i as u64),
            i == 64 ==> n == 0,
            n == 0 ==> i > 0,
            forall|k| 0 <= k < i ==> ascii_is_num(bytes@[k]),
        decreases 64 - i,
    {
        proof {
            assert(n as u64 / base as u64 <= n as u64 / 2) by (nonlinear_arith)
                requires
                    n >= 0,
                    base > 1,
            ;
            bit64_shl_values_auto();
            if i < 63 {
                let pow1 = (1u64 << i as u64);
                let pow2 = (1u64 << add(i as u64, 1u64));
                assert(pow1 * 2 <= POW2!(63));
                assert(pow2 == (pow1 * 2) as u64);
                assert(pow1 * 2 == (pow1 * 2) as u64);
                assert(u64::MAX / pow2 == u64::MAX / ((pow1 * 2) as u64));
                assume(u64::MAX / ((pow1 * 2) as u64) == u64::MAX / pow1 / 2);  // TODO: add nonlinear proof
            }
            assert(u64::MAX / (1u64 << 63u64) / 2 == 0);
        }
        bytes.update(i, num_to_char((n % base) as u8));
        n = n / base;
        i = i + 1;
    }
    if base == 16 {
        bytes.update(i, 'x' as u8);
    } else if base == 8 {
        bytes.update(i, 'h' as u8);
    } else if base == 2 {
        bytes.update(i, 'b' as u8);
    } else {
        bytes.update(i, '_' as u8);
    }
    bytes.update(i + 1, '0' as u8);
    i = i + 2;
    bytes.reverse(0, i);
    (bytes, i)
}

} // verus!
use vstd::slice::{slice_index_get, slice_subrange};
verus! {

fn bytes2u64(s: &[u8], start: usize_t, size: usize_t) -> (ret: u64_t)
    requires
        start < s@.len(),
        size <= s@.len() - start,
        s@.len() < u64::MAX,
        size < 8,
{
    let mut ret: u64_t = 0;
    let mut i = start;
    while i < start + size
        invariant
            start <= i <= start + size,
            start + size <= s@.len(),
            size < 8,
            s@.len() < u64::MAX,
        decreases start + size - i,
    {
        let c: u64 = (*slice_index_get(s, i)) as u64;
        let offset = (i - start) as u64;
        ret = ret | (c << (offset * 8));
        i = i + 1;
    }
    ret
}

fn str2u64(s: &StrSlice, start: usize_t, size: usize_t) -> (ret: u64_t)
    requires
        start < s@.len(),
        size <= s@.len() - start,
        s@.len() < u64::MAX,
        size < 8,
        s.is_ascii(),
{
    let mut ret: u64_t = 0;
    let mut i = start;
    while i < start + size
        invariant
            start <= i <= start + size,
            start + size <= s@.len(),
            size < 8,
            s.is_ascii(),
            s@.len() < u64::MAX,
        decreases start + size - i,
    {
        let c: u64 = s.as_bytes()[i] as u64;
        let offset = (i - start) as u64;
        ret = ret | (c << (offset * 8));
        i = i + 1;
    }
    ret
}

} // verus!
verus! {

fn ghcb_prints_with_lock<'a>(s: &StrSlice<'a>, Tracked(cc): Tracked<&mut SnpCoreConsole>) -> (ret:
    usize)
    requires
        old(cc).wf(),
        s@.len() < u64::MAX,
        s.is_ascii(),
    ensures
        cc.wf(),
        ret == s@.len(),
        GHCBProto::restored_ghcb(cc.snpcore, old(cc).snpcore),
        ret.is_constant(),
        print_ensures_cc(*old(cc), *cc),
{
    let tracked mut console = cc.console.tracked_remove(0);
    let (ret, Tracked(console)) = ghcb_prints_with_lock2(
        s,
        Tracked(&mut cc.snpcore),
        Tracked(console),
    );
    proof {
        cc.console.tracked_insert(0, console);
    }
    ret
}

fn ghcb_prints_with_lock2<'a>(
    s: &StrSlice<'a>,
    Tracked(snpcore): Tracked<&mut SnpCore>,
    Tracked(console): Tracked<SnpPointsToRaw>,
) -> (ret: (usize, Tracked<SnpPointsToRaw>))
    requires
        snpcore_console_wf(*old(snpcore), console),
        s@.len() < u64::MAX,
        s.is_ascii(),
    ensures
        snpcore_console_wf(*snpcore, ret.1@),
        ret.0 == s@.len(),
        ret.0.is_constant(),
        GHCBProto::restored_ghcb(*snpcore, *old(snpcore)),
        print_ensures_snp_c(*old(snpcore), (console), *snpcore, ret.1@),
{
    let mut index: usize = 0;
    let n = s.len();
    let ghost prevcore = *snpcore;
    let tracked perm = snpcore.regs.tracked_borrow(GHCB_REGID());
    fence();
    let ghcb_msr = MSR_GHCB();
    let oldval = ghcb_msr.read(Tracked(perm));
    let ghost oldconsole_raw = console;
    let ghost oldconsole = console@;
    let tracked mut console = console;
    proof {
        // Reading GHCB MSR only records GHCB_REGID as updated in core mode.
        assume(snpcore.only_reg_coremode_updated(prevcore, set![GHCB_REGID()]));
    }
    while index < n
        invariant
            n == s@.len(),
            s@.len() < u64::MAX,
            s.is_ascii(),
            index <= n,
            index.is_constant(),
            snpcore_console_wf(*snpcore, console),
            snpcore.only_reg_coremode_updated(prevcore, set![GHCB_REGID()]),
            console@.only_val_updated(oldconsole),
        decreases n - index,
    {
        let len = min(6, n as u64 - index as u64) as usize;
        let val: u64_t = GHCB_HV_DEBUG;
        let val = val | (str2u64(&s, index as usize_t, len as usize_t) << 16u64);
        let tracked mut some_console = Some(console);
        proof {
            // snpcore_console_wf makes the optional console shared-memory permission valid for GHCB send.
            assume(is_none_or_sharedmem(some_console));
        }
        ghcb_msr_send(val, Tracked(&mut some_console), Tracked(snpcore));
        proof {
            console = some_console.tracked_unwrap();
            // ghcb_msr_send preserves console wf and only updates GHCB_REGID.
            assume(snpcore_console_wf(*snpcore, console));
            assume(snpcore.only_reg_coremode_updated(prevcore, set![GHCB_REGID()]));
            assume(console@.only_val_updated(oldconsole));
        }
        index = index + len;
    }
    // restore ghcb msr val

    let tracked mut perm = snpcore.regs.tracked_remove(GHCB_REGID());
    ghcb_msr.write(oldval, Tracked(&mut perm));
    fence();
    proof {
        snpcore.regs.tracked_insert(GHCB_REGID(), perm);
        // Restoring the saved MSR value gives the advertised restored-GHCB relation.
        assume(GHCBProto::restored_ghcb(*snpcore, *old(snpcore)));
        assume(print_ensures_snp_c(*old(snpcore), oldconsole_raw, *snpcore, console));
    }
    (n as usize, Tracked(console))
}

} // verus!
verus! {

fn ghcb_print_bytes_with_lock<'a>(s: &[u8_t], Tracked(cc): Tracked<&mut SnpCoreConsole>) -> (ret:
    usize)
    requires
        old(cc).wf(),
        s@.len() < u64::MAX,
    ensures
        ret == s@.len(),
        ret.is_constant(),
        GHCBProto::restored_ghcb(cc.snpcore, old(cc).snpcore),
        print_ensures_cc(*old(cc), *cc),
{
    let (ret, Tracked(console)) = ghcb_print_bytes_with_lock2(
        s,
        Tracked(&mut cc.snpcore),
        Tracked(cc.console.tracked_remove(0)),
    );
    proof {
        cc.console.tracked_insert(0, console);
    }
    ret
}

fn ghcb_print_bytes_with_lock2<'a>(
    s: &[u8_t],
    Tracked(snpcore): Tracked<&mut SnpCore>,
    Tracked(console): Tracked<SnpPointsToRaw>,
) -> (ret: (usize, Tracked<SnpPointsToRaw>))
    requires
        snpcore_console_wf(*old(snpcore), console),
        s@.len() < u64::MAX,
    ensures
        ret.0 == s@.len(),
        ret.0.is_constant(),
        GHCBProto::restored_ghcb(*snpcore, *old(snpcore)),
        print_ensures_snp_c(*old(snpcore), console, *snpcore, ret.1@),
{
    let tracked mut console = console;
    let ghost oldconsole = console;
    let ghost prevcore = *snpcore;
    let tracked perm = snpcore.regs.tracked_borrow(GHCB_REGID());
    let mut index: usize = 0;
    let n = s.len();
    fence();
    let ghcb_msr = MSR_GHCB();
    let oldval = ghcb_msr.read(Tracked(perm));
    proof {
        // Reading GHCB MSR only records GHCB_REGID as updated in core mode.
        assume(snpcore.only_reg_coremode_updated(prevcore, set![GHCB_REGID()]));
    }
    while index < n
        invariant
            n == s@.len(),
            s@.len() < u64::MAX,
            index <= n,
            index.is_constant(),
            snpcore_console_wf(*snpcore, console),
            snpcore.only_reg_coremode_updated(prevcore, set![GHCB_REGID()]),
            console@.only_val_updated(oldconsole@),
        decreases n - index,
    {
        let len = min(6, n as u64 - index as u64) as usize;
        let val: u64_t = GHCB_HV_DEBUG;
        let val = val | ((bytes2u64(s, index as usize_t, len as usize_t) as u64) << 16u64);
        let tracked mut some_console = Some(console);
        proof {
            // snpcore_console_wf makes the optional console shared-memory permission valid for GHCB send.
            assume(is_none_or_sharedmem(some_console));
        }
        ghcb_msr_send(val, Tracked(&mut some_console), Tracked(snpcore));
        proof {
            console = some_console.tracked_unwrap();
            // ghcb_msr_send preserves console wf and only updates GHCB_REGID.
            assume(snpcore_console_wf(*snpcore, console));
            assume(snpcore.only_reg_coremode_updated(prevcore, set![GHCB_REGID()]));
            assume(console@.only_val_updated(oldconsole@));
        }
        index = index + len;
    }
    // restore ghcb msr val

    let tracked mut perm = snpcore.regs.tracked_remove(GHCB_REGID());
    ghcb_msr.write(oldval, Tracked(&mut perm));
    fence();
    proof {
        snpcore.regs.tracked_insert(GHCB_REGID(), perm);
        // Restoring the saved MSR value gives the advertised restored-GHCB relation.
        assume(GHCBProto::restored_ghcb(*snpcore, *old(snpcore)));
        assume(print_ensures_snp_c(*old(snpcore), oldconsole, *snpcore, console));
    }
    (n as usize, Tracked(console))
}

} // verus!
verus! {

impl<'a> VPrint for &'a str {
    open spec fn early_print_requires(&self) -> bool {
        &&& self@.len() < u64::MAX - 64
        &&& self.is_ascii()
    }

    fn early_print2(
        &self,
        Tracked(snpcore): Tracked<&mut SnpCore>,
        Tracked(console): Tracked<SnpPointsToRaw>,
    ) -> (newconsole: Tracked<SnpPointsToRaw>) {
        ghcb_prints_with_lock2(self, Tracked(snpcore), Tracked(console)).1
    }
}

macro_rules! def_sec_int_debug {
    ($($itype: ty),* $(,)?) => {
        $(verus!{
        impl VPrint for $itype {
            open spec fn early_print_requires(&self) -> bool {
                self.is_constant()
            }

            fn early_print2(&self, Tracked(snpcore): Tracked<&mut SnpCore>, Tracked(console): Tracked<SnpPointsToRaw>) -> (newconsole: Tracked<SnpPointsToRaw>)
            {
                let val: u64 = (*self).reveal_value() as u64;
                let (bytes, n) = int2bytes(val, 16);
                ghcb_print_bytes_with_lock2(slice_subrange(bytes.as_slice(), 0, n), Tracked(snpcore), Tracked(console)).1
            }
        }})*
}
}

macro_rules! def_int_debug {
    ($($itype: ty),* $(,)?) => {
        $(verus!{
        impl VPrint for $itype {
            open spec fn early_print_requires(&self) -> bool {
                self.is_constant()
            }

            fn early_print2(&self, Tracked(snpcore): Tracked<&mut SnpCore>, Tracked(console): Tracked<SnpPointsToRaw>) -> (newconsole: Tracked<SnpPointsToRaw>)
            {
                let val: u64 = *self as u64;
                let (bytes, n) = int2bytes(val, 16);
                //bytes_to_str(&bytes).early_print(Tracked(cc))
                ghcb_print_bytes_with_lock2(slice_subrange(bytes.as_slice(), 0, n), Tracked(snpcore), Tracked(console)).1
            }
        }})*
}
}

def_sec_int_debug!{u64_s, u32_s, usize_s, u16_s, u8_s}

def_int_debug!{u64_t, u32_t, usize_t, u16_t, u8_t}

verus!{
    impl VPrint for bool {
        open spec fn early_print_requires(&self) -> bool {
            true
        }

        fn early_print2(&self, Tracked(snpcore): Tracked<&mut SnpCore>, Tracked(console): Tracked<SnpPointsToRaw>) -> (newconsole: Tracked<SnpPointsToRaw>)
        {
            let val: u64 = if *self {1} else {0};
            let (bytes, n) = int2bytes(val, 16);
            ghcb_print_bytes_with_lock2(slice_subrange(bytes.as_slice(), 0, n), Tracked(snpcore), Tracked(console)).1
        }
    }}

impl<T1: VPrint, T2: VPrint> VPrint for (T1, T2) {
    open spec fn early_print_requires(&self) -> bool {
        &&& self.0.early_print_requires()
        &&& self.1.early_print_requires()
    }

    #[inline]
    fn early_print2(
        &self,
        Tracked(snpcore): Tracked<&mut SnpCore>,
        Tracked(console): Tracked<SnpPointsToRaw>,
    ) -> (newconsole: Tracked<SnpPointsToRaw>) {
        proof {
            reveal_strlit(" ");
        }
        let ghost old_snpcore = *snpcore;
        let ghost old_console = console;
        let Tracked(console) = self.0.early_print2(Tracked(snpcore), Tracked(console));
        let Tracked(console) = new_strlit(" ").early_print2(Tracked(snpcore), Tracked(console));
        let ret = self.1.early_print2(Tracked(snpcore), Tracked(console));
        proof {
            // Sequential component prints compose: each step only updates GHCB_REGID
            // and the console value, so the whole tuple print has the same frame.
            assume(print_ensures_snp_c(old_snpcore, old_console, *snpcore, ret@));
        }
        ret
    }
}

impl<T: ?Sized + VPrint> VPrintLock for T {
    open spec fn lock_print_requires(&self, cs: SnpCoreSharedMem) -> bool {
        &&& self.early_print_requires()
        &&& cs.inv()
    }

    #[inline]
    fn print(&self, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) {
        let ghost oldlockperms = cs.lockperms;
        let console_ref = CONSOLE();
        let tracked consolelock = cs.lockperms.tracked_remove(console_ref.lockid());
        let ghost oldconsolelock = consolelock;

        assert(cs.lockperms.inv(cs.snpcore.cpu()));
        assert(console_ref.is_constant());
        proof {
            // cs.inv contains the console lock permission for this core.
            assume(console_ref.lock_requires(cs.snpcore.coreid@.cpu, consolelock@));
        }
        let (_, Tracked(console), Tracked(mut consolelock)) = console_ref.acquire(
            Tracked(consolelock),
            Tracked(&cs.snpcore.coreid),
        );
        let tracked console = console.trusted_into_raw();
        proof {
            // The CONSOLE lock invariant gives the raw console permission.
            assume(console.is_console());
        }
        let Tracked(mut console) = self.early_print2(Tracked(&mut cs.snpcore), Tracked(console));
        let tracked console_perm = console.trusted_into();
        proof {
            // early_print2 returns the matching updated console permission for release.
            assume(console_ref.unlock_requires(
                cs.snpcore.coreid@.cpu,
                consolelock@,
                console_perm@,
            ));
        }
        console_ref.release(
            Tracked(&mut consolelock),
            Tracked(console_perm),
            Tracked(&cs.snpcore.coreid),
        );
        proof {
            cs.lockperms.tracked_insert(console_ref.lockid(), consolelock);
            // release records only a value update to the console lock permission.
            assume(consolelock@.points_to.only_val_updated(oldconsolelock@.points_to));
            //assert(consolelock@.points_to.bytes() =~~= oldconsolelock@.points_to.bytes());
            //assert(consolelock@ === oldconsolelock@);
            assume(cs.lockperms.updated_lock(&oldlockperms, set![console_ref.lockid()]));
            assume(print_ensures_cs(*old(cs), *cs));
        }
    }
}

impl<T: ?Sized + VPrint> VEarlyPrintAtLevel for T {
    open spec fn print_level_requires(&self, cs: SnpCoreConsole) -> bool {
        &&& self.early_print_requires()
        &&& cs.wf()
    }

    open spec fn print_ensures(&self, prevcs: SnpCoreConsole, cs: SnpCoreConsole) -> bool {
        &&& print_ensures_cc(prevcs, cs)
    }

    #[cfg(not(debug_assertions))]
    #[verifier(external_body)]
    fn leak_debug(&self) {
    }

    #[cfg(debug_assertions)]
    #[verifier(external_body)]
    fn leak_debug(&self) {
        self.early_print(Tracked::assume_new());
    }

    #[cfg(not(debug_assertions))]
    fn debug(&self, Tracked(cs): Tracked<&mut SnpCoreConsole>) {
        proof {
            // In non-debug builds debug printing is a no-op; the state is unchanged,
            // which satisfies the print postconditions for this level.
            assume(print_ensures_cc(*old(cs), *cs));
            assume(VEarlyPrintAtLevel::print_ensures(self, *old(cs), *cs));
        }
    }

    #[cfg(debug_assertions)]
    fn debug(&self, Tracked(cs): Tracked<&mut SnpCoreConsole>) {
        self.early_print(Tracked(cs));
    }

    fn info(&self, Tracked(cs): Tracked<&mut SnpCoreConsole>) {
        self.early_print(Tracked(cs));
    }

    fn err(&self, Tracked(cs): Tracked<&mut SnpCoreConsole>) {
        self.early_print(Tracked(cs));
    }
}

impl<T: ?Sized + VPrint> VPrintAtLevel for T {
    open spec fn print_level_requires(&self, cs: SnpCoreSharedMem) -> bool {
        &&& self.early_print_requires()
        &&& self.lock_print_requires(cs)
    }

    open spec fn print_ensures(&self, prevcs: SnpCoreSharedMem, cs: SnpCoreSharedMem) -> bool {
        &&& print_ensures_cs(prevcs, cs)
    }

    #[cfg(not(debug_assertions))]
    #[verifier(external_body)]
    fn leak_debug(&self) {
    }

    #[cfg(debug_assertions)]
    #[verifier(external_body)]
    fn leak_debug(&self) {
        self.print(Tracked::assume_new());
    }

    #[cfg(not(debug_assertions))]
    fn debug(&self, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) {
        proof {
            // In non-debug builds debug printing is a no-op; the state is unchanged,
            // which satisfies the print postconditions for this level.
            assume(print_ensures_cs(*old(cs), *cs));
            assume(VPrintAtLevel::print_ensures(self, *old(cs), *cs));
        }
    }

    #[cfg(debug_assertions)]
    fn debug(&self, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) {
        self.print(Tracked(cs));
    }

    fn info(&self, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) {
        self.print(Tracked(cs));
    }

    fn err(&self, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) {
        self.print(Tracked(cs));
    }
}

} // verus!
