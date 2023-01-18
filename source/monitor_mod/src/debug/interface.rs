use super::*;
use crate::global::*;
use crate::snp::ghcb::GHCB_REGID;
use crate::snp::{snpcore_console_wf, SnpCoreConsole, SnpCoreSharedMem};

verismo_simple! {
    pub struct Console;

    impl Console {
        pub open spec fn invfn() -> spec_fn(Console) -> bool {
            |c: Console| true
        }
    }
}

verus! {
pub open spec fn print_ensures_cc(cc: SnpCoreConsole, ret: SnpCoreConsole) -> bool {
    &&& print_ensures_snp_c(cc.snpcore, cc.console(), ret.snpcore, ret.console())
    &&& cc.wf()
    &&& ret.wf()
}

pub open spec fn print_ensures_snp_c(
    snpcore: SnpCore, console: SnpPointsToRaw, retsnpcore: SnpCore, retconsole: SnpPointsToRaw) -> bool {
    &&& snpcore_console_wf(retsnpcore, retconsole)
    &&& retsnpcore.only_reg_coremode_updated(snpcore, set![GHCB_REGID()])
    &&& retconsole@.only_val_updated(console@)
}

pub open spec fn print_ensures_cs(cs: SnpCoreSharedMem, ret: SnpCoreSharedMem) -> bool {
    &&& ret.inv()
    &&& ret.only_lock_reg_coremode_updated(
        cs, set![GHCB_REGID()],
        set![spec_CONSOLE().lockid()],
    )
    &&& ret.lockperms.contains_vlock(spec_CONSOLE())
    &&& forall |id| id != spec_CONSOLE().lockid() && cs.lockperms.contains_key(id) ==> (#[trigger]ret.lockperms[id]) === cs.lockperms[id] && ret.lockperms.contains_key(id)
    &&& cs.inv()
}

pub trait VPrintCC {
    spec fn early_print_cc_requires(&self) -> bool;

    fn early_print(&self, Tracked(cc): Tracked<&mut SnpCoreConsole>)
    requires
        self.early_print_cc_requires(),
        old(cc).wf(),
    ensures
        print_ensures_cc(*old(cc), *cc);
}

// Basic traits
pub trait VPrint {
    spec fn early_print_requires(&self) -> bool;

    fn early_print2(&self, Tracked(snpcore): Tracked<&mut SnpCore>, Tracked(console): Tracked<SnpPointsToRaw>) -> (newconsole: Tracked<SnpPointsToRaw>)
    requires
        self.early_print_requires(),
        snpcore_console_wf(*old(snpcore), console),
    ensures
        print_ensures_snp_c(*old(snpcore), console, *snpcore, newconsole@);
}

impl<T: ?Sized + VPrint> VPrintCC for T {
    open spec fn early_print_cc_requires(&self) -> bool {
        self.early_print_requires()
    }

    fn early_print(&self, Tracked(cc): Tracked<&mut SnpCoreConsole>)
    {
        let Tracked(console) = self.early_print2(
            Tracked(&mut cc.snpcore), Tracked(cc.console.tracked_remove(0))
        );
        proof{cc.console.tracked_insert(0, console);}
    }
}

// derived from VPrint
pub trait VPrintLock {
    spec fn lock_print_requires(&self, cs: SnpCoreSharedMem) -> bool;
    fn print(&self, Tracked(cs): Tracked<&mut SnpCoreSharedMem>)
    requires
        self.lock_print_requires(*old(cs)),
    ensures
        print_ensures_cs(*old(cs), *cs);
}

// derived from VPrint
pub trait VEarlyPrintAtLevel {
    spec fn print_level_requires(&self, cs: SnpCoreConsole) -> bool;
    spec fn print_ensures(&self, prevcs: SnpCoreConsole, cs: SnpCoreConsole) -> bool;

    fn leak_debug(&self);

    fn debug(&self, Tracked(cs): Tracked<&mut SnpCoreConsole>)
    requires
        self.print_level_requires(*old(cs)),
    ensures
        print_ensures_cc(*old(cs), *cs),
        self.print_ensures(*old(cs), *cs);

    fn info(&self, Tracked(cs): Tracked<&mut SnpCoreConsole>)
    requires
        self.print_level_requires(*old(cs)),
    ensures
        print_ensures_cc(*old(cs), *cs),
        self.print_ensures(*old(cs), *cs);

    fn err(&self, Tracked(cs): Tracked<&mut SnpCoreConsole>)
    requires
        self.print_level_requires(*old(cs)),
    ensures
        print_ensures_cc(*old(cs), *cs),
        self.print_ensures(*old(cs), *cs);

}

// derived from VPrintLock
pub trait VPrintAtLevel {
    spec fn print_level_requires(&self, cs: SnpCoreSharedMem) -> bool;
    spec fn print_ensures(&self, prevcs: SnpCoreSharedMem, cs: SnpCoreSharedMem) -> bool;
    fn leak_debug(&self);
    fn debug(&self, Tracked(cs): Tracked<&mut SnpCoreSharedMem>)
    requires
        self.print_level_requires(*old(cs)),
    ensures
        print_ensures_cs(*old(cs), *cs),
        self.print_ensures(*old(cs), *cs);

    fn info(&self, Tracked(cs): Tracked<&mut SnpCoreSharedMem>)
    requires
        self.print_level_requires(*old(cs)),
    ensures
        print_ensures_cs(*old(cs), *cs),
        self.print_ensures(*old(cs), *cs);

    fn err(&self, Tracked(cs): Tracked<&mut SnpCoreSharedMem>)
    requires
        self.print_level_requires(*old(cs)),
    ensures
        print_ensures_cs(*old(cs), *cs),
        self.print_ensures(*old(cs), *cs);
}
}
