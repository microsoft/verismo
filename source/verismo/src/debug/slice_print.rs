use vstd::slice::slice_index_get;

use super::*;
use crate::snp::{snpcore_console_wf, SnpCoreConsole, SnpCoreSharedMem};

verus! {

broadcast use crate::group_verismo_default;

} // verus!
verismo_simple! {
impl<T: VPrint> VPrint for [T] {
    open spec fn early_print_requires(&self) -> bool {
        forall |i| 0 <= i < self@.len() ==> (#[trigger] self@[i]).early_print_requires()
    }


    #[verifier::exec_allows_no_decreases_clause]
    fn early_print2(&self, Tracked(snpcore): Tracked<&mut SnpCore>, Tracked(console): Tracked<SnpPointsToRaw>) -> (newconsole: Tracked<SnpPointsToRaw>)
    {
        let table = self;
        let n = usize_s::constant(self.len());
        let n64 = n as u64;
        let ghost input_console = console;
        let tracked mut console = console;
        proof {reveal_strlit("size = ");}
        let Tracked(console) = new_strlit("size = ").early_print2(Tracked(snpcore), Tracked(console));
        let Tracked(console) = n.early_print2(Tracked(snpcore), Tracked(console));
        proof {reveal_strlit("[\n");}
        let Tracked(console) = new_strlit("[\n").early_print2(Tracked(snpcore), Tracked(console));
        let ghost oldsnpcore = *snpcore;
        let ghost oldconsole = console;
        let mut i: usize = 0;
        proof {
            // The prefix prints establish the same GHCB/console frame relation.
            assert(print_ensures_snp_c(oldsnpcore, oldconsole, *snpcore, console));
        }
        while i < n
        invariant
            i <= n,
            i.is_constant(),
            n.is_constant(),
            snpcore.cpu() == oldsnpcore.cpu(),
            snpcore.inv(),
            snpcore_console_wf(oldsnpcore, oldconsole),
            print_ensures_snp_c(oldsnpcore, oldconsole, *snpcore, console),
            n == self@.len(),
            forall |i| 0 <= i < self@.len() ==> (#[trigger] self@[i]).early_print_requires(),
        {
            let Tracked(tmpconsole) =  slice_index_get(self, i.reveal_value()).early_print2(Tracked(snpcore), Tracked(console));
            proof {
                reveal_strlit(" ");
            }
            let Tracked(tmpconsole) = new_strlit(" ").early_print2(Tracked(snpcore), Tracked(tmpconsole));
            proof {
                console = tmpconsole;
                // Element and separator prints compose with the loop's print frame.
                assert(print_ensures_snp_c(oldsnpcore, oldconsole, *snpcore, console));
            }
            i = i + 1;
        }
        proof {
            reveal_strlit("]\n");
        }
        let ret = new_strlit("]\n").early_print2(Tracked(snpcore), Tracked(console));
        proof {
            // The closing bracket print composes with the accumulated frame.
            assert(print_ensures_snp_c(*old(snpcore), input_console, *snpcore, ret@));
        }
        ret
    }
}

impl<T: VPrint + IsConstant + WellFormed, const N: usize_t> VPrint for [T; N] {
    open spec fn early_print_requires(&self) -> bool {
        &&& forall |i| 0 <= i < self@.len() ==> (#[trigger] self@[i]).early_print_requires()
        &&& self.is_constant()
    }

    #[inline]
    fn early_print2(&self, Tracked(snpcore): Tracked<&mut SnpCore>, Tracked(console): Tracked<SnpPointsToRaw>) -> (newconsole: Tracked<SnpPointsToRaw>)
    {
        self.as_slice().early_print2(Tracked(snpcore), Tracked(console))
    }
}
}

verus! {

// slice does not have a size, and so cannot use derived PrintAtAllLevel trait.
// To use derived traits, we use SlicePrinter to print.
pub struct SlicePrinter<'a, T: IsConstant + WellFormed> {
    pub s: &'a [T],
}

} // verus!
verus! {

impl<'a, T: IsConstant + WellFormed + VPrint> VPrint for SlicePrinter<'a, T> {
    open spec fn early_print_requires(&self) -> bool {
        forall|i| 0 <= i < self.s@.len() ==> (#[trigger] self.s@[i]).early_print_requires()
    }

    #[inline]
    fn early_print2(
        &self,
        Tracked(snpcore): Tracked<&mut SnpCore>,
        Tracked(console): Tracked<SnpPointsToRaw>,
    ) -> (newconsole: Tracked<SnpPointsToRaw>) {
        self.s.early_print2(Tracked(snpcore), Tracked(console))
    }
}

} // verus!
