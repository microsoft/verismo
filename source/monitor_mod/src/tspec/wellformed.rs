use super::*;

verus! {

pub trait WellFormed {
    spec fn wf(&self) -> bool;
}

impl WellFormed for () {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl<T1: WellFormed, T2: WellFormed> WellFormed for (T1, T2) {
    open spec fn wf(&self) -> bool {
        self.0.wf() && self.1.wf()
    }
}

impl<T1: WellFormed, T2: WellFormed, T3: WellFormed> WellFormed for (T1, T2, T3) {
    open spec fn wf(&self) -> bool {
        self.0.wf() && self.1.wf() && self.2.wf()
    }
}

impl<T: WellFormed> WellFormed for Option<T> {
    #[verifier(inline)]
    open spec fn wf(&self) -> bool {
        self.is_Some() ==> self.get_Some_0().wf()
    }
}

impl<T> WellFormed for Ghost<T> {
    #[verifier(inline)]
    open spec fn wf(&self) -> bool {
        true
    }
}

impl<T> WellFormed for Tracked<T> {
    #[verifier(inline)]
    open spec fn wf(&self) -> bool {
        true
    }
}

#[macro_export]
    macro_rules! impl_spec_wf_for_basic {
        ($($type: ty),* $(,)?) => {
            $(verus!{
                impl WellFormed for $type {
                    #[verifier(inline)]
                    open spec fn wf(&self) -> bool
                    {
                        true
                    }
                }
            })*
        }
    }

impl_spec_wf_for_basic!{u64, u32, u16, usize, u8, bool, char}

} // verus!
