use super::*;

verus! {
impl<T: WellFormed> WellFormed for Seq<T> {
    open spec fn wf(&self) -> bool {
        &&& forall |i: int| 0 <= i < self.len() ==> (#[trigger]self[i]).wf()
    }
}

impl<T: IsConstant + WellFormed> IsConstant for Seq<T> {
    open spec fn is_constant(&self) -> bool {
        &&& forall |i: int| 0 <= i < self.len() ==> (#[trigger]self[i]).is_constant()
        &&& self.wf()
    }

    open spec fn is_constant_to(&self, vmpl: nat) -> bool {
        &&& forall |i: int| 0 <= i < self.len() ==> (#[trigger]self[i]).is_constant_to(vmpl)
        &&& self.wf()
    }
}

pub open spec fn recursive_sec_bytes<T: ToSecSeq>(s: Seq<T>) -> SecSeqByte
decreases s.len()
{
    if s.len() > 0 {
        let prevs = s.subrange(0, s.len() - 1);
        if prevs.len() < s.len() {
            recursive_sec_bytes(prevs) + s.last().sec_bytes()
        } else {
            Seq::empty()
        }
    } else {
        Seq::empty()
    }
}

impl<T: ToSecSeq> VTypeCast<SecSeqByte> for Seq<T>
{
    open spec fn vspec_cast_to(self) -> SecSeqByte {
        recursive_sec_bytes(self)
    }
}

#[macro_use]
macro_rules! def_basic_tosecseq {
($basetype: ty) => {
    verus!{
    impl VTypeCast<SecSeqByte> for $basetype {
        open spec fn vspec_cast_to(self) -> SecSeqByte {
            let seq: Seq<u8> = self.vspec_cast_to();
            Seq::new(
                seq.len(),
                |i| SpecSecType::constant(seq[i])
            )
        }
    }
    }
}
}
def_basic_tosecseq!{u8}
def_basic_tosecseq!{usize}
def_basic_tosecseq!{u16}
def_basic_tosecseq!{u32}
def_basic_tosecseq!{u64}

pub trait ValSetSize {
    spec fn valset_size(self, vmpl: nat) -> nat where Self: core::marker::Sized
    recommends 1<= vmpl <= 4;
}

pub open spec fn valset_size(s: SecSeqByte, vmpl: nat) -> nat
decreases
    s.len()
{
    if s.len() == 0 {
        1
    } else {
        valset_size(s.subrange(0, s.len() - 1), vmpl) * s.last().valsets[vmpl].len()
    }
}

impl ValSetSize for SecSeqByte {
    open spec fn valset_size(self, vmpl: nat) -> nat
    {
        valset_size(self, vmpl)
    }
}

impl<T: IsFullSecret> IsFullSecret for Seq<T> {
    open spec fn is_fullsecret_to(&self, vmpl: nat) -> bool {
        forall |i| 0<= i < self.len() ==> self[i].is_fullsecret_to(vmpl)
    }
}
}
