use super::*;
use crate::ptr::SnpPointsToRaw;

verus! {
#[derive(SpecGetter, SpecSetter)]
pub ghost struct CoreMode {
    pub cpu: nat, // CPU index
    pub run: bool,
    pub vmpl: nat, // VMPL index
    pub count: nat, // number of VM exits
    pub sent_ghcb_msrs: Seq<(nat, nat)>, // req, resp,
    pub sent_mem: Seq<((int, nat), SecSeqByte, SecSeqByte)>, // memrange, bytes
}

impl CoreMode {
    pub open spec fn spec_vmgexit(self, ghcbperm: RegisterPermValue<u64_s>, memperm: Option<SnpPointsToRaw>, prev: Self, prev_ghcbperm: RegisterPermValue<u64_s>, prev_memperm: Option<SnpPointsToRaw>) -> bool {
        &&& prev
        .spec_set_count(prev.count + 1)
        .spec_set_sent_ghcb_msrs(prev.sent_ghcb_msrs.push((prev_ghcbperm.value.vspec_cast_to(), ghcbperm.value.vspec_cast_to())))
        .spec_set_sent_mem(
            if memperm.is_Some() {
                prev.sent_mem.push((memperm.get_Some_0()@.range(), prev_memperm.get_Some_0()@.bytes(), memperm.get_Some_0()@.bytes()))
            } else {
                prev.sent_mem
            }
        ) === self
    }
}


#[verifier(external_body)]
pub tracked struct CoreIdPerm {
    no_copy: NoCopy,
}

impl CoreIdPerm {
    pub spec fn view(&self) -> CoreMode;
}

pub open spec fn spec_cpumap_contains_cpu(ap_ids: Map<int, CoreIdPerm>, i: int, vmpl: nat) -> bool {
    ap_ids.contains_key(i) && (ap_ids[i])@.vmpl == vmpl && ap_ids[i]@.cpu == i
}

pub open spec fn spec_ap_ids_wf(ap_ids: Map<int, CoreIdPerm>, bsp: int) -> bool {
    forall |i| (i != bsp) ==> #[trigger]spec_cpumap_contains_cpu(ap_ids, i, 0)
}

pub open spec fn spec_ap_ids_wf_lowerbound(ap_ids: Map<int, CoreIdPerm>, bsp: int, min_cpu: int) -> bool {
    forall |i: int| (i != bsp) && i >= min_cpu ==> #[trigger]spec_cpumap_contains_cpu(ap_ids, i, 0)
}
}
