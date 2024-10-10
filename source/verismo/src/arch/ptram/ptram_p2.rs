use super::*;
use crate::arch::attack::*;
use crate::arch::memop::MemOp;
use crate::arch::rmp::{RmpEntry, RmpMap, *};
use crate::arch::vram::VRamDB;

verus! {

impl GuestPTRam {
    pub proof fn lemma_write_pte_inv_ppn(
        old_pt: &Self,
        new_pt: &Self,
        sysmap: SysMap,
        memid: MemID,
        memop: MemOp<GuestPhy>,
        gvn: GVN,
        lvl: PTLevel,
    )
        requires
            old_pt.inv(memid),
            memid.is_vmpl0(),
            gvn.is_valid(),
            memop.is_valid(),
            memop.is_Write(),
            memop.to_memid().is_sm(memid) ==> old_pt.spec_ram().gpmemop_requires(memop, sysmap),
            new_pt.l0_entry(memid) === old_pt.l0_entry(memid),
            new_pt === &old_pt.spec_set_ram(old_pt.spec_ram().op(sysmap, memop).to_result()),
            new_pt.map_entry_exe_ok(memid, gvn, lvl).is_Some(),
            old_pt.spec_ram().op(sysmap, memop).is_Ok(),
        ensures
            old_pt.map_entry_exe_ok(memid, gvn, lvl).is_Some(),
            ({
                ||| old_pt.map_entry_gpa_ok(memid, gvn, lvl).get_Some_0() !== memop.to_mem()
                ||| !memop.to_memid().is_sm(memid)
                ||| memop.to_memid().to_asid() !== memid.to_asid()
            }) ==> {
                new_pt.map_entry_exe_ok(memid, gvn, lvl).get_Some_0() === old_pt.map_entry_exe_ok(
                    memid,
                    gvn,
                    lvl,
                ).get_Some_0()
            },
            ({
                &&& old_pt.map_entry_gpa_ok(memid, gvn, lvl).get_Some_0() === memop.to_mem()
                &&& memop.to_memid().is_sm(memid)
                &&& memop.to_memid().to_asid() == memid.to_asid()
            }) ==> {
                new_pt.map_entry_exe_ok(memid, gvn, lvl).get_Some_0() === stream_to_data(
                    memop.get_Write_2(),
                ) && new_pt.map_entry_exe_ok(memid, gvn, lvl).get_Some_0().view().spec_ppn()
                    === old_pt.map_entry_exe_ok(memid, gvn, lvl).get_Some_0().view().spec_ppn()
            },
        decreases lvl.as_int(),
    {
        let pte = new_pt.map_entry_exe_ok(memid, gvn, lvl);
        let old_pte = old_pt.map_entry_exe_ok(memid, gvn, lvl);
        let pte_gpa = new_pt.map_entry_gpa_ok(memid, gvn, lvl);
        let old_pte_gpa = old_pt.map_entry_gpa_ok(memid, gvn, lvl);
        match lvl.parent_lvl() {
            Option::Some(next_lvl) => {
                Self::lemma_write_pte_inv_ppn(old_pt, new_pt, sysmap, memid, memop, gvn, next_lvl);
                assert(pte_gpa === old_pte_gpa);
                assert(pte_gpa.is_Some());
            },
            _ => {
                assert(pte_gpa === old_pte_gpa) by {
                    reveal_with_fuel(GuestPTRam::pgtb_walk_addrs_recursive_ok, 1);
                }
            },
        }
        assert(pte_gpa === old_pte_gpa);
        assert(pte.is_Some());
        if let MemOp::Write(_, enc, data) = memop {
            let write_pte: GuestPTEntry = stream_to_data(data);
            let gpmem_id = memop.to_addr_memid();
            let AddrMemID { range: wgpmem, memid: op_memid } = gpmem_id;
            assert(old_pt.spec_ram().inv()) by {
                reveal(GuestPTRam::inv_dom_ok);
            }
            let pte_gpa = pte_gpa.get_Some_0();
            assert(old_pt.map_entry_gpa_ok(memid, gvn, lvl).is_Some());
            let old_pte_gpa = old_pte_gpa.get_Some_0();
            assert(memtype(memid, old_pte_gpa.to_page()).is_PTE()) by {
                old_pt.lemma_map_entry_gpa_is_pte_type(memid, gvn, lvl);
            }
            assert(old_pte_gpa.to_page().is_valid()) by {
                old_pt.lemma_map_entry_gpa_ok_valid(memid, gvn, lvl);
            }
            reveal_with_fuel(GuestPTRam::pgtb_walk_addrs_recursive_ok, 1);
            if gpmem_id.memtype().is_PTE() {
                old_pt.spec_ram().lemma_write_sm_int_ok(memid, memop, sysmap);
                if !memop.to_memid().is_sm(memid) || !enc {
                    old_pt.spec_ram().lemma_write_bytes_effect_by_other_vm_or_shared(
                        &new_pt.spec_ram(),
                        sysmap,
                        memop,
                        memid,
                        old_pte_gpa,
                    );
                    assert(old_pt.spec_ram().get_enc_bytes_ok(
                        AddrMemID { memid, range: old_pte_gpa },
                    ) === new_pt.spec_ram().get_enc_bytes_ok(
                        AddrMemID { memid, range: old_pte_gpa },
                    ));
                    assert(pte === old_pte);
                } else {
                    assert(old_pt.spec_ram().gpmemop_requires(memop, sysmap));
                    assert(old_pt.spec_ram().pte_write_requires_nosysmap(gpmem_id, true, data));
                    if (old_pte.is_Some()) {
                        assert(rmp_has_gpn_memid(
                            &old_pt.spec_ram().rmp,
                            old_pte_gpa.to_page(),
                            memid,
                        ));
                        if (!rmp_has_gpn_memid(
                            &old_pt.spec_ram().rmp,
                            wgpmem.to_page(),
                            op_memid,
                        )) {
                            assert(wgpmem.to_page() !== old_pte_gpa.to_page());
                        }
                    } else {
                        assert(!rmp_has_gpn_memid(
                            &old_pt.spec_ram().rmp,
                            old_pte_gpa.to_page(),
                            memid,
                        ));
                        old_pt.spec_ram().proof_rmp_check_access_rmp_has_gpn_memid(memop, sysmap);
                        assert(wgpmem.to_page() !== old_pte_gpa.to_page());
                        assert(wgpmem.disjoint(old_pte_gpa));
                    }
                    assert(spec_size::<GuestPTEntry>() == PT_ENTRY_SIZE);
                    assert(wgpmem.len() == 0 || (wgpmem.len() == PT_ENTRY_SIZE as int
                        && wgpmem.is_aligned(PT_ENTRY_SIZE as int)) || wgpmem.disjoint(
                        old_pte_gpa,
                    ));
                    if (wgpmem.len() == PT_ENTRY_SIZE as int && wgpmem.is_aligned(
                        PT_ENTRY_SIZE as int,
                    )) {
                        GPMem::lemma_aligned_mem_eq_or_disjoint(
                            old_pte_gpa,
                            wgpmem,
                            PT_ENTRY_SIZE as int,
                        );
                    }
                    if old_pte_gpa === wgpmem {
                        assert(enc);
                        old_pt.spec_ram().lemma_write_enc_bytes_effect_same_read(
                            &new_pt.spec_ram(),
                            sysmap,
                            memop,
                            memid,
                            old_pte_gpa,
                        );
                        assert(op_memid.to_asid() === memid.to_asid());
                        assert(pte.get_Some_0() === write_pte);
                        assert(op_memid.is_sm(memid));
                        let old_value: Option<GuestPTEntry> = old_pt.spec_ram().get_enc_data_ok(
                            memop.to_addr_memid(),
                        );
                        assert(old_value.is_Some()) by {
                            old_pt.spec_ram().lemma_write_enc_must_has_gpn_in_rmp(
                                memid,
                                memop,
                                sysmap,
                            );
                        }
                        assert(write_pte.view().spec_ppn()
                            === old_pte.get_Some_0().view().spec_ppn());
                    } else {
                        old_pt.spec_ram().lemma_write_enc_bytes_effect_disjoint_read(
                            &new_pt.spec_ram(),
                            sysmap,
                            memop,
                            memid,
                            old_pte_gpa,
                        );
                        assert(pte === old_pte);
                    }
                }
            } else {
                assert(memtype(memid, old_pte_gpa.to_page()).is_PTE());
                old_pte_gpa.lemma_disjoint(wgpmem);
                old_pt.spec_ram().lemma_write_enc_bytes_effect_disjoint_read(
                    &new_pt.spec_ram(),
                    sysmap,
                    memop,
                    memid,
                    old_pte_gpa,
                );
                assert(old_pt.spec_ram().get_enc_bytes_ok(AddrMemID { memid, range: old_pte_gpa })
                    === new_pt.spec_ram().get_enc_bytes_ok(
                    AddrMemID { memid, range: old_pte_gpa },
                ));
                assert(pte === old_pte);
            }
        }
    }
}

} // verus!
