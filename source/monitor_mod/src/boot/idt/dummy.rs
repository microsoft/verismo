use core::arch::global_asm;

use super::*;
use crate::arch::reg::RegName;
use crate::debug::VPrintAtLevel;
use crate::lock::MapLockContains;
use crate::snp::ghcb::GHCB_REGID;
use crate::snp::{SnpCoreConsole, SnpCoreSharedMem};
use crate::vbox::VBox;

#[cfg(target_os = "none")]
global_asm!(include_str!("isr.s"), options(att_syntax));

verus! {

// Requires the exception code and stackframe is not secret.
// This holds since we do not have secret-dependent control flows.
fn debug_handler(
    code: u64_s,
    stack_frame: &InterruptStackFrame,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
)
    requires
        stack_frame.is_constant(),
        code.is_constant(),
        old(cs).inv_ac(),
    ensures
        cs.inv_ac(),
        cs.only_lock_reg_coremode_updated(
            *old(cs),
            set![GHCB_REGID()],
            set![spec_CONSOLE_lockid()],
        ),
{
    proof {
        reveal_strlit("idt handler for error:");
        reveal_strlit("\n");
        reveal_strlit("stack info: ");
        SnpCoreSharedMem::lemma_update_prop_auto();
    }
    (new_strlit("idt handler for error:"), code).err(Tracked(cs));
    new_strlit("\n").err(Tracked(cs));
    (new_strlit("stack info: ")).err(Tracked(cs));
    stack_frame.err(Tracked(cs));
    new_strlit("\n").err(Tracked(cs));
}

#[no_mangle]
pub extern "C" fn dummy_handler_fn(
    stack_frame: InterruptStackFrame,
    error: u64_s,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
)
    requires
        stack_frame.is_constant(),
        error.is_constant(),
        old(cs).inv_ac(),
    ensures
        cs.inv_ac(),
{
    debug_handler(error, &stack_frame, Tracked(cs))
}

} // verus!
seq_macro::seq!(N in 0..21 {
    #(
        def_asm_addr_for! {
            isr_handler_addr_~N = isr_handler0
        }
    )*
});

seq_macro::seq!(N in 28..29 {
    def_asm_addr_for! {
        isr_handler_addr_~N = isr_handler~N
    }
});

verus! {

impl IDTEntry {
    verismo_simple! {
    #[verifier(inline)]
    pub open spec fn ensures_from_addr_selector(self, addr: u64_s, gdt_selector: u16_s) -> bool
    {
        &&& self.pointer_low === addr as u16_s
        &&& self.pointer_middle === (addr >> (16u64 as u64_s)) as u16_s
        &&& self.pointer_high ===  (addr >> (32u64 as u64_s)) as u32_s
        &&& self.gdt_selector === gdt_selector
        &&& self.options === ENTRY_MIN_PRE as EntryOptions
        &&& self.reserved === 0u32 as u32_s
    }
    }

    verus! {
    pub fn from_addr_selector(addr: u64, gdt_selector: u16) -> (ret: Self)
    requires
        gdt_selector.is_constant(),
        addr.is_constant(),
    ensures
        ret.is_constant(),
        ret.pointer_low@.val == addr as u16,
        ret.pointer_middle@.val == (addr >> 16u64) as u16,
        ret.pointer_high@.val ==  (addr >> 32u64) as u32,
        ret.gdt_selector@.val == gdt_selector,
        ret.options@.val == ENTRY_MIN_PRE,
        ret.reserved@.val == 0u32,
    {
        IDTEntry{
            pointer_low: addr.into(),
            pointer_middle: (addr >> 16u64).into(),
            pointer_high: (addr >> 32u64).into(),
            gdt_selector: gdt_selector.into(),
            options: ENTRY_MIN_PRE.into(),
            reserved: 0u32.into(),
        }
    }
    }
}

} // verus!
verus! {

pub fn init_idt_content(idt: &mut InterruptDescriptorTable, gdt_selector: u16)
    requires
        gdt_selector.is_constant(),
    ensures
        idt.wf(),
        idt.is_constant(),
{
    let dummy_handler = isr_handler_addr_0();
    let mut i: usize = 0;
    while i < idt.len()
        invariant
            i <= idt@.len(),
            dummy_handler == spec_isr_handler_addr_0(),
            dummy_handler.is_constant(),
            gdt_selector.is_constant(),
            forall|k: int| 0 <= k < (i as int) ==> idt@[k].is_constant(),
            i.is_constant(),
    {
        idt.update(i, IDTEntry::from_addr_selector(dummy_handler as u64, gdt_selector));
        i = i + 1;
    }/*assert(idt@.len() == 256);
    seq_macro::seq!(N in 0..21 {
        #(
            idt.update((N as usize_t).into(), IDTEntry::from_addr_selector(isr_handler_addr_~N().into(), gdt_selector));
        )*
    });
    seq_macro::seq!(N in 28..29 {
        #(
            idt.update((N as usize_t).into(), IDTEntry::from_addr_selector(isr_handler_addr_~N().into(), gdt_selector));
        )*
    });*/

}

} // verus!
verus! {

#[verifier(external_body)]
pub fn box_init_idt_content(idt: &mut VBox<InterruptDescriptorTable>, gdt_selector: u16) {
    init_idt_content(&mut *idt.b, gdt_selector);
}

} // verus!
verus! {

pub trait HasIDT {
    spec fn has_idt(&self) -> bool;
}

pub closed spec fn idt_wf(val: Idtr) -> bool {
    val.wf()
}

} // verus!
verus! {

impl HasIDT for Map<RegName, RegisterPerm> {
    // Reveal regs but hide bit ops.
    open spec fn has_idt(&self) -> bool {
        idt_wf(self[RegName::IdtrBaseLimit]@.value())
    }
}

} // verus!
verus! {

pub fn init_idt(Tracked(cs): Tracked<&mut SnpCoreSharedMem>)
    requires
        (*old(cs)).inv_ac(),
    ensures
        cs.inv_ac(),
        cs.snpcore.regs.has_idt(),
        cs.only_lock_reg_updated(
            (*old(cs)),
            set![RegName::IdtrBaseLimit],
            set![spec_ALLOCATOR_lockid()],
        ),
{
    let tracked mut cs_perm;
    let tracked mut idt_perm;
    let mut idt = VBox::new_uninit(Tracked(cs));
    proof {
        idt_perm = cs.snpcore.regs.tracked_remove(RegName::IdtrBaseLimit);
        cs_perm = cs.snpcore.regs.tracked_borrow(RegName::Cs);
    }
    let gdt_selector = CS.read(Tracked(cs_perm)).reveal_value();
    box_init_idt_content(&mut idt, gdt_selector);
    // convert vbox to raw mem.
    let (idt_addr, idt_memperm) = idt.into_raw();
    // TODO: adjust pte.
    assume(!idt_memperm@@.snp().pte().w);
    let dtp = Idtr { base: idt_addr.as_u64().into(), limit: 0xffffu64.into() };
    assert(dtp.is_constant());
    IdtBaseLimit.write(dtp, Tracked(&mut idt_perm));
    proof {
        cs.snpcore.regs.tracked_insert(RegName::IdtrBaseLimit, idt_perm);
    }
}

} // verus!
