//! Encoding of a single hardware page-table entry. Nothing here knows which
//! level an entry is read at: at the leaf bit 7 is PAT rather than PS, so it is
//! the walk layer that must refuse to descend below the leaf.
use core::marker::PhantomData;

use bitflags::Flags;

use crate::structs::address::{Address, PhysAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::level::PageLevel;

/// A single hardware page-table entry: a raw machine word, typed by the
/// architecture whose bit layout it follows. Any word is a well-formed value,
/// so the type carries no invariant of its own.
#[repr(transparent)]
#[derive(Debug)]
pub struct PTEntry<A: ArchPagingMeta> {
    val: usize,
    dummy: PhantomData<A>,
}

impl<A: ArchPagingMeta> PTEntry<A> {
    /// Raw word.
    pub fn raw(&self) -> usize {
        self.val
    }

    /// Whether the entry is the null word, which is what an unused slot holds.
    pub fn is_clear(&self) -> bool {
        self.val == 0
    }

    pub fn clear(&mut self) {
        self.val = 0;
    }

    /// The entry a raw word denotes. The layer above stores entries as plain
    /// words, so it needs both directions of this correspondence.
    pub fn from_bits(val: usize) -> Self {
        Self { val, dummy: PhantomData }
    }

    /// The address-field bits, *including* any confidentiality or shared tag
    /// stored alongside the physical address.
    pub fn paddr_field(&self) -> usize {
        self.val & A::address_mask()
    }

    /// [`Self::paddr_field`] with the private bit cleared: the frame a table
    /// walk should follow.
    pub fn page_frame(&self) -> usize {
        self.paddr_field() & !A::private_pte_mask()
    }

    /// [`Self::page_frame`] with the shared bit cleared too: the clean physical
    /// frame, every architecture-specific tag stripped.
    pub fn address(&self) -> usize {
        self.page_frame() & !A::shared_pte_mask()
    }

    /// Whether the stored address carries the shared (plaintext) tag.
    pub fn is_shared(&self) -> bool {
        self.paddr_field() & A::shared_pte_mask() == A::shared_pte_mask()
    }

    /// The whole word as flags. Every bit is kept, including any the
    /// architecture has no name for -- the C-bit's position, for one, is a
    /// machine property rather than an architectural constant.
    pub fn flags(&self) -> A::PTFlags {
        A::PTFlags::from_bits_retain(self.val)
    }

    pub fn present(&self) -> bool {
        self.val & A::PTFlags::present_bit() != 0
    }

    /// Hardware huge (large-page) bit. At the leaf level the hardware reads it
    /// as PAT instead, so only a caller that knows the level may read it as
    /// "maps a large page".
    pub fn huge(&self) -> bool {
        self.val & A::PTFlags::huge_bit() != 0
    }

    pub fn writable(&self) -> bool {
        self.val & A::PTFlags::writable_bit() != 0
    }

    pub fn user(&self) -> bool {
        self.val & A::PTFlags::user_bit() != 0
    }

    /// An entry a walker may follow down to a child table. The bits alone
    /// cannot say this, which is why the level is an argument.
    pub fn is_table(&self, level: PageLevel) -> bool {
        self.present() && !level.is_leaf() && !self.huge()
    }

    /// A present entry that maps a page rather than pointing at a table.
    pub fn is_leaf(&self, level: PageLevel) -> bool {
        self.present() && (self.huge() || level.is_leaf())
    }

    /// The all-zero entry: not present, and so neither a table nor a leaf.
    pub fn empty() -> Self {
        Self { val: 0, dummy: PhantomData }
    }

    /// An entry holding `addr` with `flags`. Flag bits that fall inside the
    /// address field are dropped, so the address survives whatever the caller
    /// passes.
    pub fn new(addr: PhysAddr, flags: A::PTFlags) -> Self {
        let val = (addr.bits() & A::address_mask()) | (flags.bits() & !A::address_mask());
        Self { val, dummy: PhantomData }
    }

    /// An entry pointing at a table page: present and not huge, whatever
    /// `flags` says, since those two bits are what "points at a table" means.
    pub fn new_table(addr: PhysAddr, flags: A::PTFlags) -> Self {
        let flag_bits = flags.bits() & !A::address_mask() & !A::PTFlags::huge_bit();
        let val = (addr.bits() & A::address_mask()) | flag_bits | A::PTFlags::present_bit();
        Self { val, dummy: PhantomData }
    }

    /// An entry mapping a page rather than pointing at a table. The large-page
    /// bit is left to `flags`, since above the leaf level it is what stops the
    /// hardware reading this entry as a table pointer.
    pub fn new_leaf(addr: PhysAddr, flags: A::PTFlags) -> Self {
        Self::new(addr, flags)
    }

    /// The same entry with the large-page bit set. Above the leaf, an update
    /// that keeps a huge page huge has to keep that bit: flags supplied by a
    /// caller who does not know the level would not.
    pub fn set_huge(self) -> Self {
        Self { val: self.val | A::PTFlags::huge_bit(), dummy: PhantomData }
    }

    pub fn set(&mut self, addr: PhysAddr, flags: A::PTFlags) {
        *self = Self::new(addr, flags);
    }
}

impl<A: ArchPagingMeta> Clone for PTEntry<A> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<A: ArchPagingMeta> Copy for PTEntry<A> {}

impl<A: ArchPagingMeta> From<usize> for PTEntry<A> {
    fn from(val: usize) -> Self {
        Self::from_bits(val)
    }
}

impl<A: ArchPagingMeta> From<PTEntry<A>> for usize {
    fn from(entry: PTEntry<A>) -> usize {
        entry.raw()
    }
}
