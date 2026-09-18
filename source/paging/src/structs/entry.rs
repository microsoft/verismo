//! Encoding of a single hardware page-table entry. Nothing here knows which
//! level an entry is read at: at the leaf bit 7 is PAT rather than PS, so it is
//! the walk layer that must refuse to descend below the leaf.
use core::marker::PhantomData;
use core::sync::atomic::{AtomicUsize, Ordering};

use bitflags::Flags;

use crate::structs::address::{Address, PhysAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::level::PageLevel;

/// A raw page-table entry word typed by the architecture whose layout it follows.
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

    /// Whether the entry is the null word, which is what an unused entry holds.
    pub fn is_clear(&self) -> bool {
        self.val == 0
    }

    #[inline(always)]
    pub(crate) fn from_bits(val: usize) -> Self {
        Self { val, dummy: PhantomData }
    }

    #[inline(always)]
    pub(crate) fn for_publication(self) -> Self {
        #[cfg(not(feature = "use_ad"))]
        if self.present() {
            return Self::from_bits(self.val | A::accessed_dirty_mask());
        }
        self
    }

    /// The address-field bits, *including* any confidentiality or shared tag
    /// stored alongside the physical address.
    #[inline(always)]
    pub fn paddr_field(&self) -> usize {
        self.val & A::address_mask()
    }

    /// [`Self::paddr_field`] with the private bit cleared: the frame a table
    /// walk should follow.
    #[inline(always)]
    pub fn page_frame(&self) -> usize {
        self.paddr_field() & !A::private_pte_mask()
    }

    /// The address field without confidentiality tags. Huge-page attributes
    /// may remain; use [`Self::leaf_address`] for a leaf's clean frame base.
    #[inline(always)]
    pub fn address(&self) -> usize {
        self.page_frame() & !A::shared_pte_mask()
    }

    /// The clean frame base of a leaf at `level`, without size-dependent
    /// attributes such as huge-page PAT.
    pub fn leaf_address(&self, level: PageLevel) -> PhysAddr {
        PhysAddr::from(self.address() & !(level.size() - 1))
    }

    /// Whether the stored address carries the shared (plaintext) tag.
    pub fn is_shared(&self) -> bool {
        A::is_shared_address(PhysAddr::from(self.paddr_field()))
    }

    /// The whole word as flags. Every bit is kept, including any the
    /// architecture has no name for -- the C-bit's position, for one, is a
    /// machine property rather than an architectural constant.
    pub fn flags(&self) -> A::PTFlags {
        A::PTFlags::from_bits_retain(self.val)
    }

    #[inline(always)]
    pub fn present(&self) -> bool {
        self.val & A::PTFlags::present_bit() != 0
    }

    /// Hardware huge (large-page) bit. At the leaf level the hardware reads it
    /// as PAT instead, so only a caller that knows the level may read it as
    /// "maps a large page".
    #[inline(always)]
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
    #[inline(always)]
    pub fn is_table(&self, level: PageLevel) -> bool {
        self.present() && !level.is_leaf() && !self.huge()
    }

    /// A present entry that maps a page rather than pointing at a table.
    #[inline(always)]
    pub fn is_leaf(&self, level: PageLevel) -> bool {
        self.present() && (self.huge() || level.is_leaf())
    }

    /// The all-zero entry: not present, and so neither a table nor a leaf.
    pub fn empty() -> Self {
        Self { val: 0, dummy: PhantomData }
    }

    /// An entry holding `addr` with `flags`. Flag bits that fall inside the
    /// address field are dropped, so the address survives whatever the caller
    /// passes. Without `use_ad`, present entries also have A/D preset.
    #[inline(always)]
    pub fn new(addr: PhysAddr, flags: A::PTFlags) -> Self {
        let val = (addr.bits() & A::address_mask()) | (flags.bits() & !A::address_mask());
        Self::from_bits(val).for_publication()
    }

    /// Builds a present, non-huge pointer to a child table.
    #[inline(always)]
    pub(crate) fn new_table(addr: PhysAddr, flags: A::PTFlags) -> Self {
        Self::new(addr, flags.with(A::PTFlags::PRESENT).without(A::PTFlags::HUGE))
    }

    pub fn set_flags(&mut self, flags: A::PTFlags) {
        self.val |= (flags & A::supported_flags()).bits();
    }

    pub fn clear_flags(&mut self, flags: A::PTFlags) {
        self.val &= !(flags & A::PTFlags::all()).bits();
    }

    #[inline(always)]
    pub(crate) fn with_present(mut self) -> Self {
        self.val |= A::PTFlags::present_bit();
        self
    }

    #[inline(always)]
    pub(crate) fn split_child(self, level: PageLevel, index: usize) -> Self {
        let child = level.child().expect("cannot split a smallest leaf");
        let base = self.paddr_field() & !(level.size() - 1);
        let huge = if child.is_leaf() { A::PTFlags::huge_bit() } else { 0 };
        let flags = self.raw() & !A::address_mask() & !huge;
        let address = base + index * child.size();
        let entry = Self::from_bits((address & A::address_mask()) | flags).for_publication();
        Self::from_bits(entry.raw() | A::split_leaf_attributes(self.raw(), level))
    }

    /// Retags the mapped frame as shared, keeping the flags. The address the
    /// entry reports already has the private tag stripped.
    pub fn make_shared(&mut self) {
        let flags = self.flags();
        let addr = PhysAddr::from(self.address());
        *self = Self::new(A::make_shared_address(addr), flags);
    }

    /// Retags the mapped frame as private, keeping the flags.
    pub fn make_private(&mut self) {
        let flags = self.flags();
        let addr = PhysAddr::from(self.address());
        *self = Self::new(A::make_private_address(addr), flags);
    }
}

/// Borrowed atomic access to a live page-table entry.
/// Without `use_ad`, every successful write presets A/D if the result is present.
#[derive(Clone, Copy, Debug)]
pub(crate) struct PTEntryRef<'tree, A: ArchPagingMeta> {
    word: &'tree AtomicUsize,
    // Preserve the raw handles' thread affinity independently of the atomic word.
    marker: PhantomData<*mut A>,
}

impl<'tree, A: ArchPagingMeta> PTEntryRef<'tree, A> {
    /// # Safety
    /// The initialized, writable entry must be atomic-aligned and remain allocated
    /// for `'tree`. Conflicting accesses must be atomic, with no ordinary entry references.
    pub(crate) unsafe fn from_raw(entry: *mut PTEntry<A>) -> Self {
        let word = unsafe { AtomicUsize::from_ptr(entry.cast::<usize>()) };
        Self { word, marker: PhantomData }
    }

    #[inline(always)]
    pub(crate) fn load(self) -> PTEntry<A> {
        PTEntry::from_bits(self.word.load(Ordering::Acquire))
    }

    pub(crate) fn store(self, value: PTEntry<A>) {
        self.word.store(value.for_publication().raw(), Ordering::Release);
    }

    pub(crate) fn swap(self, value: PTEntry<A>) -> PTEntry<A> {
        PTEntry::from_bits(self.word.swap(value.for_publication().raw(), Ordering::AcqRel))
    }

    pub(crate) fn fetch_and(self, mask: usize) -> PTEntry<A> {
        #[cfg(feature = "use_ad")]
        {
            PTEntry::from_bits(self.word.fetch_and(mask, Ordering::AcqRel))
        }
        #[cfg(not(feature = "use_ad"))]
        {
            self.update(|word| word & mask)
        }
    }

    pub(crate) fn fetch_or(self, mask: usize) -> PTEntry<A> {
        #[cfg(feature = "use_ad")]
        {
            PTEntry::from_bits(self.word.fetch_or(mask, Ordering::AcqRel))
        }
        #[cfg(not(feature = "use_ad"))]
        {
            self.update(|word| word | mask)
        }
    }

    #[cfg(not(feature = "use_ad"))]
    fn update(self, update: impl Fn(usize) -> usize) -> PTEntry<A> {
        let previous = self
            .word
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |word| {
                Some(PTEntry::<A>::from_bits(update(word)).for_publication().raw())
            })
            .unwrap();
        PTEntry::from_bits(previous)
    }

    pub(crate) fn compare_exchange(
        self,
        current: PTEntry<A>,
        value: PTEntry<A>,
    ) -> Result<PTEntry<A>, PTEntry<A>> {
        self.word
            .compare_exchange(
                current.raw(),
                value.for_publication().raw(),
                Ordering::AcqRel,
                Ordering::Acquire,
            )
            .map(PTEntry::from_bits)
            .map_err(PTEntry::from_bits)
    }

    pub(crate) fn update_preserving_ad(self, current: PTEntry<A>, value: PTEntry<A>) {
        #[cfg(feature = "use_ad")]
        {
            let ad_mask = A::accessed_dirty_mask();
            let mut observed = current;
            loop {
                let desired =
                    PTEntry::from_bits((value.raw() & !ad_mask) | (observed.raw() & ad_mask));
                match self.compare_exchange(observed, desired) {
                    Ok(_) => return,
                    Err(latest) => observed = latest,
                }
            }
        }
        #[cfg(not(feature = "use_ad"))]
        {
            let _ = current;
            self.store(value);
        }
    }
}

impl<A: ArchPagingMeta> Clone for PTEntry<A> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<A: ArchPagingMeta> Copy for PTEntry<A> {}
