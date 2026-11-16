//! Concrete, allocation-free content locks shared across page-table roots.
use crate::address::{Address, PhysAddr};
use crate::structs::ArchPagingMeta;

#[cfg(feature = "spin-mutex")]
pub use spin::mutex::SpinMutex as PagingMutex;
#[cfg(not(feature = "spin-mutex"))]
pub use spin::mutex::TicketMutex as PagingMutex;

#[cfg(feature = "spin-mutex")]
use spin::mutex::SpinMutexGuard as MutexGuard;
#[cfg(not(feature = "spin-mutex"))]
use spin::mutex::TicketMutexGuard as MutexGuard;

#[cfg(feature = "striped-locks")]
const LOCK_COUNT: usize = 64;
#[cfg(not(feature = "striped-locks"))]
const LOCK_COUNT: usize = 1;

pub(crate) struct LockWait;

#[cfg(feature = "lock-wait-hook")]
extern "C" {
    fn paging_lock_wait();
}

impl spin::RelaxStrategy for LockWait {
    fn relax() {
        #[cfg(feature = "lock-wait-hook")]
        // SAFETY: enabling this feature requires a context-safe, non-reentrant,
        // non-unwinding callback supplied by the embedder.
        unsafe {
            paging_lock_wait()
        };
        core::hint::spin_loop();
    }
}

static CONTENT_LOCKS: [PagingMutex<(), LockWait>; LOCK_COUNT] =
    [const { PagingMutex::new(()) }; LOCK_COUNT];

fn lock_index(page: PhysAddr) -> usize {
    (page.bits() >> 12) & (LOCK_COUNT - 1)
}

pub(crate) type ContentGuard = MutexGuard<'static, (), LockWait>;

pub(crate) fn lock_table_page<A: ArchPagingMeta>(page: PhysAddr) -> ContentGuard {
    let page = A::strip_shared_address_bits(A::strip_confidentiality_bits(page));
    CONTENT_LOCKS[lock_index(page)].lock()
}
