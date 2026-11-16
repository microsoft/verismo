//! Ensures static user tables can borrow tracked subtrees from a lock-protected kernel without holding its lock.
mod common;

use std::sync::{Arc, OnceLock, RwLock};

use common::{Allocator, Arena, Host, Table, ARENA};
use paging::{
    arch::x86_64::{PTEntryFlags, X86_64Paging},
    pagetable::UserPageTable,
    structs::{CoveredRange, Lvl, UserPolicy},
};

type Arch = X86_64Paging<Host>;
type User = UserPageTable<Arch, Allocator, Lvl<3>, CoveredRange<256, 512>>;

// Kept alive for the process so `KERNEL`'s direct-mapped allocator stays valid.
static ARENA_HANDLE: OnceLock<Arc<Arena>> = OnceLock::new();
static KERNEL: OnceLock<RwLock<Table>> = OnceLock::new();
static USERS: RwLock<Vec<RwLock<User>>> = RwLock::new(Vec::new());

fn kernel() -> &'static RwLock<Table> {
    KERNEL.get_or_init(|| {
        let arena = Arena::new(ARENA);
        ARENA_HANDLE.set(arena).unwrap_or_else(|_| panic!("kernel initialized twice"));
        RwLock::new(Table::new(PTEntryFlags::data()).unwrap())
    })
}

/// Derives one more `'static` user table sharing the kernel's high half and
/// stores it, still lock-protected, in `USERS`.
fn push_user_table() {
    // SAFETY: `KERNEL`'s root-level tables are never freed for the process's
    // life, so the shared top entries stay valid for as long as any user
    // table derived here.
    let user: User = unsafe {
        Table::new_from_sharing_top::<UserPolicy<CoveredRange<256, 512>>, _, _, _>(
            kernel(),
            |lock| lock.read().unwrap(),
        )
    }
    .unwrap();
    USERS.write().unwrap().push(RwLock::new(user));
}

#[test]
fn derives_static_user_tables_from_a_locked_kernel_table() {
    push_user_table();
    push_user_table();
    assert_eq!(USERS.read().unwrap().len(), 2);
}
