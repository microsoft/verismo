mod spin_perm_s;
mod spin_t;
mod spincell_e;
//#[macro_use]
//mod spin_macro_t;

//pub use spin_e::*;
pub use spin_perm_s::*;
pub use spin_t::*;
pub use spincell_e::*;

use crate::addr_e::*;
use crate::ptr::*;
use crate::registers::{CoreIdPerm, CoreMode};
use crate::tspec_e::*;

//spin::def_lock!(CONSOLE_LOCK, console);
