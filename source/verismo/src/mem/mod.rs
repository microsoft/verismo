mod rawmem_p;
mod rawmem_p2;

mod rawmem_s;

pub use rawmem_p::*;
pub use rawmem_s::*;

use crate::ptr::{SnpMemAttrTrait, SnpPPtr, SnpPointsToBytes, SnpPointsToData, SnpPointsToRaw};
use crate::tspec::*;
