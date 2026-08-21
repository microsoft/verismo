// The register contract modeled below is architecture specific: it names
// x86-64 control registers and their paging bits.
#[cfg(target_arch = "x86_64")]
pub mod x86_64;
