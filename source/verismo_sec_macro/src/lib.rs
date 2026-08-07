//! Verismo's front-end macros.
//!
//! Each macro applies only the Verismo-specific replacements to the still-Verus
//! syntax it is given (secure integer types and operators, the project's
//! specification traits, the project's derives and the synthesized constantness
//! contracts) and then delegates all standard Verus lowering to the upstream
//! `verus_builtin_macros::verus!` macro.
mod syntax;

use syntax::ContractMode;

/// Verismo replacements plus the implicit
/// `constant inputs ==> constant outputs` postcondition.
#[proc_macro]
pub fn verismo(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, ContractMode::PreserveConstant)
}

/// Verismo replacements plus explicit `is_constant()` requirements on the
/// inputs and guarantees on the outputs.
#[proc_macro]
pub fn verismo_non_secret(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, ContractMode::RequireConstant)
}

/// Verismo replacements only; no constantness clauses are synthesized.
#[proc_macro]
pub fn verismo_simple(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_items(input, ContractMode::None)
}
