#![feature(box_patterns)]
#![feature(proc_macro_span)]
#![feature(proc_macro_tracked_env)]
#![feature(proc_macro_quote)]
#![feature(proc_macro_expand)]

//mod atomic_ghost;
//mod fndecl;
//mod is_variant;
mod rustdoc;
//mod struct_decl_inv;
mod structural;
mod syntax;
mod topological_sort;

#[proc_macro]
pub fn verismo(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ret = syntax::rewrite_items(input, cfg_erase(), true, false, true);
    //println!("ret = {}", ret);
    ret
}

#[proc_macro]
pub fn verismo_non_secret(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ret = syntax::rewrite_items(input, cfg_erase(), true, true, true);
    //println!("ret = {}", ret);
    ret
}

#[proc_macro]
pub fn verismo_simple(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ret = syntax::rewrite_items(input, cfg_erase(), true, true, false);
    //println!("ret = {}", ret);
    ret
}

#[proc_macro]
pub fn verismo_proof_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(false, true, input, false)
}

#[proc_macro]
pub fn verismo_exec_expr_keep_ghost(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(false, false, input, false)
}

#[proc_macro]
pub fn verismo_exec_expr_erase_ghost(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(true, false, input, false)
}

#[proc_macro]
pub fn verismo_exec_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::rewrite_expr(cfg_erase(), false, input, false)
}

pub(crate) fn cfg_erase() -> bool {
    let ts: proc_macro::TokenStream =
        quote::quote! { ::core::cfg!(verus_macro_erase_ghost) }.into();
    let bool_ts = ts.expand_expr();
    let bool_ts = match bool_ts {
        Ok(name) => name,
        Err(_) => {
            panic!("cfg_erase call failed");
        }
    };
    let bool_ts = bool_ts.to_string();
    assert!(bool_ts == "true" || bool_ts == "false");
    bool_ts == "true"
}

/// verismo_proof_macro_exprs!(f!(exprs)) applies verismo syntax to transform exprs into exprs',
/// then returns f!(exprs'),
/// where exprs is a sequence of expressions separated by ",", ";", and/or "=>".
#[proc_macro]
pub fn verismo_proof_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::proof_macro_exprs(false, true, input, false)
}

#[proc_macro]
pub fn verismo_exec_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    syntax::proof_macro_exprs(cfg_erase(), false, input, false)
}

#[proc_macro]
pub fn verismo_inv_macro_exprs(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // Reads the first expression as proof; the second as exec
    syntax::inv_macro_exprs(cfg_erase(), input, false)
}

/// `verismo_proof_macro_explicit_exprs!(f!(tts))` applies verismo syntax to transform `tts` into
/// `tts'`, then returns `f!(tts')`, only applying the transform to any of the exprs within it that
/// are explicitly prefixed with `@@`, leaving the rest as-is. Contrast this to
/// [`verismo_proof_macro_exprs`] which is likely what you want to try first to see if it satisfies
/// your needs.
#[proc_macro]
pub fn verismo_proof_macro_explicit_exprs(
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    syntax::proof_macro_explicit_exprs(false, true, input, false)
}
