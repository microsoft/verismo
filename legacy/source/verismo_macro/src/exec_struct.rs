use proc_macro;
use quote::quote;
use quote::spanned::Spanned;
use syn_verus::{parse_macro_input, Data, DeriveInput};

fn add_empty_trait(input: &DeriveInput, trt: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    // Used in the quasi-quotation below as `#name`.
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let _s = match &input.data {
        Data::Struct(s) => s,
        _ => panic!("Only support struct datatype"),
    };
    let expanded = quote! {
        // The generated axiom for size.
        verus!{
        impl #impl_generics #trt for #name #ty_generics #where_clause  {}
        }
    };
    expanded
}

pub fn add_empty_trait_for_struct(
    input: proc_macro::TokenStream,
    name: &str,
) -> proc_macro::TokenStream {
    // Hand the output tokens back to the compiler.
    let input = parse_macro_input!(input as DeriveInput);
    let trait_name = proc_macro2::Ident::new(name, input.__span());
    proc_macro::TokenStream::from(add_empty_trait(&input, quote! {#trait_name}))
}
