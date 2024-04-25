use quote::quote;
use syn_verus::{parse_macro_input, Data, DeriveInput, Ident};

use crate::def::{
    add_bound_to_generic_with_self, field_name_ty, gen_field_calls, generic_mod,
    get_closed_or_open, join_tokens,
};

pub fn verismo_eq_expand(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    //let eq_tokens = &crate::eq::verismo_eq_expand2(&input);
    let name = input.ident;
    let generics = input.generics;
    let (_impl_generics, ty_generics, _where_clause) = generics.split_for_impl();
    let _ty_generics_fn = if !generics.params.is_empty() {
        quote!(::#ty_generics)
    } else {
        quote!()
    };
    let _instance = Ident::new("self", name.span());
    let _spec_type = generic_mod();

    let mut spec_eq_def_calls = vec![];
    let s = match input.data {
        Data::Struct(s) => s,
        _ => panic!("Only structs can be annotated with Mem"),
    };
    let s = &s;
    for (i, field) in s.fields.iter().enumerate() {
        let (fname, ftype) = field_name_ty(&field, i, name.span());
        spec_eq_def_calls.extend(gen_field_calls(
            &fname,
            &ftype,
            &|_fname: &proc_macro2::TokenStream, _ftype| quote! {self.#_fname.spec_eq(rhs.#_fname)},
        ));
    }
    let closed_or_open = get_closed_or_open(s);
    let eq = if spec_eq_def_calls.len() > 0 {
        join_tokens(&spec_eq_def_calls, quote! {&&})
    } else {
        quote! {true}
    };
    let mut eq_generic = generics.clone();
    add_bound_to_generic_with_self(&mut eq_generic, vec!["VSpecEq"], name.span());
    let (impl_generics, ty_generics, where_clause) = eq_generic.split_for_impl();
    let expand2 = quote! {
        verus!{
            impl #impl_generics VSpecEq<#name #ty_generics> for #name #ty_generics #where_clause {
                #closed_or_open spec fn spec_eq(self, rhs: Self) -> bool
                {
                    #eq
                }
            }
        }
    };
    proc_macro::TokenStream::from(expand2)
}
