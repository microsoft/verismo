use quote::quote;
use syn_verus::{Data, DeriveInput};

use crate::def::{field_name_ty, get_field};

pub fn gen_new_fn(input: &DeriveInput) -> proc_macro2::TokenStream {
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let s = match &input.data {
        Data::Struct(s) => s,
        _ => {
            panic!();
        }
    };
    let mut new_fields = quote! {};
    let mut new_fields_param = quote! {};
    let mut new_fields_param_body = quote! {};
    let mut struct_lit_fields = quote! {};

    for (i, field) in s.fields.iter().enumerate() {
        let (fname, ftype) = field_name_ty(&field, i, name.span());
        new_fields_param = quote! {#new_fields_param #fname: #ftype,};
        new_fields_param_body = quote! {#new_fields_param_body #fname,};
        struct_lit_fields = quote! {#struct_lit_fields #fname,};
    }

    for (i, field) in s.fields.iter().enumerate() {
        let (fname, _) = field_name_ty(&field, i, name.span());
        let getter = get_field(&fname, name.span());
        new_fields = quote! {
            #new_fields
            builtin::equal((#[trigger] Self::spec_new(#new_fields_param_body)).#getter(), #fname),
        };
    }

    let expand = quote! {
        verus!{
        impl #impl_generics #name #ty_generics #where_clause  {
        verus!{
            pub closed spec fn spec_new(#new_fields_param) -> Self{
                Self { #struct_lit_fields }
            }

            pub broadcast proof fn axiom_spec_new(#new_fields_param)
                ensures #new_fields
            {
            }
        }
        }
    }
    };
    expand
}
