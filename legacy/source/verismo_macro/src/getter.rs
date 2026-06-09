use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn_verus::{parse_macro_input, Data, DeriveInput, Type, Visibility};

use crate::def::{field_name_ty, get_field};

pub fn gen_getter(
    fname: &proc_macro2::TokenStream,
    ftype: &Type,
    verus_pub_token: proc_macro2::TokenStream,
    span: Span,
) -> proc_macro2::TokenStream {
    let getter_ident = get_field(&fname, span);
    match ftype {
        Type::Path(_type_path) => {
            quote! {
                verus!{
                pub #verus_pub_token spec fn #getter_ident(&self) -> #ftype {
                    self.#fname
                }}
            }
        }
        Type::Reference(_type_path) => {
            quote! {
                verus!{
                pub #verus_pub_token spec fn #getter_ident(&self) -> #ftype {
                    self.#fname
                }}
            }
        }
        Type::Array(_tyarray) => {
            panic! {"Not supported"}
            /*let mut ret = quote!{};
            let len = get_array_len(&tyarray);
            for i in 0..len {
                let subfname = Ident::new(format!("{}_{}", fname, i).as_str(), fname.span());
                let subf = gen_getter(&subfname, &tyarray.elem, verus_pub_token);
                ret  = quote!{
                    #ret
                    #subf
                }
            }
            ret*/
        }
        _ => {
            panic! {"Not supported"}
        }
    }
}

pub fn verismo_getter_expand(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    let generics = input.generics;
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let mut fields_stream = quote! {};

    match input.data {
        Data::Struct(s) => {
            for (i, field) in s.fields.iter().enumerate() {
                let (fname, ftype) = field_name_ty(&field, i, name.span());
                let verus_pub_token = match &field.vis {
                    Visibility::Inherited => {
                        quote! {closed}
                    }
                    _ => {
                        quote! {open}
                    }
                };
                let field_stream = gen_getter(&fname, &ftype, verus_pub_token, name.span());
                fields_stream = quote! {
                    #fields_stream

                    #field_stream
                };
            }
        }
        _ => panic!("Only structs with fields can be annotated with Mem"),
    };

    let expand = quote! {
        verus!{
        impl #impl_generics #name #ty_generics #where_clause {
            #fields_stream
        }
        }
    };
    proc_macro::TokenStream::from(expand)
}
