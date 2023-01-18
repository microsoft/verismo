use quote::quote;
use syn_verus::{parse_macro_input, Data, DeriveInput};

use crate::def::{field_name_ty, get_field, set_field};
use crate::new::gen_new_fn;

pub fn verismo_setter_expand(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    //let strinput = input.to_string();
    //let inputcopy = TokenStream::from_str(&strinput).expect("unreacheable");
    //parse_macro_input!(inputcopy as DeriveInput)
    let dinput: DeriveInput = parse_macro_input!(input as DeriveInput);
    let newcode = gen_new_fn(&dinput);

    let setcode = _verismo_setter_expand(&dinput);
    proc_macro::TokenStream::from(quote! {#setcode #newcode})
}

pub fn _verismo_setter_expand(input: &DeriveInput) -> proc_macro2::TokenStream {
    let name = &input.ident;

    let mut fields_stream = quote! {};
    let generics = &input.generics;
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    match &input.data {
        Data::Struct(s) => {
            for (i, field) in s.fields.iter().enumerate() {
                let (fname, _) = field_name_ty(&field, i, name.span());
                let mut set_fields = quote! {};
                let field_ty = &field.ty;
                let setter = set_field(&fname, name.span());

                for (j, field2) in s.fields.iter().enumerate() {
                    let (fname2, _) = field_name_ty(&field2, j, name.span());
                    let get_ident = get_field(&fname2, name.span());
                    if i == j {
                        set_fields = quote! {
                            #set_fields
                            val,
                        };
                    } else {
                        set_fields = quote! {
                            #set_fields
                            self.#get_ident(),
                        };
                    }
                }

                /*let verus_pub_token = match &field.vis {
                    Visibility::Inherited => {
                        quote! {open}
                    }
                    _ => {
                        quote! {open}
                    }
                };*/

                fields_stream = quote! {
                    #fields_stream
                    verus!{
                    pub open spec fn #setter(&self, val: #field_ty) -> Self
                    {Self::spec_new(#set_fields)
                    }}
                };
            }
        }
        _ => panic!("Only structs with named fields can be annotated with Mem"),
    };

    let expand = quote! {
        verus!{
        impl #impl_generics #name #ty_generics #where_clause  {
            #fields_stream
        }
    }
    };
    expand
    //let strtoken = newcode.to_string() + &expand.to_string();
    //proc_macro::TokenStream::from_str(&strtoken).expect("wrong code")
    //proc_macro::TokenStream::from(expand)
}
