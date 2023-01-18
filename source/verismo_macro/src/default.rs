use quote::quote;
use syn_verus::{parse_macro_input, Data, DeriveInput, Type};

use crate::def::{add_bound_to_generic, field_name_ty, gen_trait_bound};

pub fn verismo_default_expand(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    //let strinput = input.to_string();
    //let inputcopy = TokenStream::from_str(&strinput).expect("unreacheable");
    //parse_macro_input!(inputcopy as DeriveInput)
    let input: DeriveInput = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let mut fields_stream = quote! {};
    let mut spec_fields_stream = quote! {};
    let generics = &input.generics;
    let (_impl_generics, _ty_generics, _where_clause) = generics.split_for_impl();
    let mut is_named = false;
    match &input.data {
        Data::Struct(s) => {
            for (i, field) in s.fields.iter().enumerate() {
                is_named = is_named | field.ident.is_some();
                let (fname, ftype) = field_name_ty(&field, i, name.span());
                let ty = &ftype;

                let ty_with_generic = crate::def::type_to_type_generic(ty);
                match ty {
                    Type::Path(tpath) => {
                        let path_segments = tpath
                            .path
                            .segments
                            .iter()
                            .map(|segment| segment.ident.to_string())
                            .collect::<Vec<_>>();
                        if path_segments.last() == Some(&"Ghost".to_string()) {
                            fields_stream = quote! {
                                #fields_stream
                                #fname: Ghost(arbitrary()),
                            };
                            spec_fields_stream = quote! {
                                #spec_fields_stream
                                #fname: (arbitrary()),
                            };
                        } else if path_segments.last() == Some(&"Tracked".to_string()) {
                            fields_stream = quote! {
                                #fields_stream
                                #fname: Tracked(arbitrary()),
                            };
                            spec_fields_stream = quote! {
                                #spec_fields_stream
                                #fname: (arbitrary()),
                            };
                        } else {
                            fields_stream = quote! {
                                #fields_stream
                                #fname: #ty_with_generic::default(),
                            };
                            spec_fields_stream = quote! {
                                #spec_fields_stream
                                #fname: #ty_with_generic::spec_default(),
                            };
                        }
                    }
                    _ => {
                        /*fields_stream = quote! {
                            #fields_stream
                            #fname: #ty_with_generic::default(),
                        };
                        spec_fields_stream = quote! {
                            #spec_fields_stream
                            #fname: #ty_with_generic::spec_default(),
                        };*/
                        panic! {"unsupported default"}
                    }
                }
            }
        }
        _ => {
            panic!("Only structs can be annotated with VClone");
        }
    };

    let newstruct = if is_named {
        quote! {
            #name{
                #fields_stream
            }
        }
    } else {
        quote! {
            #name(#fields_stream)
        }
    };

    let spec_newstruct = if is_named {
        quote! {
            #name{
                #spec_fields_stream
            }
        }
    } else {
        quote! {
            #name(#spec_fields_stream)
        }
    };
    let mut generic_for_default = generics.clone();
    add_bound_to_generic(
        &mut generic_for_default,
        gen_trait_bound(vec!["Default"], name.span()),
        name.span(),
    );
    add_bound_to_generic(
        &mut generic_for_default,
        gen_trait_bound(vec!["SpecDefault"], name.span()),
        name.span(),
    );
    let (impl_generics, ty_generics, where_clause) = generic_for_default.split_for_impl();
    let expand = quote! {
    verus!{
        impl #impl_generics Default for #name #ty_generics #where_clause  {
            #[verifier(external_body)]
            fn default() -> (ret: Self)
            ensures
                builtin::equal(ret, Self::spec_default()),
                ret.wf(),
            { #newstruct }
        }

        impl #impl_generics SpecDefault for #name #ty_generics #where_clause  {
            open spec fn spec_default() -> Self {
                #spec_newstruct
            }
        }
    }
    };

    //let strtoken = newcode.to_string() + &expand.to_string();
    //proc_macro::TokenStream::from_str(&strtoken).expect("wrong code")
    //proc_macro::TokenStream::from(expand)
    //println!("{}", expand);
    proc_macro::TokenStream::from(expand)
}
