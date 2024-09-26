use quote::quote;
use syn_verus::{parse_macro_input, Data, DeriveInput, Ident, Type};

use crate::def::{
    add_bound_to_generic, field_name_ty, field_offset, field_offset_exe, gen_field_calls,
    gen_trait_bound, generic_mod, get_field, join_tokens, type_to_type_generic,
};

fn convert(ftype: &Type) -> proc_macro2::TokenStream {
    match ftype {
        Type::Reference(_) | Type::Ptr(_) => {
            quote! {8}
        }
        _ => {
            let t = type_to_type_generic(ftype);
            quote! {#t::spec_size_def()}
        }
    }
}

fn convert_exe(ftype: &Type) -> proc_macro2::TokenStream {
    let t = type_to_type_generic(ftype);
    quote! {core::mem::size_of::<#t>()}
}

pub fn verismo_size_expand(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    //let size_tokens = &crate::size::verismo_size_expand2(&input);
    let name = input.ident;
    let generics = input.generics;
    let (_impl_generics, ty_generics, _where_clause) = generics.split_for_impl();
    let _ty_generics_fn =
        if !generics.params.is_empty() { quote!(::#ty_generics) } else { quote!() };
    let _instance = Ident::new("self", name.span());
    let _spec_type = generic_mod();

    let mut spec_size_def_calls = vec![];
    let mut size_def_calls = vec![];

    let s = match input.data {
        Data::Struct(s) => s,
        _ => panic!("Only structs can be annotated with Mem"),
    };
    let s = &s;
    for (i, field) in s.fields.iter().enumerate() {
        let (fname, ftype) = field_name_ty(&field, i, name.span());
        if field.attrs.iter().any(|attr| attr.path.is_ident("def_offset")) {
            let field_name = &field.ident;
            let _field_offset_exe = field_offset_exe(&fname, name.span());
            let _field_copy = Ident::new(
                format!("copy_{}", field_name.clone().unwrap().to_string()).as_str(),
                name.span(),
            );

            let _field_update = Ident::new(
                format!("set_{}", field_name.clone().unwrap().to_string()).as_str(),
                name.span(),
            );

            let _spec_set_fn = Ident::new(
                format!("spec_set_{}", field_name.clone().unwrap().to_string()).as_str(),
                name.span(),
            );

            let _spec_get_field = Ident::new(
                format!("spec_{}", field_name.clone().unwrap().to_string()).as_str(),
                name.span(),
            );

            let _copy_field_param = Ident::new(
                format!("Copy{}", field_name.clone().unwrap().to_string()).as_str(),
                name.span(),
            );

            let _update_field_param = Ident::new(
                format!("Update{}", field_name.clone().unwrap().to_string()).as_str(),
                name.span(),
            );

            let _spec_field_offset = field_offset(&fname, name.span());
            let _getter = get_field(&fname, name.span());
            let _axiom_field = Ident::new(
                format!("axiom_field_{}", field_name.clone().unwrap().to_string()).as_str(),
                name.span(),
            );
            let _sizeexe = if size_def_calls.len() > 0 {
                join_tokens(&size_def_calls, quote! {+})
            } else {
                quote! {0usize}
            };
            let _specsize = if spec_size_def_calls.len() > 0 {
                join_tokens(&spec_size_def_calls, quote! {+})
            } else {
                quote! {0}
            };
        }

        spec_size_def_calls.extend(gen_field_calls(
            &fname,
            &ftype,
            &|_fname: &proc_macro2::TokenStream, ftype| convert(ftype),
        ));

        size_def_calls.extend(gen_field_calls(
            &fname,
            &ftype,
            &|_fname: &proc_macro2::TokenStream, ftype| convert_exe(ftype),
        ));
    }
    let size = if spec_size_def_calls.len() > 0 {
        join_tokens(&spec_size_def_calls, quote! {+})
    } else {
        quote! {0}
    };
    let mut size_generic = generics.clone();
    add_bound_to_generic(
        &mut size_generic,
        gen_trait_bound(vec!["SpecSize"], name.span()),
        name.span(),
    );
    let (impl_generics, ty_generics, where_clause) = size_generic.split_for_impl();

    let expand2 = quote! {
        verus!{
            impl #impl_generics SpecSize for #name #ty_generics #where_clause {
                #[verifier(inline)]
                open spec fn spec_size_def() -> (ret: nat)
                {
                    #size
                }
            }
        }
    };
    proc_macro::TokenStream::from(expand2)
}

pub fn verismo_defoffset_expand(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    //let size_tokens = &crate::size::verismo_size_expand2(&input);
    let name = input.ident;
    let generics = input.generics;
    let (impl_generics, ty_generics, _where_clause) = generics.split_for_impl();
    let _ty_generics_fn =
        if !generics.params.is_empty() { quote!(::#ty_generics) } else { quote!() };
    let _instance = Ident::new("self", name.span());
    let _spec_type = generic_mod();

    let mut spec_size_def_calls = vec![];
    let mut size_def_calls = vec![];
    let mut offsetfns = quote!();
    let mut offsetfns_ptr = quote!();
    let mut offsetfns_box = quote!();

    let mut offset_counts: i32 = 0;
    let s = match input.data {
        Data::Struct(s) => s,
        _ => panic!("Only structs can be annotated with Mem"),
    };
    let s = &s;
    for (i, field) in s.fields.iter().enumerate() {
        let (fname, ftype) = field_name_ty(&field, i, name.span());
        if field.attrs.iter().any(|attr| attr.path.is_ident("def_offset")) {
            let field_name = &field.ident;
            let field_offset_exe = field_offset_exe(&fname, name.span());
            let field_copy = Ident::new(
                format!("copy_{}", field_name.clone().unwrap().to_string()).as_str(),
                name.span(),
            );

            let field_update = Ident::new(
                format!("set_{}", field_name.clone().unwrap().to_string()).as_str(),
                name.span(),
            );

            let spec_set_fn = Ident::new(
                format!("spec_set_{}", field_name.clone().unwrap().to_string()).as_str(),
                name.span(),
            );

            let spec_get_field = Ident::new(
                format!("spec_{}", field_name.clone().unwrap().to_string()).as_str(),
                name.span(),
            );

            let copy_field_param = Ident::new(
                format!("Copy{}", field_name.clone().unwrap().to_string()).as_str(),
                name.span(),
            );

            let update_field_param = Ident::new(
                format!("Update{}", field_name.clone().unwrap().to_string()).as_str(),
                name.span(),
            );

            let spec_field_offset = field_offset(&fname, name.span());
            let getter = get_field(&fname, name.span());
            let axiom_field = Ident::new(
                format!("axiom_field_{}", field_name.clone().unwrap().to_string()).as_str(),
                name.span(),
            );
            let sizeexe = if size_def_calls.len() > 0 {
                join_tokens(&size_def_calls, quote! {+})
            } else {
                quote! {0usize}
            };
            let specsize = if spec_size_def_calls.len() > 0 {
                join_tokens(&spec_size_def_calls, quote! {+})
            } else {
                quote! {0}
            };
            let offsetfn = quote! {
                pub fn #field_offset_exe() -> (ret: usize)
                ensures
                    ret == Self::#spec_field_offset()
                {
                    // Calculate the offset for the field here
                    // You may want to use std::mem::offset_of!
                    // Example: std::mem::offset_of!(Self, #field_name)
                    #sizeexe
                }

                pub open spec fn #spec_field_offset() -> nat
                {
                    (#specsize) as nat
                }

                #[verifier(external_body)]
                pub broadcast proof fn #axiom_field(&self)
                ensures
                    builtin::equal(self.#getter(), field_at(*self, Self::#spec_field_offset()))
                {}
            };
            offset_counts = offset_counts + 1;
            offsetfns = quote!(
                #offsetfns
                #offsetfn
            );
            offsetfns_ptr = quote! {
                #offsetfns_ptr
                pub fn #field_name(&self) -> (ret: SnpPPtr<#ftype>)
                requires
                    self.not_null(),
                ensures
                    self.id() + #name::#spec_field_offset() == ret.id(),
                    builtin::imply(self.is_constant(), ret.is_constant()),
                {
                    let offset: usize_s = #name::#field_offset_exe().into();
                    SnpPPtr::from_usize(self.uptr.add(offset))
                    //SnpPPtr::from_usize(self.uptr)
                }
            };
            offsetfns_box = quote! {
                #offsetfns_box
                pub struct #copy_field_param;
                impl<'a> crate::vbox::BorrowFnTrait<'a, #copy_field_param, #ftype> for #name {
                    open spec fn spec_borrow_requires(&self, params: #copy_field_param) -> bool {
                        true
                    }

                    open spec fn spec_borrow_ensures(&self, params: #copy_field_param, ret: #ftype) -> bool {
                        builtin::equal(self.#spec_get_field(), ret)
                    }

                    //#[verifier(external_body)]
                    fn box_borrow(&'a self, params: #copy_field_param) -> (ret: #ftype)
                    {
                        self.#field_name.clone()
                    }
                }
                impl #impl_generics crate::vbox::VBox<#name #ty_generics> {
                    #[inline]
                    pub fn #field_copy(&self) -> (ret: #ftype)
                    ensures
                        ret.wf(),
                        builtin::imply(self.snp().is_vmpl0_private(),
                            builtin::equal(ret, self@.#spec_get_field())),
                    {
                        return self.box_borrow(#copy_field_param);
                    }
                }

                pub struct #update_field_param {
                    pub val: #ftype
                }

                impl<'a> crate::vbox::MutFnTrait<'a, #update_field_param, bool> for #name {
                    open spec fn spec_update_requires(&self, params: #update_field_param) -> bool {
                        true
                    }

                    open spec fn spec_update(&self, prev: &Self, params:  #update_field_param, ret: bool) -> bool {
                        builtin::equal(*self, prev.#spec_set_fn(params.val))
                    }

                    fn box_update(&'a mut self, params: #update_field_param) -> (ret: bool)
                    {
                        self.#field_name = params.val;
                        true
                    }
                }

                impl #impl_generics crate::vbox::VBox<#name #ty_generics> {
                    #[inline]
                    pub fn #field_update(&mut self, val: #ftype)
                    ensures
                        self@.spec_update(&old(self)@, #update_field_param{val}, true),
                        self.only_val_updated(*old(self)),
                    {
                        self.box_update(#update_field_param{val});
                    }
                }
            };
        }

        spec_size_def_calls.extend(gen_field_calls(
            &fname,
            &ftype,
            &|_fname: &proc_macro2::TokenStream, ftype| convert(ftype),
        ));

        size_def_calls.extend(gen_field_calls(
            &fname,
            &ftype,
            &|_fname: &proc_macro2::TokenStream, ftype| convert_exe(ftype),
        ));
    }
    let _size = if spec_size_def_calls.len() > 0 {
        join_tokens(&spec_size_def_calls, quote! {+})
    } else {
        quote! {0}
    };
    let mut size_generic = generics.clone();
    add_bound_to_generic(
        &mut size_generic,
        gen_trait_bound(vec!["SpecSize"], name.span()),
        name.span(),
    );
    let (impl_generics, ty_generics, where_clause) = size_generic.split_for_impl();
    offsetfns_ptr = if offset_counts == 0 {
        quote! {}
    } else {
        quote! {
            impl #impl_generics crate::ptr::SnpPPtr<#name #ty_generics> #where_clause {
                #offsetfns_ptr
            }
        }
    };

    offsetfns_box = if offset_counts == 0 {
        quote! {}
    } else {
        //println!("{}", offsetfns_box);
        quote! {
            #offsetfns_box
        }
    };
    let expand2 = quote! {
        verus!{
            impl #impl_generics #name #ty_generics #where_clause {
                #offsetfns
            }
            #offsetfns_ptr

            #offsetfns_box
        }
    };
    proc_macro::TokenStream::from(expand2)
}
