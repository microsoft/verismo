use proc_macro;
use quote::quote;
use syn_verus::spanned::Spanned;
use syn_verus::{parse_macro_input, Data, DeriveInput, Ident, Type, Visibility};

use crate::def::{
    add_bound_to_generic, field_name_ty, gen_field_calls, gen_trait_bound, join_tokens,
};

pub fn verismo_snp_expand2(
    input: &DeriveInput,
    callname: &str,
    trtstr: &str,
) -> proc_macro2::TokenStream {
    // Used in the quasi-quotation below as `#name`.
    let name = &input.ident;
    let mut cast_generic = input.generics.clone();
    let call = Ident::new(callname, name.span());
    let _snpcall = Ident::new("snp", name.span());
    let (_impl_generics, _ty_generics, _where_clause) = input.generics.split_for_impl();
    let mut wf = vec![];
    //let mut snp = vec![];
    let mut size = vec![];
    let s = match &input.data {
        Data::Struct(s) => s,
        _ => panic!("Only support struct datatype"),
    };
    let mut close_or_open = quote! {open};
    for (i, field) in s.fields.iter().enumerate() {
        let (fname, field_ty) = field_name_ty(&field, i, name.span());
        close_or_open = match &field.vis {
            Visibility::Public(_) => close_or_open,
            _ => {
                quote! {closed}
            }
        };
        let wf_call = gen_field_calls(
            &quote! {self.#fname},
            &field_ty,
            &|fname, _ftype| quote! {#fname.#call()},
        );
        wf.extend(wf_call);

        /*let snp_call = gen_field_calls(
            &quote! {self.#fname},
            &field_ty,
            &|fname, _ftype| quote! {#fname.#snpcall()},
        );
        snp.extend(snp_call);*/

        let size_call = gen_field_calls(
            &quote! {self.#fname},
            &field_ty,
            &|_fname, ftype: &Type| quote! {spec_size::<#ftype>()},
        );
        size.extend(size_call);
    }
    /*for (i, snp_call) in snp.iter().enumerate() {
        if i > 0 {
            let prev = &snp[i - 1];
            let size_call = &size[i];
            wf.push(quote! {builtin::imply(#size_call > 0, builtin::equal(#snp_call, #prev))});
        }
    }
    let snp_call = if snp.len() > 0 {
        snp[0].clone()
    } else {
        quote! {SnpMemAttr::spec_default()}
    };*/
    let w = if wf.len() > 0 {
        join_tokens(&wf, quote! {&&})
    } else {
        quote! {true}
    };

    let trt = if trtstr.len() > 0 {
        Some(Ident::new(trtstr, name.span()))
    } else {
        None
    };
    let usetrt = if let Some(t) = trt {
        quote! {#t for}
    } else {
        quote! {}
    };
    let pub_or_default = if trtstr.len() > 0 {
        quote! {}
    } else {
        quote! {pub}
    };

    let trt = vec![trtstr];
    add_bound_to_generic(
        &mut cast_generic,
        gen_trait_bound(trt, name.span()),
        name.span(),
    );
    let (impl_generics, ty_generics, where_clause) = cast_generic.split_for_impl();

    let expanded = quote! {
        // The generated axiom for size.
        verus!{
        impl #impl_generics #usetrt #name #ty_generics #where_clause  {
            #pub_or_default #close_or_open spec fn #call(&self) -> bool {
                #w
            }
        }
        /*impl #impl_generics SnpMemAttrTrait for #name #ty_generics #where_clause  {
            #pub_or_default #close_or_open spec fn snp(&self) -> SnpMemAttr {
                #snp_call
            }
        }*/
        }
    };
    //println!("{}", expanded);
    expanded
}

pub fn verismo_snp_expand(
    input: proc_macro::TokenStream,
    calname: &str,
    trt: &str,
) -> proc_macro::TokenStream {
    // Hand the output tokens back to the compiler.
    let input = parse_macro_input!(input as DeriveInput);

    let ret = proc_macro::TokenStream::from(verismo_snp_expand2(&input, calname, trt));
    //println!("{}", ret);
    ret
}
