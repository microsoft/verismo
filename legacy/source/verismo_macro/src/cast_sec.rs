use quote::quote;
use syn_verus::{parse_macro_input, Data, DeriveInput, Ident, Type};

use crate::def::{
    add_bound_to_generic, field_name_ty, gen_field_calls, gen_trait_bound, generic_mod,
    get_closed_or_open, join_tokens, new_path, type_to_type_generic,
};
fn convert(ftype: &Type) -> proc_macro2::TokenStream {
    let t = type_to_type_generic(ftype);
    quote! {#t::spec_size_def()}
}

pub fn verismo_cast_seq_expand(
    input: proc_macro::TokenStream,
    seqtypenames: Vec<&str>,
    _add_proof: bool,
) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    //let size_tokens = &crate::size::verismo_size_expand2(&input);
    let name = input.ident;
    let generics = input.generics;
    let seqtype = new_path(&seqtypenames, name.span());
    let seqtype0 = Ident::new(seqtypenames[0], name.span());
    let (_impl_generics, ty_generics, _where_clause) = generics.split_for_impl();
    let _ty_generics_fn =
        if !generics.params.is_empty() { quote!(::#ty_generics) } else { quote!() };
    let _instance = Ident::new("self", name.span());
    let _spec_type = generic_mod();
    let mut secseqcalls = vec![];
    let mut cast_proof_calls = vec![];
    let mut spec_size_def_calls = vec![];
    let s = match input.data {
        Data::Struct(s) => s,
        _ => panic!("Only structs can be annotated with Mem"),
    };
    let s = &s;
    for (i, field) in s.fields.iter().enumerate() {
        let (fname, ftype) = field_name_ty(&field, i, name.span());
        secseqcalls.extend(gen_field_calls(&fname, &ftype, &|fname, ftype| match ftype {
            Type::Reference(_) => quote! {VTypeCast::<#seqtype>::vspec_cast_to(0u64)},
            _ => quote! {VTypeCast::<#seqtype>::vspec_cast_to(self.#fname)},
        }));
        cast_proof_calls.extend(gen_field_calls(
            &fname,
            &ftype,
            &|fname, _ftype| quote! {self.#fname.proof_into_is_constant();},
        ));
        spec_size_def_calls.extend(gen_field_calls(
            &fname,
            &ftype,
            &|_fname: &proc_macro2::TokenStream, ftype| convert(ftype),
        ));
    }
    let closed_or_open = get_closed_or_open(s);
    let seq = if secseqcalls.len() > 0 {
        join_tokens(&secseqcalls, quote! {+})
    } else {
        quote! {#seqtype0::empty()}
    };
    let _cast_proof_calls = if cast_proof_calls.len() > 0 {
        join_tokens(&cast_proof_calls, quote! {})
    } else {
        quote! {}
    };
    let mut cast_generic = generics.clone();
    let mut trt = vec!["VTypeCast"];
    trt.extend(seqtypenames);
    add_bound_to_generic(&mut cast_generic, gen_trait_bound(trt, name.span()), name.span());

    let (impl_generics, ty_generics, where_clause) = cast_generic.split_for_impl();
    let expand2 = quote! {
        verus!{
            impl #impl_generics VTypeCast<#seqtype> for #name #ty_generics #where_clause {
                //#[verifier(inline)]
                #closed_or_open spec fn vspec_cast_to(self) -> #seqtype {
                    #seq
                }
            }
        }
    };
    if name.to_string() == "VSnpPointsToNode" {
        println!("{}", expand2);
    }
    proc_macro::TokenStream::from(expand2)
}
