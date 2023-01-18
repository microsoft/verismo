use quote::quote;
use syn_verus::{parse_macro_input, Data, DeriveInput, Ident, Type};

use crate::def::{
    add_bound_to_generic, field_name_ty, gen_field_calls, gen_trait_bound, generic_mod,
    join_tokens, type_to_type_generic,
};
fn convert(ftype: &Type) -> proc_macro2::TokenStream {
    let t = type_to_type_generic(ftype);
    quote! {#t::spec_size_def()}
}
pub fn verismo_mem_expand(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    //let size_tokens = &crate::size::verismo_size_expand2(&input);
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
    let mut seqcalls = vec![];
    let mut secseqcalls = vec![];

    let mut spec_size_def_calls = vec![];
    match input.data {
        Data::Struct(s) => {
            for (i, field) in s.fields.iter().enumerate() {
                let (fname, ftype) = field_name_ty(&field, i, name.span());
                seqcalls.extend(gen_field_calls(
                    &fname,
                    &ftype,
                    &|fname, _ftype| quote! {VTypeCast::<Seq<u8>>::vspec_cast_to(self.#fname)},
                ));
                secseqcalls.extend(gen_field_calls(
                    &fname,
                    &ftype,
                    &|fname, _ftype| quote! {VTypeCast::<SecSeqByte>::vspec_cast_to(self.#fname)},
                ));
                spec_size_def_calls.extend(gen_field_calls(
                    &fname,
                    &ftype,
                    &|_fname: &proc_macro2::TokenStream, ftype| convert(ftype),
                ));
            }
        }
        _ => panic!("Only structs can be annotated with Mem"),
    }
    let seq = if seqcalls.len() > 0 {
        join_tokens(&seqcalls, quote! {+})
    } else {
        quote! {Seq::empty()}
    };
    let mut cast_generic = generics.clone();
    add_bound_to_generic(
        &mut cast_generic,
        gen_trait_bound(vec!["VTypeCast", "Seq", "u8"], name.span()),
        name.span(),
    );

    let (impl_generics, ty_generics, where_clause) = cast_generic.split_for_impl();
    let _expand2 = quote! {
        verus!{
            impl #impl_generics VTypeCast<Seq<u8>> for #name #ty_generics #where_clause {
                #[verifier(inline)]
                open spec fn vspec_cast_to(self) -> Seq<u8> {
                    #seq
                }
            }
        }
    };

    let seq = if secseqcalls.len() > 0 {
        join_tokens(&secseqcalls, quote! {+})
    } else {
        quote! {Seq::empty()}
    };
    let mut cast_generic = generics.clone();
    add_bound_to_generic(
        &mut cast_generic,
        gen_trait_bound(vec!["VTypeCast", "Seq", "u8_s"], name.span()),
        name.span(),
    );

    let (impl_generics, ty_generics, where_clause) = cast_generic.split_for_impl();
    let expand2 = quote! {
        verus!{
            impl #impl_generics VTypeCast<SecSeqByte> for #name #ty_generics #where_clause {
                #[verifier(inline)]
                open spec fn vspec_cast_to(self) -> SecSeqByte {
                    #seq
                }
            }
        }
    };
    /*let size = if spec_size_def_calls.len() > 0 {join_tokens(&spec_size_def_calls, quote! {+})} else {quote!{0}};
    let mut size_generic = generics.clone();
    add_bound_to_generic(&mut size_generic, gen_trait_bound(vec!["SpecSize"], name.span()), name.span());
    let (impl_generics, ty_generics, where_clause) = size_generic.split_for_impl();
    let expand2 = quote! {
        #expand2
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
    */

    /*
        impl #impl_generics SpecSize for #name #ty_generics #where_clause {
            #[verifier(inline)]
            open spec fn spec_size_def() -> (ret: nat)
            {
                #size
            }
        }
    }*/
    //#size_tokens
    println!("{}", expand2);
    proc_macro::TokenStream::from(expand2)
}
