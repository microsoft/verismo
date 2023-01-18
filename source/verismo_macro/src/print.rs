use proc_macro;
use quote::quote;
use syn_verus::spanned::Spanned;
use syn_verus::{parse_macro_input, Data, DeriveInput, Ident};

use crate::def::{
    add_bound_to_generic, field_name_ty, gen_field_calls, gen_trait_bound, join_tokens,
};

pub fn verismo_print_expand(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
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

    let mut print_calls = vec![];
    let s = match input.data {
        Data::Struct(s) => s,
        _ => panic!("Only structs can be annotated with Mem"),
    };
    let s = &s;
    for (i, field) in s.fields.iter().enumerate() {
        let (fname, ftype) = field_name_ty(&field, i, name.span());
        print_calls.extend(gen_field_calls(
            &fname,
            &ftype,
            &|_fname: &proc_macro2::TokenStream, _ftype| {
                let fname_str = if i == 0 {
                    "{".to_string() + &_fname.to_string()
                } else {
                    ", ".to_string() + &_fname.to_string()
                } + "=";
                quote! {
                    proof {
                        reveal_strlit(#fname_str);
                    }
                    let Tracked(console) = new_strlit(#fname_str).early_print2(Tracked(snpcore), Tracked(console));
                    let Tracked(console) = self.#_fname.early_print2(Tracked(snpcore), Tracked(console));
                }
            },
        ));
    }
    let print_stmts = if print_calls.len() > 0 {
        join_tokens(&print_calls, quote! {})
    } else {
        quote! {}
    };
    let mut print_generic: syn_verus::Generics = generics.clone();
    add_bound_to_generic(
        &mut print_generic,
        gen_trait_bound(vec!["VPrint"], name.span()),
        name.span(),
    );
    add_bound_to_generic(
        &mut print_generic,
        gen_trait_bound(vec!["IsConstant"], name.span()),
        name.span(),
    );
    let (impl_generics, ty_generics, where_clause) = print_generic.split_for_impl();
    let expand2 = quote! {
        verus!{
            impl #impl_generics VPrint for #name #ty_generics #where_clause {
                #[verifier(inline)]
                open spec fn early_print_requires(&self) -> bool
                {
                    self.is_constant()
                }

                fn early_print2(&self, Tracked(snpcore): Tracked<&mut crate::registers::SnpCore>, Tracked(console): Tracked<SnpPointsToRaw>) -> (newconsole: Tracked<SnpPointsToRaw>)
                {
                    #print_stmts
                    proof {
                        reveal_strlit("}\n");
                    }
                    let Tracked(console) = new_strlit("}\n").early_print2(Tracked(snpcore), Tracked(console));
                    Tracked(console)
                }
            }
        }
    };
    proc_macro::TokenStream::from(expand2)
}
