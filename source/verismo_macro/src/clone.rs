use quote::quote;
use syn_verus::{parse_macro_input, Data, DeriveInput, Lit, LitInt};

pub fn verismo_clone_expand(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    //let strinput = input.to_string();
    //let inputcopy = TokenStream::from_str(&strinput).expect("unreacheable");
    //parse_macro_input!(inputcopy as DeriveInput)
    let input: DeriveInput = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let mut fields_stream = quote! {};
    let generics = &input.generics;
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let mut is_named = false;
    match &input.data {
        Data::Struct(s) => {
            for (i, field) in s.fields.iter().enumerate() {
                match &field.ident {
                    Some(fname) => {
                        is_named = true;
                        fields_stream = quote! {
                            #fields_stream
                            #fname: self.#fname,
                        };
                    }
                    None => {
                        let lit = Lit::Int(LitInt::new(format!("{}", i).as_str(), name.span()));
                        fields_stream = quote! {
                            #fields_stream
                            self.#lit,
                        };
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
    let expand = quote! {
    verus!{
        impl #impl_generics Clone for #name #ty_generics #where_clause  {
            #[verifier(external_body)]
            fn clone(&self) -> (ret: Self)
            ensures
                builtin::equal(ret, *self)
            { #newstruct }
        }
    }
    };

    //println!("{}", expand);
    //let strtoken = newcode.to_string() + &expand.to_string();
    //proc_macro::TokenStream::from_str(&strtoken).expect("wrong code")
    //proc_macro::TokenStream::from(expand)

    proc_macro::TokenStream::from(expand)
}
