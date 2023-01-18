use proc_macro::TokenStream;
use quote::quote;
use syn_verus::{
    parse_macro_input, Attribute, Data, DeriveInput, Expr, Fields, Ident, Meta, NestedMeta, Type,
};

struct ParsedArgs {
    global_ident: Ident,
    type_ident: Type,
    invfn: Expr,
}

impl syn_verus::parse::Parse for ParsedArgs {
    fn parse(input: syn_verus::parse::ParseStream) -> syn_verus::Result<Self> {
        let content;
        syn_verus::parenthesized!(content in input);
        let global_ident = content.parse::<Ident>()?;
        content.parse::<syn_verus::Token![,]>()?;
        let type_ident = content.parse::<Type>()?;
        content.parse::<syn_verus::Token![,]>()?;
        let initfn_tokens: proc_macro2::TokenStream = content.parse()?;
        let invfn = syn_verus::parse2(initfn_tokens)?;
        Ok(ParsedArgs {
            global_ident,
            type_ident,
            invfn,
        })
    }
}

pub fn gen_shared_globals(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = &input.ident;
    let data = &input.data;

    let mut new_variants = Vec::new();
    let mut funcs = Vec::new();

    if let Data::Enum(data_enum) = data {
        for variant in &data_enum.variants {
            if let Fields::Unit = variant.fields {
                let tname_attr = variant
                    .attrs
                    .iter()
                    .find(|attr| attr.path.is_ident("tname"))
                    .expect("Expected #[tname(..)] attribute");
                let args: proc_macro2::TokenStream = tname_attr.tokens.clone().into();
                let parsed_args: ParsedArgs =
                    syn_verus::parse2(args).expect("Failed to parse tname arguments");
                let global_ident = &parsed_args.global_ident;
                let type_ident = &parsed_args.type_ident;
                let invfn = &parsed_args.invfn;
                let variant_name = &variant.ident;
                new_variants.push(variant_name.clone());
                let spec_fn =
                    Ident::new(&format!("spec_{}", variant_name.to_string()), name.span());

                let memrange_fn = Ident::new(
                    &format!("spec_{}_range", variant_name.to_string()),
                    name.span(),
                );
                let lockid_fn = Ident::new(
                    &format!("spec_{}_lockid", variant_name.to_string()),
                    name.span(),
                );
                let contains_fn = Ident::new(
                    &format!("contains_{}", variant_name.to_string()),
                    name.span(),
                );
                let islock_fn = Ident::new(
                    &format!("is_permof_{}", variant_name.to_string()),
                    name.span(),
                );
                let axiom_func_name = Ident::new(
                    &format!("axiom_global_{}", variant_name.to_string().to_uppercase()),
                    name.span(),
                );

                funcs.push(quote! {
                    pub closed spec fn #spec_fn() -> VSpinLock<#type_ident>;
                    #[verifier(inline)]
                    pub open spec fn #memrange_fn() -> (int, nat) {
                        g_range(#name::#variant_name)
                    }
                    #[verifier(inline)]
                    pub open spec fn #lockid_fn() -> int {
                        g_range(#name::#variant_name).0
                    }

                    #[verifier(external_body)]
                    #[verifier(broadcast_forall)]
                    pub proof fn #axiom_func_name()
                    ensures
                        g_range(#name::#variant_name).1 == spec_size::<#type_ident>(),
                        builtin::equal(#spec_fn().ptr_range(), #memrange_fn()),
                        builtin::equal(#spec_fn().lockid(), #lockid_fn()),
                        #spec_fn().is_constant(),
                    {
                    }

                    #[verifier(external_body)]
                    pub fn #variant_name() -> (ret: &'static VSpinLock<#type_ident>)
                    ensures
                        builtin::equal(*ret, #spec_fn()),
                        ret.lockid() == #lockid_fn(),
                        ret.is_constant(),
                    {
                        &#global_ident
                    }

                    #[verifier(inline)]
                    pub open spec fn #contains_fn(m: crate::lock::LockMap) -> bool {
                        m.contains_lock(#lockid_fn(), #memrange_fn()) &&
                        builtin::equal(m[#lockid_fn()]@.invfn.value_invfn(), #invfn) &&
                        builtin::equal(m[#lockid_fn()]@.points_to.snp(), SwSnpMemAttr::spec_default())
                    }

                    #[verifier(inline)]
                    pub open spec fn #islock_fn(lockperm: crate::lock::LockPermToRaw) -> bool {
                        lockperm.lockid() == #lockid_fn() &&
                        lockperm.ptr_range() == #memrange_fn() &&
                        builtin::equal(lockperm.invfn.value_invfn(), #invfn) &&
                        builtin::equal(lockperm.points_to.snp(), SwSnpMemAttr::spec_default())
                    }
                });
            }
        }
    }

    let expanded = quote! {
        verus!{
        pub enum #name {
            #(#new_variants),*
        }
        }
        verus!{
        #[verifier(external_body)]
        #[verifier(broadcast_forall)]
        pub proof fn axiom_global_auto()
        ensures
            forall |v1: #name, v2: #name|
                builtin::imply(!builtin::equal(v1, v2),
                g_range(v1).0 != g_range(v2).0
            ),
            forall |v1: #name, v2: #name|
                builtin::imply(!builtin::equal(v1, v2),
                range_disjoint_(#[trigger]g_range(v1), #[trigger]g_range(v2))),
        {}
        #(#funcs)*
        }
    };
    TokenStream::from(expanded)
}

fn get_type_from_attr(attr: &Attribute) -> Option<syn_verus::Ident> {
    if attr.path.is_ident("tname") {
        if let Ok(Meta::List(meta_list)) = attr.parse_meta() {
            for nested_meta in meta_list.nested {
                if let NestedMeta::Meta(Meta::Path(path)) = nested_meta {
                    return Some(path.get_ident().unwrap().clone());
                }
            }
        }
    }
    None
}
