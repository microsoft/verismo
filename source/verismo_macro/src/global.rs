use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use proc_macro::TokenStream;
use quote::quote;
use syn_verus::spanned::Spanned;
use syn_verus::{parse_macro_input, ItemFn, Signature};

fn string_to_u64(s: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    s.hash(&mut hasher);
    hasher.finish()
}

pub fn parse_global(
    _attr: TokenStream,
    item: TokenStream,
    non_zero: bool,
    need_extern: bool,
) -> TokenStream {
    let input = parse_macro_input!(item as syn_verus::Item);
    let line = input.span().unwrap().start().line() as u64;
    let file = input.span().unwrap().source_file().path();
    let file = file.as_os_str().to_str().unwrap();
    let fileid = string_to_u64(file);
    let unique_id = fileid / 0x10000 * 0x10000 + line;
    let specmem = quote! {crate::arch::addr::SpecMem<crate::arch::addr::GuestVir>};
    let gdef = quote! {crate::verismo::VeriSMoGhost};
    let gspec = quote! {crate::verismo::VeriSMoSpec};
    let vaddrty = quote! {crate::arch::addr::VAddr};
    let extra = match &input {
        syn_verus::Item::Static(syn_verus::ItemStatic { ident, ty, .. }) => {
            //let file = ident.span().source_file().path().display().to_string();
            let addr_ident =
                syn_verus::Ident::new(&format!("mem_{}", ident.to_string()), ident.span());
            let get_ident =
                syn_verus::Ident::new(&format!("{}_get", ident.to_string()), ident.span());
            let axiom_ident =
                syn_verus::Ident::new(&format!("axiom_{}", ident.to_string()), ident.span());
            quote! {
                verus!{
                impl #gspec {
                    #[verifier(inline)]
                    pub open spec fn #addr_ident() -> #specmem
                    {Self::raw_vmem(spec_cast_integer::<_, int>(#unique_id), #non_zero)}
                    pub spec fn #ident() -> crate::verismo::data::VData<#ty>;
                    #[verifier(external_body)]
                    pub broadcast proof fn #axiom_ident()
                    ensures
                        builtin::equal(#[trigger] #gspec::#ident().spec_vmem(),  #[trigger] #gspec::#addr_ident())
                    {}

                    #[verifier(inline)]
                    pub open spec fn #get_ident(&self) -> #ty
                    { Self::#ident().spec_vget(*self)}
                }
                }

                verus!{
                impl #gdef {
                    #[verifier(external_body)]
                    pub fn #ident() -> crate::verismo::data::VData<#ty>
                    {
                        builtin::ensures(|ret: VData<#ty>|[builtin::equal(ret, #gspec::#ident())]);
                        let ret = unsafe {
                            &#ident as *const _ as u64
                        };
                        let vaddr = #vaddrty::new(ret);
                        VData::new(vaddr)
                    }
                }
            }
            }
        }
        syn_verus::Item::Fn(ItemFn {
            sig: Signature { ident, .. },
            ..
        }) => {
            quote! {
                    verus!{
                    impl #gspec {
                        #[verifier(inline)]
                        pub open spec fn #ident() -> #specmem
                        {
                            Self::raw_vmem(spec_cast_integer::<_, int>(#unique_id), true)
                        }
                        }
                    }

                    verus!{
                    impl #gdef {
                        #[verifier(external_body)]
                        #[inline]
                        pub fn #ident() -> #vaddrty
                        {
                            builtin::ensures(|ret: #vaddrty|[builtin::equal(ret.view(), #gspec::#ident().first())]);
                            let ret = unsafe {
                                &#ident as *const _ as u64
                            };
                            #vaddrty::new(ret)
                        }
                    }
                }
            }
        }
        _ => {
            panic! {"Unsupported items"}
        }
    };

    let expanded = if need_extern {
        quote! {
            extern{ #input }

            #extra
        }
    } else {
        quote! {
            #input

            #extra
        }
    };
    //println!("{}", extra);
    proc_macro::TokenStream::from(expanded)
}
