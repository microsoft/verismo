use proc_macro::TokenStream;
use quote::quote;
use syn_verus::{parse_macro_input, Data, DeriveInput, ExprLit, Lit};

pub fn verismo_enum_int_expand(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    let mut variant_stream = quote! {};
    let mut variant_stream_u64 = quote! {};
    let mut variant_stream_from = quote! {};
    let mut variant_stream_from_u64 = quote! {};
    let mut variant_stream_from_int = quote! {};
    match input.data {
        Data::Enum(enumdata) => {
            let mut default = 0;
            for (_, variant) in enumdata.variants.iter().enumerate() {
                let ident = &variant.ident;
                match &variant.discriminant {
                    Some(discriminant) => {
                        let expr = &discriminant.1;
                        let default_lit = if let syn_verus::Expr::Lit(ExprLit {
                            lit: Lit::Int(l),
                            attrs: _,
                        }) = expr
                        {
                            l
                        } else {
                            unreachable!()
                        };
                        default = default_lit.base10_parse::<u64>().unwrap();
                    }
                    None => {}
                };
                let fields = if variant.fields.len() == 0 {
                    quote! {}
                } else {
                    let mut f = quote! {};
                    for _ in 0..variant.fields.len() {
                        f = quote! {
                            #f _,
                        };
                    }
                    f
                };
                variant_stream = quote! {
                    #variant_stream
                    #name::#ident #fields => {spec_cast_integer::<_, int> (#default)},
                };

                variant_stream_from_int = quote! {
                    #variant_stream_from_int
                    else if val == spec_cast_integer::<_, int>(#default) {
                        Option::Some(#name::#ident #fields)
                    }
                };

                variant_stream_from_u64 = quote! {
                    #variant_stream_from_u64
                    if val == #default {
                        Option::Some(#name::#ident #fields)
                    } else
                };

                variant_stream_u64 = quote! {
                    #variant_stream_u64
                    #name::#ident #fields => {#default},
                };

                if variant.fields.len() == 0 {
                    variant_stream_from = quote! {
                        #variant_stream_from
                        builtin::equal(Self::spec_from_int(spec_cast_integer::<_, int> (#default)).get_Some_0(), #name::#ident),
                    };
                }

                default = default + 1;
            }
        }
        _ => panic!("Only Enum can be annotated with SpecIntEnum"),
    };

    let tspec = crate::def::tspec_path();
    let expand = quote! {
        verus!{
        impl #tspec::IntValue for #name {
            open spec fn as_int(&self) -> int {
                let val = match self {
                    #variant_stream
                };
                val
            }

            open spec fn from_int(val: int) -> Self {
                Self::spec_from_int(val).get_Some_0()
            }
        }
        impl #tspec::IntOrd for #name {
            open spec fn ord_int(&self) -> int {
                self.as_int()
            }
        }

        impl #name {
                pub open spec fn spec_from_int(val: int) -> Option<Self> {
                    if val < 0 {
                        Option::None
                    }
                    #variant_stream_from_int
                    else {
                        Option::None
                    }
                }

                #[inline]
                pub const fn as_u64(&self) -> (ret: u64)
                ensures
                    ret as int == self.as_int()
                {
                    let ret = match self {
                        #variant_stream_u64
                    };
                    ret
                }

                #[inline]
                pub const fn from_u64(val: u64) -> (ret: Option<Self>)
                ensures
                    builtin::equal(ret, Self::spec_from_int(spec_cast_integer::<_, int>(val)))
                {
                    #variant_stream_from_u64
                    {
                    Option::None
                    }
                }
            }
        }
    };

    proc_macro::TokenStream::from(expand)
}
