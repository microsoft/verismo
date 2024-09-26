use proc_macro::TokenStream;
use quote::quote;
use syn_verus::parse::{Parse, ParseStream};
use syn_verus::{parse_macro_input, Ident, Token};

struct AsmInput {
    func_name: Ident,
    varname: Ident,
}

impl Parse for AsmInput {
    fn parse(input: ParseStream) -> Result<Self, syn_verus::Error> {
        let func_name = input.parse()?;
        input.parse::<Token![=]>()?;
        let varname = input.parse()?;
        Ok(AsmInput { func_name, varname })
    }
}

pub fn asm_global(input: TokenStream) -> TokenStream {
    let AsmInput { func_name, varname } = parse_macro_input!(input);
    let spec_func_name =
        Ident::new(format!("spec_{}", func_name.to_string()).as_str(), func_name.span());
    let asm_str = format!("lea rax, [rip + {}]", varname.to_string());
    let asm_tokens = quote! {
        verus!{
            pub spec fn #spec_func_name() -> int;
        }
        verus!{
            #[verifier(external_body)]
            pub fn #func_name() -> (ret: usize_t)
            ensures
                ret as int == #spec_func_name(),
                ret.is_constant()
            {
                let ret: usize;
                unsafe{
                    core::arch::asm!(
                        #asm_str,
                        lateout("rax") ret,
                    );
                }
                ret as usize
            }
        }
    };

    asm_tokens.into()
}
