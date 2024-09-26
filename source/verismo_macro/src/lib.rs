#![feature(proc_macro_span)]

mod bits;
mod clone;
mod def;
mod default;
mod enum_int;
mod exec_struct;
mod getter;
mod global;
mod new;
//mod op;
mod property;
//mod sec;
mod setter;
//mod size;
mod asm_global;
mod cast_sec;
mod print;
mod snp;
mod spec_eq;
mod spec_size;
mod static_globals;
//mod vdata;

use proc_macro::TokenStream;

#[proc_macro_attribute]
//static with non-zero initialization
pub fn vbit_struct(attribute: TokenStream, item: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    bits::parse_bit_struct(attribute, item)
}

#[proc_macro_attribute]
//static with non-zero initialization
pub fn v_static(attribute: TokenStream, item: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    global::parse_global(attribute, item, true, false)
}

#[proc_macro]
pub fn def_asm_addr_for(input: TokenStream) -> TokenStream { asm_global::asm_global(input) }

#[proc_macro_attribute]
pub fn gen_shared_globals(_attribute: TokenStream, item: TokenStream) -> TokenStream {
    static_globals::gen_shared_globals(item)
}

#[proc_macro_attribute]
//static with non-zero initialization
pub fn v_extern_static(attribute: TokenStream, item: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    global::parse_global(attribute, item, true, true)
}

#[proc_macro_attribute]
// static with zero initialization
pub fn v_zstatic(attribute: TokenStream, item: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    global::parse_global(attribute, item, false, false)
}

/*#[proc_macro_attribute]
pub fn vstateop(attribute: TokenStream, item: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    op::parse_op(attribute, item)
}
*/

#[proc_macro_derive(SpecSize)]
pub fn verismo_size(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    spec_size::verismo_size_expand(input)
}

#[proc_macro_derive(SpecOffset, attributes(def_offset))]
pub fn verismo_defoffset(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    spec_size::verismo_defoffset_expand(input)
}

#[proc_macro_derive(VSpecEq)]
pub fn verismo_eq(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    spec_eq::verismo_eq_expand(input)
}

/*
#[proc_macro_derive(VSecLabel)]
pub fn verismo_security(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    sec::verismo_sec_expand(input)
}
*/

#[proc_macro_derive(WellFormed)]
pub fn verismo_wf(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    //snp::verismo_snp_expand(input, "wf", "WellFormed")
    snp::verismo_snp_expand(input, "wf", "WellFormed")
}

#[proc_macro_derive(IsConstant)]
pub fn verismo_is_constant(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    property::verismo_derive_property_expand(input, "is_constant", "IsConstant")
}

/// Auto generate Clone
#[proc_macro_derive(VClone)]
pub fn verismo_clone(input: TokenStream) -> proc_macro::TokenStream {
    // Parse the input tokens into a syntax tree.
    clone::verismo_clone_expand(input)
}

#[proc_macro_derive(VDefault)]
pub fn verismo_default(input: TokenStream) -> TokenStream { default::verismo_default_expand(input) }

#[proc_macro_derive(VPrint)]
pub fn verismo_print(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    print::verismo_print_expand(input)
}

/// Auto generate VData<T> method for the struct T;
/// Provides VData<T>::<field> -> VData<FieldType>
/*#[proc_macro_derive(VeriSMoData)]
pub fn verismo_data(input: TokenStream) -> proc_macro::TokenStream {
    // Parse the input tokens into a syntax tree.
    vdata::verismo_data_expand(input)
}
*/
/// Auto generate to_stream method for the struct;
/// Provides MemStream<struct>::from_data and SpecType::<struct>::size()
#[proc_macro_derive(VTypeCast)]
pub fn verismo_cast(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    cast_sec::verismo_cast_seq_expand(input, vec!["Seq", "u8"], false)
}

#[proc_macro_derive(VTypeCastSec)]
pub fn verismo_cast_sec(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    cast_sec::verismo_cast_seq_expand(input, vec!["SecSeqByte"], true)
}

/// Auto generate spec_set_#field
/// The spec function will be closed if the field is private
#[proc_macro_derive(SpecSetter, attributes(is_public))]
pub fn verismo_setter(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    setter::verismo_setter_expand(input)
}

/// Auto generate spec_#field
/// The spec function will be closed if the field is private
#[proc_macro_derive(SpecGetter, attributes(is_public))]
pub fn verismo_getter(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    getter::verismo_getter_expand(input)
}

#[proc_macro_derive(SpecIntEnum)]
pub fn verismo_enum_int(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    enum_int::verismo_enum_int_expand(input)
}

#[proc_macro_derive(ExecStruct)]
//static with non-zero initialization
pub fn verismo_exec_struct(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    exec_struct::add_empty_trait_for_struct(input, "ExecStruct")
}

#[proc_macro_derive(NotPrimitive)]
//static with non-zero initialization
pub fn verismo_non_primitive_struct(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree.
    exec_struct::add_empty_trait_for_struct(input, "NotPrimitive")
}
