use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn_verus::punctuated::Punctuated;
use syn_verus::spanned::Spanned;
use syn_verus::{
    AngleBracketedGenericArguments, DataStruct, Field, GenericArgument, GenericParam, Generics,
    Ident, Lit, LitInt, Path, PathArguments, PathSegment, TraitBound, TraitBoundModifier, Type, TypeParamBound, TypePath, Visibility,
};

pub fn get_closed_or_open(s: &DataStruct) -> TokenStream {
    let mut close_or_open = quote! {open};
    for (i, field) in s.fields.iter().enumerate() {
        let (_fname, _field_ty) = field_name_ty(&field, i, field.span());
        close_or_open = match &field.vis {
            Visibility::Public(_) => close_or_open,
            _ => {
                quote! {closed}
            }
        };
    }
    close_or_open
}
pub fn new_path(names: &[&str], span: Span) -> Path {
    let mut path_segments = Punctuated::new();
    let mut args = Punctuated::new();

    if names.len() > 1 {
        let next = &names[1..names.len()];
        args.push(GenericArgument::Type(Type::Path(TypePath {
            qself: None,
            path: new_path(next, span),
        })));
        path_segments.push(PathSegment {
            ident: proc_macro2::Ident::new(names[0], span),
            arguments: PathArguments::AngleBracketed(AngleBracketedGenericArguments {
                colon2_token: None,
                lt_token: syn_verus::token::Lt(span),
                args: args,
                gt_token: syn_verus::token::Gt(span),
            }),
        });
    } else {
        path_segments.push(PathSegment {
            ident: proc_macro2::Ident::new(names[0], span),
            arguments: PathArguments::None,
        });
    }
    Path {
        leading_colon: None,
        segments: path_segments,
    }
}
pub fn gen_trait_bound(names: Vec<&str>, span: Span) -> TypeParamBound {
    //let path = TypePath {qself: None, path: new_path(&names.as_slice())};
    TypeParamBound::Trait(TraitBound {
        paren_token: None,
        modifier: TraitBoundModifier::None,
        lifetimes: None,
        path: new_path(&names.as_slice(), span),
    })
}

pub fn add_bound_to_generic(
    generic_for_default: &mut Generics,
    bound: TypeParamBound,
    _span: Span,
) {
    //let mut generic_for_default = generics.clone();
    for gparam in generic_for_default.params.iter_mut() {
        let tmp = gparam.clone();
        match &tmp {
            GenericParam::Type(tparam) => {
                let mut tparam = tparam.clone();
                tparam.bounds.push(bound.clone());
                *gparam = GenericParam::Type(tparam);
            }
            _ => (),
        }
    }
}

pub fn add_bound_to_generic_with_self(
    generic_for_default: &mut Generics,
    bound: Vec<&str>,
    _span: Span,
) {
    //let mut generic_for_default = generics.clone();
    for gparam in generic_for_default.params.iter_mut() {
        let tmp = gparam.clone();
        match &tmp {
            GenericParam::Type(tparam) => {
                let mut tparam = tparam.clone();
                let mut bound = bound.clone();
                let tname = tparam.ident.to_string();
                bound.push(&tname);
                tparam.bounds.push(gen_trait_bound(bound, _span));
                *gparam = GenericParam::Type(tparam);
            }
            _ => (),
        }
    }
}

pub fn type_to_type_generic(ty: &Type) -> Type {
    match ty {
        Type::Path(type_path) => {
            let mut type_path = type_path.clone();
            let _segments_len = type_path.path.segments.len();
            for (_i, segment) in type_path.path.segments.iter_mut().enumerate() {
                if let PathArguments::AngleBracketed(ref mut args) = &mut segment.arguments {
                    let mut new_args = vec![];

                    for arg in &args.args {
                        match arg {
                            GenericArgument::Type(arg_type) => {
                                new_args
                                    .push(GenericArgument::Type(type_to_type_generic(arg_type)));
                            }
                            _ => {
                                new_args.push(arg.clone());
                            }
                        }
                    }

                    // Always add the colon2 token since we want every generic to be in the desired format.
                    segment.arguments =
                        PathArguments::AngleBracketed(syn_verus::AngleBracketedGenericArguments {
                            colon2_token: Some(syn_verus::token::Colon2::default()),
                            ..args.clone()
                        });
                }
            }
            Type::Path(type_path)
        }
        _ => ty.clone(),
    }
}

pub fn is_ghost_or_tracked_type(ty: &Type) -> bool {
    if let Type::Path(tpath) = ty {
        let path_segments = tpath
            .path
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect::<Vec<_>>();
        if path_segments.last() == Some(&"Ghost".to_string()) {
            true
        } else if path_segments.last() == Some(&"Tracked".to_string()) {
            true
        } else {
            false
        }
    } else {
        false
    }
}

pub fn join_tokens(
    v: &Vec<proc_macro2::TokenStream>,
    j: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let mut ret = quote! {};
    for (i, vv) in v.iter().enumerate() {
        ret = if i == 0 {
            vv.clone()
        } else {
            quote! {#ret #j #vv}
        };
    }
    ret
}

pub fn gen_field_calls<T: Fn(&proc_macro2::TokenStream, &Type) -> proc_macro2::TokenStream>(
    fname: &proc_macro2::TokenStream,
    field_ty: &Type,
    tocall: &T,
) -> Vec<proc_macro2::TokenStream> {
    let mut ret = vec![];
    let is_ghost = is_ghost_or_tracked_type(field_ty);
    match field_ty {
        Type::Path(_tpath) => {
            if !is_ghost {
                ret.push(tocall(fname, field_ty))
            }
        }
        Type::Tuple(t) => {
            if t.elems.len() > 0 {
                let _ele_sec_label = quote! {true};
                let mut i = 0;
                for elem in &t.elems {
                    let l = LitInt::new(format!("{}", i).as_str(), elem.span());
                    ret.extend(gen_field_calls(&quote! {#fname.#l}, elem, tocall));
                    i = i + 1;
                }
            }
        }
        _ => ret.push(tocall(fname, field_ty)),
    }
    ret
}

pub fn field_name_ty(field: &Field, i: usize, span: Span) -> (proc_macro2::TokenStream, Type) {
    let field_name = match &field.ident {
        Some(name) => quote! {#name},
        None => {
            let lit = Lit::Int(LitInt::new(format!("{}", i).as_str(), span));
            quote! {#lit}
        }
    };

    (field_name, field.ty.clone())
}

pub fn had_name(field: &Field) -> bool {
    match &field.ident {
        Some(_name) => true,
        None => false,
    }
}

pub fn get_field(fname: &proc_macro2::TokenStream, span: Span) -> Ident {
    let getter_ident = Ident::new(&format!("spec_{}", fname.to_string()), span);
    getter_ident
}

pub fn set_field(fname: &proc_macro2::TokenStream, span: Span) -> Ident {
    syn_verus::Ident::new(&format!("spec_set_{}", fname.to_string()), span)
}

pub fn field_offset(fname: &proc_macro2::TokenStream, span: Span) -> Ident {
    syn_verus::Ident::new(&format!("spec_{}_offset", fname.to_string()), span)
}

pub fn field_offset_exe(fname: &proc_macro2::TokenStream, span: Span) -> Ident {
    syn_verus::Ident::new(&format!("_{}_offset", fname.to_string()), span)
}

pub fn tspec_path() -> TokenStream {
    quote! {crate::tspec}
}

pub fn generic_mod() -> TokenStream {
    let common = tspec_path();
    quote! {#common::size_s}
}

/*
pub fn get_array_len(tyarray: &TypeArray) -> &syn_verus::LitInt {
    if let Expr::Lit(ExprLit {
        lit: Lit::Int(l),
        attrs: _,
    }) = &tyarray.len
    {
        l
    } else {
        panic!("Wrong array size {:#?}", tyarray.len);
    }
}
*/
