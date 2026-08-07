//! Verismo-specific rewriting of Verus syntax.
//!
//! The macros exported by this crate deliberately do **not** implement Verus
//! lowering. They parse still-Verus syntax with `verus_syn`, apply only the
//! transformations that are specific to Verismo (secure integer types, secure
//! operators, the project's specification traits, the project's derives and the
//! synthesized constantness contracts), print the result as still-Verus syntax
//! and hand it to the upstream `builtin_macros::verus!` macro, which performs
//! all the standard Verus lowering.

use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned, ToTokens};
use verus_syn::parse::{Parse, ParseStream};
use verus_syn::punctuated::Punctuated;
use verus_syn::spanned::Spanned;
use verus_syn::visit_mut::{
    visit_expr_mut, visit_impl_item_fn_mut, visit_item_const_mut, visit_item_enum_mut,
    visit_item_fn_mut, visit_item_struct_mut, visit_local_mut, visit_trait_item_fn_mut, VisitMut,
};
use verus_syn::{
    parse_macro_input, AngleBracketedGenericArguments, Attribute, BinOp, DataMode, Ensures, Expr,
    ExprBinary, ExprLit, ExprUnary, FnArgKind, FnMode, Generics, Ident, ImplItemFn, Item,
    ItemConst, ItemEnum, ItemFn, ItemImpl, ItemMod, ItemStruct, ItemTrait, Lit, LitInt, Local,
    Meta, Pat, Path, Requires, ReturnType, Signature, Specification, Stmt, Token, TraitItemFn,
    Type, TypeArray, UnOp,
};

/// Which constantness clauses the macro synthesizes on executable functions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ContractMode {
    /// Synthesize nothing (`verismo_simple!`).
    None,
    /// Only `inputs constant ==> outputs constant` (`verismo!`).
    PreserveConstant,
    /// Explicitly require constant inputs, guarantee constant outputs, and keep
    /// the preservation implication (`verismo_non_secret!`).
    RequireConstant,
}

impl ContractMode {
    fn synthesizes_clauses(&self) -> bool {
        !matches!(self, ContractMode::None)
    }

    fn requires_constant_inputs(&self) -> bool {
        matches!(self, ContractMode::RequireConstant)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InsideArith {
    None,
    Widen,
    Fixed,
}

#[derive(Debug)]
struct Visitor {
    /// `> 0` while visiting ghost (spec/proof) code.
    inside_ghost: u32,
    /// `> 0` while visiting a type.
    inside_type: u32,
    /// Whether the enclosing arithmetic context widens its operands. Literals
    /// are given a fixed-width secure type in `Fixed` (bitwise) contexts.
    inside_arith: InsideArith,
    /// `true` while visiting the left-hand side of an assignment.
    assign_to: bool,
    /// `true` inside `assert(..) by(bit_vector)`, where the native fixed-width
    /// operators must be kept.
    inside_bitvector: bool,
    /// `true` inside code marked external to the verifier.
    inside_external: bool,
    contract: ContractMode,
}

macro_rules! quote_verbatim {
    ($span:expr, $attrs:tt => $($tok:tt)*) => {
        Expr::Verbatim(quote_spanned!{ $span => #(#$attrs)* $($tok)* })
    }
}

fn take_expr(expr: &mut Expr) -> Expr {
    let dummy: Expr = Expr::Verbatim(TokenStream::new());
    std::mem::replace(expr, dummy)
}

fn path_is_ident(path: &Path, s: &str) -> bool {
    let segments = &path.segments;
    segments.len() == 1 && segments.first().unwrap().ident == s
}

/// `#[derive(..)]` and friends.
fn mk_rust_attr(span: Span, name: &str, tokens: TokenStream) -> Attribute {
    let ident = Ident::new(name, span);
    verus_syn::parse_quote_spanned! { span => #[#ident(#tokens)] }
}

/// The project derives that every executable struct declared inside one of the
/// Verismo macros must have.
fn struct_data_mode_attrs(mode: &DataMode, inside_external: bool) -> Vec<Attribute> {
    let tk = if inside_external {
        quote! { ExecStruct, NotPrimitive }
    } else {
        quote! { ExecStruct, NotPrimitive, VTypeCastSec, SpecSize, SpecOffset, WellFormed, IsConstant }
    };
    match mode {
        DataMode::Default | DataMode::Exec(_) => {
            vec![mk_rust_attr(mode.span(), "derive", tk)]
        }
        _ => vec![],
    }
}

fn attr_is_external(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|a| match &a.meta {
        Meta::List(list) => matches!(
            list.tokens.to_string().as_str(),
            "external_body" | "external" | "external_fn_specification"
        ),
        _ => false,
    })
}

fn is_exe(sig: &Signature) -> bool {
    match sig.mode {
        FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_) | FnMode::ProofAxiom(_) => {
            false
        }
        FnMode::Exec(_) | FnMode::Default => true,
    }
}

fn is_ghost_or_tracked_type(ty: &Type) -> bool {
    if let Type::Path(tpath) = ty {
        match tpath.path.segments.last() {
            Some(last) => last.ident == "Ghost" || last.ident == "Tracked",
            None => false,
        }
    } else {
        false
    }
}

fn is_generic(ty: &Type, generics: &Generics) -> bool {
    for generic in &generics.params {
        if let verus_syn::GenericParam::Type(typaram) = generic {
            if let Type::Path(tpath) = ty {
                if let Some(name) = tpath.path.segments.last() {
                    if name.ident == typaram.ident {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// Collect the `(pre, post)` expressions naming every non-ghost, non-generic
/// value reachable from a parameter or a named return value. These are the
/// values whose constantness the synthesized contracts talk about.
fn param_list(
    pat: &Pat,
    ty: &Type,
    is_mut: bool,
    ret: &mut Vec<(Option<Expr>, Option<Expr>)>,
    generics: &Generics,
    is_param: bool,
) {
    let prefix = if is_mut {
        quote! {*old}
    } else {
        quote! {}
    };
    match ty {
        Type::Array(_) | Type::Path(_) | Type::Slice(_) => {
            if is_ghost_or_tracked_type(ty) || is_generic(ty, generics) {
                return;
            }
            if is_param {
                ret.push((Some(Expr::Verbatim(quote! {(#prefix(#pat))})), None));
            } else {
                ret.push((None, Some(Expr::Verbatim(quote! {(#prefix(#pat))}))));
            }
        }
        Type::Reference(r) => {
            param_list(pat, &r.elem, r.mutability.is_some(), ret, generics, is_param);
        }
        Type::Tuple(tup) => {
            for (i, ty) in tup.elems.iter().enumerate() {
                let index = LitInt::new(format!("{}", i).as_str(), tup.span());
                let p = Pat::Verbatim(quote! {(#prefix(#pat)).#index});
                param_list(&p, ty, false, ret, generics, is_param);
            }
        }
        Type::BareFn(_)
        | Type::Never(_)
        | Type::Verbatim(_)
        | Type::FnSpec(_)
        | Type::FnProof(_) => {}
        _ => {}
    }
}

impl Visitor {
    /// Replace an executable primitive integer type with its secure wrapper and
    /// an executable array type with the project's `Array<T, N>`.
    fn replace_stype(&self, ty: &mut Type, must_replace: bool) {
        let span = ty.span();

        match ty {
            Type::Array(TypeArray { elem, len, .. }) => {
                if !self.inside_external || must_replace {
                    *ty = Type::Verbatim(quote_spanned! { span => Array<#elem, #len> });
                } else {
                    *ty = Type::Verbatim(quote_spanned! { span => [#elem; #len] });
                }
            }
            Type::Path(patht)
                if (!self.inside_external && self.inside_ghost == 0 && !self.inside_bitvector)
                    || must_replace =>
            {
                let tpath = &patht.path;
                for (name, sec) in [
                    ("u64", quote! {u64_s}),
                    ("u32", quote! {u32_s}),
                    ("u16", quote! {u16_s}),
                    ("u8", quote! {u8_s}),
                    ("usize", quote! {usize_s}),
                ] {
                    if path_is_ident(tpath, name) {
                        *ty = Type::Verbatim(quote_spanned! { span => #sec });
                        break;
                    }
                }
            }
            _ => {}
        }
    }

    /// Rewrite an executable signature: securify the return type and synthesize
    /// the constantness contract clauses required by the current mode.
    ///
    /// Returns the statements to splice in at the top of the function body.
    fn visit_fn(&mut self, sig: &mut Signature) -> Vec<Stmt> {
        let mut stmts: Vec<Stmt> = Vec::new();
        if !self.inside_external && is_exe(sig) {
            let mut varlist = vec![];
            for arg in &sig.inputs {
                match &arg.kind {
                    FnArgKind::Receiver(receiver) => {
                        let (pre_varname, post_varname) = if receiver.mutability.is_some() {
                            (
                                Some(Expr::Verbatim(quote! {(*old(self))})),
                                Some(Expr::Verbatim(quote! {(*self)})),
                            )
                        } else {
                            (Some(Expr::Verbatim(quote! {self})), None)
                        };
                        varlist.push((pre_varname, post_varname));
                    }
                    FnArgKind::Typed(pat) => {
                        param_list(&pat.pat, &pat.ty, false, &mut varlist, &sig.generics, true)
                    }
                };
            }

            let output = sig.output.clone();
            match output {
                ReturnType::Default => {}
                ReturnType::Type(tk, tracked, ret_opt, ty) => {
                    let mut tmp = ty.clone();
                    self.replace_stype(&mut tmp, !self.inside_external);

                    if tracked.is_none() {
                        if let Some(ret) = &ret_opt {
                            let (_, pat, _) = &**ret;
                            param_list(pat, &ty, false, &mut varlist, &sig.generics, false);
                        }
                    }
                    sig.output = ReturnType::Type(tk, tracked, ret_opt, tmp);
                }
            }

            if self.contract.synthesizes_clauses() {
                self.add_constantness_clauses(sig, &varlist, &mut stmts);
            }
        }
        self.inside_bitvector = false;
        stmts
    }

    fn add_constantness_clauses(
        &mut self,
        sig: &mut Signature,
        varlist: &[(Option<Expr>, Option<Expr>)],
        stmts: &mut Vec<Stmt>,
    ) {
        let explicit = self.contract.requires_constant_inputs();
        let mut pres: Punctuated<Expr, Token![,]> = Punctuated::new();
        let mut posts: Punctuated<Expr, Token![,]> = Punctuated::new();
        let mut constant_pre = quote! {true};
        let mut constant_post = quote! {true};

        for (pre, post) in varlist {
            if let Some(var) = pre {
                constant_pre = quote! { #constant_pre && #var.is_constant() };
                if explicit {
                    pres.push(Expr::Verbatim(quote! {#var.is_constant()}));
                }
                // Expose the closed `wf_value()` type invariant of each input in
                // the body. `wf()` is trivially true, so a precondition would add
                // no proof power; `use_type_invariant` is the only thing that
                // surfaces the real fact. Skip the receiver forms, whose
                // identifiers may not be in scope or addressable here.
                let var_ts = var.to_token_stream().to_string();
                if var_ts != "self"
                    && var_ts != "(* old (self))"
                    && var_ts != "(* self)"
                    && !var_ts.contains("old")
                {
                    stmts.push(Stmt::Expr(
                        Expr::Verbatim(quote! {
                            proof {
                                use_type_invariant(& #var);
                            }
                        }),
                        Some(Token![;](Span::call_site())),
                    ));
                }
            }

            if let Some(var) = post {
                constant_post = quote! { #constant_post && #var.is_constant() };
                if explicit {
                    posts.push(Expr::Verbatim(quote! {#var.is_constant()}));
                }
            }
        }

        posts.push(Expr::Verbatim(quote! {builtin::imply(#constant_pre, #constant_post)}));

        if !pres.is_empty() {
            match &mut sig.spec.requires {
                Some(requires) => requires.exprs.exprs.extend(pres),
                None => {
                    sig.spec.requires = Some(Requires {
                        token: Token![requires](sig.spec.requires.span()),
                        exprs: Specification { exprs: pres },
                    });
                }
            }
        }

        match &mut sig.spec.ensures {
            Some(ensures) => ensures.exprs.exprs.extend(posts),
            None => {
                sig.spec.ensures = Some(Ensures {
                    attrs: vec![],
                    token: Token![ensures](sig.spec.ensures.span()),
                    exprs: Specification { exprs: posts },
                });
            }
        }
    }
}

impl VisitMut for Visitor {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        let is_inside_bitvector = match &expr {
            Expr::Assert(a) => match &a.prover {
                Some((_, id)) => {
                    if id == "bit_vector" {
                        self.inside_bitvector = true;
                        true
                    } else {
                        false
                    }
                }
                None => false,
            },
            _ => false,
        };

        let is_auto_proof_block = self.inside_ghost == 0
            && matches!(expr, Expr::Assume(..) | Expr::Assert(..) | Expr::AssertForall(..));
        if is_auto_proof_block {
            self.inside_ghost += 1;
        }

        let mode_block = match &*expr {
            Expr::Unary(ExprUnary { op: UnOp::Proof(..), .. }) => true,
            Expr::Call(call) if call.args.len() == 1 => match &*call.func {
                Expr::Path(path) => {
                    path.qself.is_none()
                        && (path_is_ident(&path.path, "Ghost")
                            || path_is_ident(&path.path, "Tracked"))
                }
                _ => false,
            },
            _ => false,
        };

        let sub_inside_arith = match &*expr {
            Expr::Paren(..) | Expr::Block(..) | Expr::Group(..) => self.inside_arith,
            Expr::Cast(..) => InsideArith::Widen,
            Expr::Unary(unary) => match unary.op {
                UnOp::Neg(..) => InsideArith::Widen,
                UnOp::Not(..) => InsideArith::Fixed,
                _ => InsideArith::None,
            },
            Expr::Binary(binary) => match binary.op {
                BinOp::Add(..)
                | BinOp::Sub(..)
                | BinOp::Mul(..)
                | BinOp::Eq(..)
                | BinOp::Ne(..)
                | BinOp::Lt(..)
                | BinOp::Le(..)
                | BinOp::Gt(..)
                | BinOp::Ge(..) => InsideArith::Widen,
                BinOp::Div(..) | BinOp::Rem(..) => InsideArith::None,
                BinOp::BitXor(..)
                | BinOp::BitAnd(..)
                | BinOp::BitOr(..)
                | BinOp::Shl(..)
                | BinOp::Shr(..) => InsideArith::Fixed,
                _ => InsideArith::None,
            },
            _ => InsideArith::None,
        };
        let sub_assign_to = matches!(&*expr, Expr::Field(..)) && self.assign_to;

        let is_inside_ghost = self.inside_ghost > 0;
        let is_inside_arith = self.inside_arith;
        let is_assign_to = self.assign_to;
        // Ghost code goes to the project's specification traits; executable code
        // goes to the secure operators.
        let use_spec_traits = is_inside_ghost;
        if mode_block {
            self.inside_ghost += 1;
        }
        self.inside_arith = sub_inside_arith;
        self.assign_to = sub_assign_to;
        let assign_left = if let Expr::Assign(assign) = expr {
            let mut left = take_expr(&mut assign.left);
            self.assign_to = true;
            self.visit_expr_mut(&mut left);
            self.assign_to = false;
            Some(left)
        } else {
            None
        };
        visit_expr_mut(self, expr);
        if let Expr::Assign(assign) = expr {
            assign.left = Box::new(assign_left.expect("assign_left"));
        }
        if mode_block {
            self.inside_ghost -= 1;
        }
        self.inside_arith = is_inside_arith;
        self.assign_to = is_assign_to;

        let do_replace = match &expr {
            Expr::Lit(ExprLit { lit: Lit::Int(..), .. }) => true,
            Expr::Cast(..) => true,
            Expr::Index(..) if !self.inside_external => true,
            Expr::Unary(ExprUnary { op: UnOp::Neg(..) | UnOp::Not(..), .. }) => true,
            Expr::Binary(ExprBinary {
                op:
                    BinOp::Eq(..)
                    | BinOp::Ne(..)
                    | BinOp::Le(..)
                    | BinOp::Lt(..)
                    | BinOp::Ge(..)
                    | BinOp::Gt(..)
                    | BinOp::Add(..)
                    | BinOp::Sub(..)
                    | BinOp::Mul(..)
                    | BinOp::Div(..)
                    | BinOp::Rem(..)
                    | BinOp::BitAnd(..)
                    | BinOp::BitOr(..)
                    | BinOp::BitXor(..)
                    | BinOp::Shl(..)
                    | BinOp::Shr(..),
                ..
            }) => true,
            _ => false,
        };
        let use_sec_type = !self.inside_bitvector
            && !use_spec_traits
            && !self.inside_external
            && (self.inside_type == 0);

        let const_fn = if !use_spec_traits {
            quote! {constant}
        } else {
            quote! {spec_constant}
        };

        let replace_exe_op = !is_inside_ghost && (self.inside_type == 0);
        let sec_const = quote! {SecType::#const_fn};
        if do_replace && self.inside_type == 0 {
            let e = take_expr(expr);
            match e {
                Expr::Lit(ExprLit { lit: Lit::Int(lit), attrs }) => {
                    let span = lit.span();
                    let n = lit.base10_digits().to_string();
                    if lit.suffix().is_empty() {
                        match is_inside_arith {
                            InsideArith::None => {
                                // Defer the integer type to inference, or make it
                                // a secure constant in executable code.
                                *expr = if !use_sec_type {
                                    quote_verbatim!(span, attrs => ::builtin::spec_literal_integer(#n))
                                } else {
                                    let lit =
                                        Expr::Lit(ExprLit { lit: Lit::Int(lit), attrs: vec![] });
                                    quote_verbatim! {span, attrs => #sec_const(#lit) }
                                };
                            }
                            InsideArith::Widen if n.starts_with('-') => {
                                *expr = if !use_sec_type {
                                    quote_verbatim! {span, attrs => (::builtin::spec_literal_int(#n)) }
                                } else {
                                    let lit =
                                        Expr::Lit(ExprLit { lit: Lit::Int(lit), attrs: vec![] });
                                    quote_verbatim! {span, attrs => #sec_const(#lit) }
                                };
                            }
                            InsideArith::Widen => {
                                *expr = if !use_sec_type {
                                    quote_verbatim! {span, attrs => (::builtin::spec_literal_nat(#n)) }
                                } else {
                                    let lit =
                                        Expr::Lit(ExprLit { lit: Lit::Int(lit), attrs: vec![] });
                                    quote_verbatim! {span, attrs => #sec_const(#lit) }
                                };
                            }
                            InsideArith::Fixed => {
                                // Bitwise operators keep Rust's native literals.
                                let newexpr =
                                    Expr::Lit(ExprLit { lit: Lit::Int(lit), attrs: vec![] });
                                *expr = if !use_sec_type {
                                    quote_verbatim! {span, attrs => (#newexpr) }
                                } else {
                                    quote_verbatim! {span, attrs => #sec_const(#newexpr) }
                                };
                            }
                        }
                    } else if lit.suffix() == "int" {
                        *expr = if use_spec_traits {
                            quote_verbatim! {span, attrs => (::builtin::spec_literal_int(#n)) }
                        } else {
                            panic!("No int in exe")
                        };
                    } else if lit.suffix() == "nat" {
                        *expr = quote_verbatim! {span, attrs => (::builtin::spec_literal_nat(#n))};
                    } else if lit.suffix().ends_with("_s") {
                        let tmp = Expr::Lit(ExprLit {
                            lit: Lit::Int(LitInt::new(
                                lit.to_string().as_str().replace("_s", "").as_str(),
                                lit.span(),
                            )),
                            attrs: vec![],
                        });
                        let ident = Ident::new(lit.suffix(), lit.span());

                        *expr = quote_verbatim! {span, attrs => #ident::#const_fn(#tmp)};
                    } else if lit.suffix().ends_with("_t") {
                        let tmp = Expr::Lit(ExprLit {
                            lit: Lit::Int(LitInt::new(
                                lit.to_string().as_str().replace("_t", "").as_str(),
                                lit.span(),
                            )),
                            attrs: vec![],
                        });

                        *expr = quote_verbatim! {span, attrs => #tmp};
                    } else {
                        // Native Rust integer suffix: keep it, but make it a
                        // secure literal in executable code.
                        *expr = if !use_sec_type {
                            let tmp = Expr::Lit(ExprLit { lit: Lit::Int(lit), attrs: vec![] });
                            quote_verbatim! {span, attrs => (#tmp) }
                        } else {
                            let ident =
                                Ident::new(format!("{}_s", lit.suffix()).as_str(), lit.span());
                            let tmp = Expr::Lit(ExprLit { lit: Lit::Int(lit), attrs: vec![] });
                            quote_verbatim! {span, attrs => #ident::#const_fn(#tmp) }
                        };
                    }
                }
                Expr::Cast(cast) => {
                    let span = cast.span();
                    let src = &cast.expr;
                    let attrs: Vec<Attribute> = cast.attrs.clone();
                    let mut ty = cast.ty.clone();
                    *expr = if self.inside_ghost > 0 {
                        quote_verbatim!(span, attrs => VTypeCast::<#ty>::vspec_cast_to(#src))
                    } else if !self.inside_external {
                        // Keep primitive narrowing/widening casts as `as` to avoid
                        // requiring nonexistent `Into<u8> for u64` impls. Only rewrite
                        // when the target is a non-primitive, so we route through the
                        // project's `Into` impls for `SecType`, etc.
                        let ty_trim = ty.to_token_stream().to_string().replace(' ', "");
                        let is_primitive = matches!(
                            ty_trim.as_str(),
                            "u8" | "u16"
                                | "u32"
                                | "u64"
                                | "u128"
                                | "usize"
                                | "i8"
                                | "i16"
                                | "i32"
                                | "i64"
                                | "i128"
                                | "isize"
                                | "bool"
                                | "char"
                                | "f32"
                                | "f64"
                        );
                        if is_primitive {
                            Expr::Cast(cast)
                        } else {
                            self.replace_stype(&mut ty, true);
                            quote_verbatim!(span, attrs => core::convert::Into::<#ty>::into(#src))
                        }
                    } else {
                        Expr::Cast(cast)
                    };
                }
                Expr::Index(idx) => {
                    let span = idx.span();
                    let src = idx.expr;
                    let attrs = idx.attrs;
                    let index = idx.index;
                    if use_spec_traits {
                        *expr = quote_verbatim!(span, attrs => #src.spec_index(#index));
                    } else if replace_exe_op {
                        *expr = quote_verbatim!(span, attrs => #src.index(#index));
                    }
                }
                Expr::Unary(unary) => {
                    let span = unary.span();
                    let attrs = unary.attrs;
                    let arg = unary.expr;
                    match unary.op {
                        UnOp::Neg(_) => {
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => (#arg).spec_neg());
                            } else if replace_exe_op {
                                *expr = quote_verbatim!(span, attrs => (#arg).neg());
                            }
                        }
                        UnOp::Not(_) => {
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => (#arg).spec_not());
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => (#arg).not());
                            }
                        }
                        _ => panic!("unary"),
                    }
                }
                Expr::Binary(binary) => {
                    let b = binary.clone();
                    let span = b.span();
                    let attrs = b.attrs;
                    let right = b.right;
                    let left = {
                        let l = b.left;
                        quote_spanned! { l.span() => (#l) }
                    };
                    match b.op {
                        BinOp::Eq(..) => {
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_eq(#right));
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.eq(&#right));
                            }
                        }
                        BinOp::Ne(..) => {
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => !(#left.spec_eq(#right)));
                            } else if !is_inside_ghost {
                                *expr = Expr::Verbatim(quote! {!(#left.eq(&#right))});
                            }
                        }
                        BinOp::Le(..) => {
                            if use_spec_traits {
                                *expr = Expr::Binary(binary);
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.le(&#right));
                            }
                        }
                        BinOp::Lt(..) => {
                            if use_spec_traits {
                                *expr = Expr::Binary(binary);
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.lt(&#right));
                            }
                        }
                        BinOp::Ge(..) => {
                            if use_spec_traits {
                                *expr = Expr::Binary(binary);
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.ge(&#right));
                            }
                        }
                        BinOp::Gt(..) => {
                            if use_spec_traits {
                                *expr = Expr::Binary(binary);
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.gt(&#right));
                            }
                        }
                        BinOp::Add(..) if !self.inside_bitvector => {
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_add(#right));
                            } else if replace_exe_op {
                                *expr = quote_verbatim!(span, attrs => #left.add(#right));
                            }
                        }
                        BinOp::Sub(..) if !self.inside_bitvector => {
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_sub(#right));
                            } else if replace_exe_op {
                                *expr = quote_verbatim!(span, attrs => #left.sub(#right));
                            }
                        }
                        BinOp::Mul(..) if !self.inside_bitvector => {
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_mul(#right));
                            } else if replace_exe_op {
                                *expr = quote_verbatim!(span, attrs => #left.mul(#right));
                            }
                        }
                        BinOp::Add(..) | BinOp::Sub(..) | BinOp::Mul(..) => {
                            *expr = quote_verbatim!(span, attrs => compile_error!("Inside bit-vector assertion, use `add` `sub` `mul` for fixed-bit operators, instead of `+` `-` `*`. (see the functions builtin::add(left, right), builtin::sub(left, right), and builtin::mul(left, right))"));
                        }
                        BinOp::Div(..) => {
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_euclidean_or_real_div(#right));
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.div(#right));
                            }
                        }
                        BinOp::Rem(..) => {
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_euclidean_mod(#right));
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.rem(#right));
                            };
                        }
                        BinOp::BitAnd(..) => {
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_bitand(#right));
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.bitand(#right));
                            }
                        }
                        BinOp::BitOr(..) => {
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_bitor(#right));
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.bitor(#right));
                            }
                        }
                        BinOp::BitXor(..) => {
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_bitxor(#right));
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.bitxor(#right));
                            }
                        }
                        BinOp::Shl(..) => {
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_shl(#right));
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.shl(#right));
                            }
                        }
                        BinOp::Shr(..) => {
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_shr(#right));
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.shr(#right));
                            }
                        }
                        _ => panic!("binary"),
                    }
                }
                _ => *expr = e,
            }
        }
        if is_inside_bitvector {
            self.inside_bitvector = false;
        }
        if is_auto_proof_block {
            self.inside_ghost -= 1;
        }
    }

    /// Apply the Verismo replacements inside `#![trigger ...]` so that triggers
    /// keep matching the shape of the rewritten bodies.
    fn visit_attribute_mut(&mut self, attr: &mut Attribute) {
        if !attr.path().is_ident("trigger") {
            return;
        }
        let Meta::List(list) = &mut attr.meta else {
            return;
        };
        if list.tokens.is_empty() {
            return;
        }
        let Ok(spec) = verus_syn::parse2::<Specification>(list.tokens.clone()) else {
            return;
        };
        let mut exprs = spec.exprs;
        for e in exprs.iter_mut() {
            self.visit_expr_mut(e);
        }
        list.tokens = quote! { #exprs };
    }

    fn visit_local_mut(&mut self, local: &mut Local) {
        let is_ghost = local.tracked.is_some() || local.ghost.is_some();
        if is_ghost {
            self.inside_ghost += 1;
        }
        visit_local_mut(self, local);
        if is_ghost {
            self.inside_ghost -= 1;
        }
    }

    fn visit_requires_mut(&mut self, i: &mut verus_syn::Requires) {
        self.inside_ghost += 1;
        verus_syn::visit_mut::visit_requires_mut(self, i);
        self.inside_ghost -= 1;
    }

    fn visit_ensures_mut(&mut self, i: &mut verus_syn::Ensures) {
        self.inside_ghost += 1;
        verus_syn::visit_mut::visit_ensures_mut(self, i);
        self.inside_ghost -= 1;
    }

    fn visit_default_ensures_mut(&mut self, i: &mut verus_syn::DefaultEnsures) {
        self.inside_ghost += 1;
        verus_syn::visit_mut::visit_default_ensures_mut(self, i);
        self.inside_ghost -= 1;
    }

    fn visit_returns_mut(&mut self, i: &mut verus_syn::Returns) {
        self.inside_ghost += 1;
        verus_syn::visit_mut::visit_returns_mut(self, i);
        self.inside_ghost -= 1;
    }

    fn visit_decreases_mut(&mut self, i: &mut verus_syn::Decreases) {
        self.inside_ghost += 1;
        verus_syn::visit_mut::visit_decreases_mut(self, i);
        self.inside_ghost -= 1;
    }

    fn visit_recommends_mut(&mut self, i: &mut verus_syn::Recommends) {
        self.inside_ghost += 1;
        verus_syn::visit_mut::visit_recommends_mut(self, i);
        self.inside_ghost -= 1;
    }

    fn visit_invariant_mut(&mut self, i: &mut verus_syn::Invariant) {
        self.inside_ghost += 1;
        verus_syn::visit_mut::visit_invariant_mut(self, i);
        self.inside_ghost -= 1;
    }

    fn visit_invariant_except_break_mut(&mut self, i: &mut verus_syn::InvariantExceptBreak) {
        self.inside_ghost += 1;
        verus_syn::visit_mut::visit_invariant_except_break_mut(self, i);
        self.inside_ghost -= 1;
    }

    fn visit_invariant_ensures_mut(&mut self, i: &mut verus_syn::InvariantEnsures) {
        self.inside_ghost += 1;
        verus_syn::visit_mut::visit_invariant_ensures_mut(self, i);
        self.inside_ghost -= 1;
    }

    fn visit_item_fn_mut(&mut self, fun: &mut ItemFn) {
        let is_external = self.inside_external;
        self.inside_external = attr_is_external(&fun.attrs);
        self.inside_ghost = if is_exe(&fun.sig) { 0 } else { 1 };
        let stmts = self.visit_fn(&mut fun.sig);
        fun.block.stmts.splice(0..0, stmts);
        fun.semi_token = None;
        visit_item_fn_mut(self, fun);
        self.inside_ghost = 0;
        self.inside_external = is_external;
    }

    fn visit_impl_item_fn_mut(&mut self, method: &mut ImplItemFn) {
        let is_external = self.inside_external;
        self.inside_external = attr_is_external(&method.attrs);
        self.inside_ghost = if is_exe(&method.sig) { 0 } else { 1 };
        let stmts = self.visit_fn(&mut method.sig);
        method.block.stmts.splice(0..0, stmts);
        method.semi_token = None;
        visit_impl_item_fn_mut(self, method);
        self.inside_external = is_external;
        self.inside_ghost = 0;
    }

    fn visit_trait_item_fn_mut(&mut self, method: &mut TraitItemFn) {
        self.inside_ghost = if is_exe(&method.sig) { 0 } else { 1 };
        // Trait method declarations get the securified signature and the
        // synthesized contract, but no body statements: the `use_type_invariant`
        // calls belong to the implementations, not to the declaration.
        let _stmts = self.visit_fn(&mut method.sig);
        visit_trait_item_fn_mut(self, method);
        self.inside_ghost = 0;
    }

    fn visit_item_const_mut(&mut self, con: &mut ItemConst) {
        let is_external = self.inside_external;
        self.inside_external = attr_is_external(&con.attrs);
        visit_item_const_mut(self, con);
        self.inside_external = is_external;
    }

    fn visit_item_enum_mut(&mut self, item: &mut ItemEnum) {
        let is_external = self.inside_external;
        self.inside_external = attr_is_external(&item.attrs);
        visit_item_enum_mut(self, item);
        self.inside_external = is_external;
    }

    fn visit_item_struct_mut(&mut self, item: &mut ItemStruct) {
        let is_external = self.inside_external;
        self.inside_external = attr_is_external(&item.attrs);
        visit_item_struct_mut(self, item);
        item.attrs.extend(struct_data_mode_attrs(&item.mode, self.inside_external));
        self.inside_external = is_external;
    }

    fn visit_type_mut(&mut self, ty: &mut Type) {
        self.inside_type += 1;
        verus_syn::visit_mut::visit_type_mut(self, ty);
        self.inside_type -= 1;

        self.replace_stype(ty, false);
    }

    fn visit_path_mut(&mut self, path: &mut Path) {
        // Generic type arguments can appear inside paths.
        self.inside_type += 1;
        verus_syn::visit_mut::visit_path_mut(self, path);
        self.inside_type -= 1;
    }

    fn visit_angle_bracketed_generic_arguments_mut(
        &mut self,
        args: &mut AngleBracketedGenericArguments,
    ) {
        // Turbofish arguments on method calls are types too.
        self.inside_type += 1;
        verus_syn::visit_mut::visit_angle_bracketed_generic_arguments_mut(self, args);
        self.inside_type -= 1;
    }

    fn visit_item_mod_mut(&mut self, item: &mut ItemMod) {
        let is_external = self.inside_external;
        self.inside_external = attr_is_external(&item.attrs);
        verus_syn::visit_mut::visit_item_mod_mut(self, item);
        self.inside_external = is_external;
    }

    fn visit_item_impl_mut(&mut self, imp: &mut ItemImpl) {
        let is_external = self.inside_external;
        self.inside_external = attr_is_external(&imp.attrs);
        verus_syn::visit_mut::visit_item_impl_mut(self, imp);
        self.inside_external = is_external;
    }

    fn visit_item_trait_mut(&mut self, tr: &mut ItemTrait) {
        let is_external = self.inside_external;
        self.inside_external = attr_is_external(&tr.attrs);
        verus_syn::visit_mut::visit_item_trait_mut(self, tr);
        self.inside_external = is_external;
    }
}

struct Items {
    items: Vec<Item>,
}

impl Parse for Items {
    fn parse(input: ParseStream) -> verus_syn::parse::Result<Items> {
        let mut items = Vec::new();
        while !input.is_empty() {
            items.push(input.parse()?);
        }
        Ok(Items { items })
    }
}

/// Apply the Verismo replacements to `stream`, which must contain items written
/// in Verus syntax, and return the result, still in Verus syntax.
#[cfg(test)]
pub(crate) fn transform_items(
    stream: TokenStream,
    contract: ContractMode,
) -> verus_syn::parse::Result<TokenStream> {
    let items: Items = verus_syn::parse2(stream)?;
    Ok(transform_parsed_items(items.items, contract))
}

fn transform_parsed_items(items: Vec<Item>, contract: ContractMode) -> TokenStream {
    let mut visitor = Visitor {
        inside_ghost: 0,
        inside_type: 0,
        inside_arith: InsideArith::None,
        assign_to: false,
        inside_bitvector: false,
        inside_external: false,
        contract,
    };
    let mut new_stream = TokenStream::new();
    for mut item in items {
        visitor.visit_item_mut(&mut item);
        visitor.inside_ghost = 0;
        visitor.inside_arith = InsideArith::None;
        item.to_tokens(&mut new_stream);
    }
    new_stream
}

/// Entry point used by the exported proc macros: apply the Verismo replacements
/// and hand the still-Verus result to the upstream `verus!` macro, which does
/// all the standard Verus lowering.
pub(crate) fn rewrite_items(
    stream: proc_macro::TokenStream,
    contract: ContractMode,
) -> proc_macro::TokenStream {
    // macro_rules `tt` fragments split tokens like `==>` and `&&&` apart; put
    // them back together before parsing.
    let stream = proc_macro::TokenStream::from(verus_syn::rejoin_tokens(stream.into()));
    let items: Items = parse_macro_input!(stream as Items);
    let new_stream = transform_parsed_items(items.items, contract);
    proc_macro::TokenStream::from(quote! { ::builtin_macros::verus! { #new_stream } })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Parse the single `ItemFn` produced by transforming `input`.
    fn transform_one_fn(input: TokenStream, contract: ContractMode) -> ItemFn {
        let out = transform_items(input, contract).expect("transform failed");
        verus_syn::parse2::<ItemFn>(out).expect("output is not a single parseable fn")
    }

    fn sample() -> TokenStream {
        quote! {
            pub fn add(a: u64, b: u64) -> (ret: u64) {
                a + b
            }
        }
    }

    /// Normalized token text of a spec clause, or `None` when absent.
    fn clause_texts(spec: Option<&Specification>) -> Vec<String> {
        match spec {
            None => vec![],
            Some(spec) => spec
                .exprs
                .iter()
                .map(|e| e.to_token_stream().to_string().replace(' ', ""))
                .collect(),
        }
    }

    fn requires_texts(f: &ItemFn) -> Vec<String> {
        clause_texts(f.sig.spec.requires.as_ref().map(|r| &r.exprs))
    }

    fn ensures_texts(f: &ItemFn) -> Vec<String> {
        clause_texts(f.sig.spec.ensures.as_ref().map(|e| &e.exprs))
    }

    const IMPLICATION: &str =
        "builtin::imply(true&&((a)).is_constant()&&((b)).is_constant(),true&&((ret)).is_constant())";

    #[test]
    fn contract_none_synthesizes_no_constantness() {
        let f = transform_one_fn(sample(), ContractMode::None);
        assert!(f.sig.spec.requires.is_none(), "expected no requires clause");
        assert!(f.sig.spec.ensures.is_none(), "expected no ensures clause");
        let all = f.to_token_stream().to_string();
        assert!(!all.contains("is_constant"), "None mode must not mention is_constant: {all}");
        assert!(!all.contains("use_type_invariant"), "None mode must not add type invariants");
    }

    #[test]
    fn contract_preserve_adds_only_the_implication() {
        let f = transform_one_fn(sample(), ContractMode::PreserveConstant);
        assert!(
            f.sig.spec.requires.is_none(),
            "PreserveConstant must not require constant inputs, got {:?}",
            requires_texts(&f)
        );
        assert_eq!(ensures_texts(&f), vec![IMPLICATION.to_string()]);
    }

    #[test]
    fn contract_require_adds_explicit_clauses_and_the_implication() {
        let f = transform_one_fn(sample(), ContractMode::RequireConstant);
        assert_eq!(
            requires_texts(&f),
            vec!["((a)).is_constant()".to_string(), "((b)).is_constant()".to_string()]
        );
        assert_eq!(
            ensures_texts(&f),
            vec!["((ret)).is_constant()".to_string(), IMPLICATION.to_string()]
        );
    }

    #[test]
    fn contract_modes_are_distinct() {
        let none = transform_one_fn(sample(), ContractMode::None);
        let preserve = transform_one_fn(sample(), ContractMode::PreserveConstant);
        let require = transform_one_fn(sample(), ContractMode::RequireConstant);

        // Only RequireConstant states input constantness explicitly.
        assert!(requires_texts(&none).is_empty());
        assert!(requires_texts(&preserve).is_empty());
        assert!(!requires_texts(&require).is_empty());

        // Both PreserveConstant and RequireConstant carry the implication;
        // only RequireConstant also guarantees the output unconditionally.
        assert!(ensures_texts(&none).is_empty());
        assert!(ensures_texts(&preserve).contains(&IMPLICATION.to_string()));
        assert!(ensures_texts(&require).contains(&IMPLICATION.to_string()));
        assert!(!ensures_texts(&preserve).contains(&"((ret)).is_constant()".to_string()));
        assert!(ensures_texts(&require).contains(&"((ret)).is_constant()".to_string()));
    }

    #[test]
    fn existing_clauses_are_extended_not_replaced() {
        let input = quote! {
            pub fn add(a: u64, b: u64) -> (ret: u64)
                requires a.is_constant()
                ensures ret.is_constant()
            {
                a + b
            }
        };
        let f = transform_one_fn(input, ContractMode::RequireConstant);
        assert_eq!(
            requires_texts(&f),
            vec![
                "a.is_constant()".to_string(),
                "((a)).is_constant()".to_string(),
                "((b)).is_constant()".to_string(),
            ]
        );
        assert_eq!(
            ensures_texts(&f),
            vec![
                "ret.is_constant()".to_string(),
                "((ret)).is_constant()".to_string(),
                IMPLICATION.to_string(),
            ]
        );
    }

    #[test]
    fn executable_types_and_operators_are_secured() {
        let f = transform_one_fn(sample(), ContractMode::None);
        let text = f.to_token_stream().to_string().replace(' ', "");
        assert!(text.contains("a:u64_s"), "parameter type not secured: {text}");
        assert!(text.contains("b:u64_s"), "parameter type not secured: {text}");
        assert!(text.contains("ret:u64_s"), "return type not secured: {text}");
        assert!(text.contains("(a).add(b)"), "executable `+` not secured: {text}");
    }

    #[test]
    fn ghost_code_uses_spec_traits() {
        let input = quote! {
            pub spec fn f(a: u64, b: u64) -> bool {
                a + b == 3
            }
        };
        let f = transform_one_fn(input, ContractMode::PreserveConstant);
        let text = f.to_token_stream().to_string().replace(' ', "");
        assert!(text.contains("spec_add"), "ghost `+` not lowered to spec_add: {text}");
        assert!(text.contains("spec_eq"), "ghost `==` not lowered to spec_eq: {text}");
        // Ghost functions get no synthesized constantness contract.
        assert!(f.sig.spec.requires.is_none());
        assert!(f.sig.spec.ensures.is_none());
        // Ghost parameter types stay primitive.
        assert!(!text.contains("u64_s"), "ghost types must not be secured: {text}");
    }

    #[test]
    fn type_invariants_are_exposed_in_executable_bodies() {
        let f = transform_one_fn(sample(), ContractMode::PreserveConstant);
        let text = f.block.to_token_stream().to_string().replace(' ', "");
        assert!(text.contains("use_type_invariant(&((a)))"), "missing type invariant: {text}");
        assert!(text.contains("use_type_invariant(&((b)))"), "missing type invariant: {text}");
    }

    #[test]
    fn external_code_is_left_alone() {
        let input = quote! {
            #[verifier(external_body)]
            pub fn raw(a: u64) -> (ret: u64) {
                a + 1
            }
        };
        let f = transform_one_fn(input, ContractMode::RequireConstant);
        let text = f.to_token_stream().to_string().replace(' ', "");
        assert!(f.sig.spec.requires.is_none(), "external fn must not get contracts");
        assert!(f.sig.spec.ensures.is_none(), "external fn must not get contracts");
        assert!(!text.contains("u64_s"), "external types must stay primitive: {text}");
    }

    #[test]
    fn bit_vector_assertions_reject_promoting_arithmetic() {
        let input = quote! {
            pub proof fn f(a: u64, b: u64) {
                assert(a + b == b + a) by (bit_vector);
            }
        };
        let f = transform_one_fn(input, ContractMode::PreserveConstant);
        let text = f.to_token_stream().to_string();
        assert!(!text.contains("spec_add"), "bit-vector `+` must not be promoted: {text}");
        assert!(
            text.contains("Inside bit-vector assertion"),
            "bit-vector `+` must be diagnosed: {text}"
        );
    }

    #[test]
    fn executable_structs_get_project_derives() {
        let input = quote! {
            pub struct S {
                pub a: u64,
            }
        };
        let out = transform_items(input, ContractMode::PreserveConstant).unwrap();
        let text = out.to_string().replace(' ', "");
        assert!(
            text.contains(
                "derive(ExecStruct,NotPrimitive,VTypeCastSec,SpecSize,SpecOffset,WellFormed,IsConstant)"
            ),
            "missing project derives: {text}"
        );
        assert!(text.contains("a:u64_s"), "struct field type not secured: {text}");
    }

    #[test]
    fn executable_arrays_become_project_arrays() {
        let input = quote! {
            pub fn f(a: [u64; 4]) {
            }
        };
        let f = transform_one_fn(input, ContractMode::None);
        let text = f.to_token_stream().to_string().replace(' ', "");
        assert!(text.contains("Array<u64_s,4>"), "array not projected: {text}");
    }

    #[test]
    fn triggers_get_the_same_replacements_as_bodies() {
        let input = quote! {
            pub proof fn f(s: Seq<int>)
                ensures forall|i: int| #![trigger s[i]] s[i] == s[i]
            {
            }
        };
        let f = transform_one_fn(input, ContractMode::PreserveConstant);
        let text = f.to_token_stream().to_string().replace(' ', "");
        assert!(
            text.contains("#![triggers.spec_index(i)]"),
            "trigger not rewritten like the body: {text}"
        );
    }
}
