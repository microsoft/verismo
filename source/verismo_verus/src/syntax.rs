use std::iter::FromIterator;

use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{quote, quote_spanned, ToTokens};
use syn_verus::parse::{Parse, ParseStream};
use syn_verus::punctuated::Punctuated;
use syn_verus::spanned::Spanned;
use syn_verus::token::{Brace, Bracket, Paren, Semi};
use syn_verus::visit_mut::{
    visit_block_mut, visit_expr_loop_mut, visit_expr_mut, visit_expr_while_mut, visit_field_mut,
    visit_impl_item_method_mut, visit_item_const_mut, visit_item_enum_mut, visit_item_fn_mut,
    visit_item_struct_mut, visit_local_mut, visit_trait_item_method_mut, VisitMut,
};
use syn_verus::{
    braced, bracketed, parenthesized, parse_macro_input, token, AttrStyle, Attribute, BinOp, Block,
    DataMode, Decreases, Ensures, Expr, ExprBinary, ExprCall, ExprLit, ExprLoop, ExprTuple,
    ExprUnary, ExprWhile, Field, FnArgKind, FnMode, Generics, Ident, ImplItem, ImplItemMethod,
    Invariant, InvariantEnsures, Item, ItemConst, ItemEnum, ItemFn, ItemImpl, ItemMod, ItemStruct,
    ItemTrait, Lit, LitInt, Local, Pat, Path, PathArguments, PathSegment, Publish, Recommends,
    Requires, ReturnType, Signature, Specification, Stmt, Token, TraitItem, TraitItemMethod, Type,
    TypeArray, UnOp, Visibility,
};

use crate::rustdoc::env_rustdoc;

const VERUS_SPEC: &str = "VERUS_SPEC__";

fn take_expr(expr: &mut Expr) -> Expr {
    let dummy: Expr = Expr::Verbatim(TokenStream::new());
    std::mem::replace(expr, dummy)
}

fn take_type(expr: &mut Type) -> Type {
    let dummy: Type = Type::Verbatim(TokenStream::new());
    std::mem::replace(expr, dummy)
}

fn take_pat(pat: &mut Pat) -> Pat {
    let dummy: Pat = Pat::Verbatim(TokenStream::new());
    std::mem::replace(pat, dummy)
}

fn take_ghost<T: Default>(erase_ghost: bool, dest: &mut T) -> T {
    if erase_ghost {
        *dest = T::default();
        T::default()
    } else {
        std::mem::take(dest)
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
    erase_ghost: bool,
    // TODO: this should always be true
    use_spec_traits: bool,
    // inside_ghost > 0 means we're currently visiting ghost code
    inside_ghost: u32,
    // inside_type > 0 means we're currently visiting a type
    inside_type: u32,
    // Widen means we're a direct subexpression in an arithmetic expression that will widen the result.
    // (e.g. "x" or "3" in x + 3 or in x < (3), but not in f(x) + g(3)).
    // When we see a constant in inside_arith, we preemptively give it type "int" rather than
    // asking Rust to infer an integer type, since the inference would usually fail.
    // We also use Widen inside "... as typ".
    // It is inherited through parentheses, if/else, match, and blocks.
    // Fixed is used for bitwise operations, where we use Rust's native integer literals
    // rather than an int literal.
    inside_arith: InsideArith,
    // assign_to == true means we're an expression being assigned to by Assign
    assign_to: bool,

    // Add extra verus signature information to the docstring
    rustdoc: bool,

    // if we are inside bit-vector assertion, warn users to use add/sub/mul for fixed-width operators,
    // rather than +/-/*, which will be promoted to integer operators
    inside_bitvector: bool,
    inside_external: bool,
    for_non_secret: bool,
    update_conditions: bool,
}

// For exec "let pat = init" declarations, recursively find Tracked(x), Ghost(x), x in pat
struct ExecGhostPatVisitor {
    inside_ghost: u32,
    tracked: Option<Token![tracked]>,
    ghost: Option<Token![ghost]>,
    x_decls: Vec<Stmt>,
    x_assigns: Vec<Stmt>,
}

fn data_mode_attrs(mode: &DataMode) -> Vec<Attribute> {
    match mode {
        DataMode::Default => vec![],
        DataMode::Ghost(token) => {
            vec![mk_verus_attr(token.ghost_token.span, quote! { spec })]
        }
        DataMode::Tracked(token) => {
            vec![mk_verus_attr(token.tracked_token.span, quote! { proof })]
        }
        DataMode::Exec(token) => {
            vec![mk_verus_attr(token.exec_token.span, quote! { exec })]
        }
    }
}

fn path_is_ident(path: &Path, s: &str) -> bool {
    let segments = &path.segments;
    segments.len() == 1 && segments.first().unwrap().ident.to_string() == s
}

macro_rules! stmt_with_semi {
    ($span:expr => $($tok:tt)*) => {
        Stmt::Semi(
            Expr::Verbatim(quote_spanned!{ $span => $($tok)* }),
            Semi { spans: [ $span ] },
        )
    };
}

macro_rules! quote_verbatim {
    ($span:expr, $attrs:tt => $($tok:tt)*) => {
        Expr::Verbatim(quote_spanned!{ $span => #(#$attrs)* $($tok)* })
    }
}

impl Visitor {
    fn take_ghost<T: Default>(&self, dest: &mut T) -> T {
        take_ghost(self.erase_ghost, dest)
    }

    fn maybe_erase_expr(&self, span: Span, e: Expr) -> Expr {
        if self.erase_ghost {
            Expr::Verbatim(quote_spanned!(span => {}))
        } else {
            e
        }
    }

    fn visit_fn(
        &mut self,
        attrs: &mut Vec<Attribute>,
        _vis: Option<&Visibility>,
        sig: &mut Signature,
        _semi_token: Option<Token![;]>,
        _is_trait: bool,
    ) -> Vec<Stmt> {
        let stmts: Vec<Stmt> = Vec::new();
        let _unwrap_ghost_tracked: Vec<Stmt> = Vec::new();
        let _call_external_fn = attr_is_call_external(attrs);
        let is_exe = is_exe(&sig);
        if !self.inside_external && is_exe {
            let mut varlist = vec![];
            for arg in &sig.inputs {
                let input = &arg.kind;
                match input {
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
                        match &ret_opt {
                            None => {}
                            Some(box (_, pat, _)) => {
                                param_list(pat, &ty, false, &mut varlist, &sig.generics, false);
                            }
                        }
                    }
                    sig.output = ReturnType::Type(tk, tracked, ret_opt, tmp);
                }
            }
            if self.update_conditions {
                let mut pres = Punctuated::new();
                let mut posts = Punctuated::new();
                let mut constant_pre = quote! {true};
                let mut constant_post = quote! {true};
                for (pre, post) in &varlist {
                    if let Some(var) = pre {
                        constant_pre = quote! {
                        #constant_pre && #var.is_constant()};
                        if self.for_non_secret {
                            pres.push(Expr::Verbatim(quote! {#var.is_constant()}));
                        }
                        pres.push(Expr::Verbatim(quote! {#var.wf()}));
                    }

                    if let Some(var) = post {
                        constant_post = quote! {
                        #constant_post && #var.is_constant()};
                        if self.for_non_secret {
                            posts.push(Expr::Verbatim(quote! {#var.is_constant()}));
                        }
                        posts.push(Expr::Verbatim(quote! {#var.wf()}));
                    }
                }

                posts.push(Expr::Verbatim(
                    quote! {builtin::imply(#constant_pre, #constant_post)},
                ));

                //println!("self.inside_ghost = {}", self.inside_ghost);
                match &sig.requires {
                    Some(_requires) => {
                        sig.requires.as_mut().unwrap().exprs.exprs.extend(pres);
                    }
                    None => {
                        let _exprs: Punctuated<Expr, token::Comma> = Punctuated::new();
                        let r = Requires {
                            exprs: Specification { exprs: pres },
                            token: syn_verus::token::Requires {
                                span: sig.requires.span(),
                            },
                        };
                        sig.requires = Some(r);
                    }
                }

                match &sig.ensures {
                    Some(_ensures) => {
                        sig.ensures.as_mut().unwrap().exprs.exprs.extend(posts);
                    }
                    None => {
                        let e = Ensures {
                            exprs: Specification { exprs: posts },
                            token: syn_verus::token::Ensures {
                                span: sig.requires.span(),
                            },
                            attrs: vec![],
                        };
                        sig.ensures = Some(e);
                    }
                }
            }
        }
        /*self.inside_ghost += 1;
        if let Some(requires) = &mut sig.requires {
            for expr in &mut requires.exprs.exprs {
                //println!("requires self.inside_ghost = {}", self.inside_ghost);
                self.visit_expr_mut(expr);
            }
        }

        if let Some(ensures) = &mut sig.ensures {
            for expr in &mut ensures.exprs.exprs {
                //println!("ensures self.inside_ghost = {}", self.inside_ghost);
                self.visit_expr_mut(expr);
            }
        }
        self.inside_ghost -= 1;
        //println!("end self.inside_ghost = {}", self.inside_ghost);
        */
        self.inside_bitvector = false;
        stmts
    }

    fn visit_const(
        &mut self,
        span: proc_macro2::Span,
        attrs: &mut Vec<Attribute>,
        vis: Option<&Visibility>,
        publish: &mut Publish,
        mode: &mut FnMode,
    ) {
        attrs.push(mk_verus_attr(span, quote! { verus_macro }));

        let publish_attrs = match (vis, &publish) {
            (Some(Visibility::Inherited), _) => vec![],
            (_, Publish::Default) => vec![mk_verus_attr(span, quote! { publish })],
            (_, Publish::Closed(_)) => vec![],
            (_, Publish::Open(o)) => vec![mk_verus_attr(o.token.span, quote! { publish })],
            (_, Publish::OpenRestricted(_)) => {
                unimplemented!("TODO: support open(...)")
            }
        };

        let (inside_ghost, mode_attrs): (u32, Vec<Attribute>) = match &mode {
            FnMode::Default => (0, vec![]),
            FnMode::Spec(token) => (
                1,
                vec![mk_verus_attr(token.spec_token.span, quote! { spec })],
            ),
            FnMode::SpecChecked(token) => (
                1,
                vec![mk_verus_attr(
                    token.spec_token.span,
                    quote_spanned! { token.spec_token.span => spec(checked) },
                )],
            ),
            FnMode::Proof(token) => (
                1,
                vec![mk_verus_attr(token.proof_token.span, quote! { proof })],
            ),
            FnMode::Exec(token) => (
                0,
                vec![mk_verus_attr(token.exec_token.span, quote! { exec })],
            ),
        };
        self.inside_ghost = inside_ghost;
        *publish = Publish::Default;
        *mode = FnMode::Default;
        attrs.extend(publish_attrs);
        attrs.extend(mode_attrs);
    }
}

impl VisitMut for ExecGhostPatVisitor {
    // Recursive traverse pat, finding all Tracked(x), Ghost(x), and, for ghost/tracked, x.
    fn visit_pat_mut(&mut self, pat: &mut Pat) {
        // Replace
        //   pat[Tracked(x), Ghost(y), z]
        // with (for mode != exec and inside_ghost != 0):
        //   pat[tmp_x, tmp_y, z]
        //   x_decls: let tracked x = tmp_x.get(); let ghost y = tmp_y.view();
        //   x_assigns: []
        // with (for mode = exec):
        //   pat[tmp_x, tmp_y, z]
        //   x_decls: let tracked x; let ghost mut y;
        //   x_assigns: x = tmp_x.get(); y = tmp_y.view();
        // with (for mode != exec and inside_ghost == 0):
        //   pat[tmp_x, tmp_y, tmp_z]
        //   x_decls: let tracked x; let ghost mut y; let [mode] mut z;
        //   x_assigns: x = tmp_x.get(); y = tmp_y.view(); z = tmp_z;
        /*use syn_verus::parse_quote_spanned;
        let mk_ident_tmp = |x: &Ident| {
            Ident::new(
                &("verus_tmp_".to_string() + &x.to_string()),
                Span::mixed_site(),
            )
        };
        match pat {
            Pat::TupleStruct(pts)
                if pts.pat.elems.len() == 1
                    && (path_is_ident(&pts.path, "Tracked")
                        || path_is_ident(&pts.path, "Ghost")) =>
            {
                if let Pat::Ident(id) = &mut pts.pat.elems[0] {
                    if id.by_ref.is_some() || id.subpat.is_some() {
                        return;
                    }
                    let tmp_x = mk_ident_tmp(&id.ident);
                    let mut x = id.clone();
                    x.mutability = None;
                    let span = id.span();
                    let decl = if path_is_ident(&pts.path, "Tracked") {
                        if self.inside_ghost == 0 {
                            parse_quote_spanned!(span => #[verus::internal(proof)] let mut #x;)
                        } else if id.mutability.is_some() {
                            parse_quote_spanned!(span => #[verus::internal(proof)] let mut #x = #tmp_x.get();)
                        } else {
                            parse_quote_spanned!(span => #[verus::internal(proof)] let #x = #tmp_x.get();)
                        }
                    } else {
                        if self.inside_ghost == 0 {
                            parse_quote_spanned!(span => #[verus::internal(spec)] let mut #x;)
                        } else if id.mutability.is_some() {
                            parse_quote_spanned!(span => #[verus::internal(spec)] let mut #x = #tmp_x.view();)
                        } else {
                            parse_quote_spanned!(span => #[verus::internal(spec)] let #x = #tmp_x.view();)
                        }
                    };
                    self.x_decls.push(decl);
                    if self.inside_ghost == 0 {
                        let assign = if path_is_ident(&pts.path, "Tracked") {
                            quote_spanned!(span => #x = #tmp_x.get())
                        } else {
                            quote_spanned!(span => #x = #tmp_x.view())
                        };
                        let assign = Stmt::Semi(Expr::Verbatim(assign), Semi { spans: [span] });
                        self.x_assigns.push(assign);
                    }
                    *pat = parse_quote_spanned!(span => #tmp_x);
                    return;
                }
            }
            Pat::Struct(pat_struct) => {
                // When syn parses a struct pattern like `Foo { x }`,
                // it results in an AST similar to `Foo { x: x }`,
                // that is, with a separate node for the field and the expression.
                // The only difference is that one of the nodes has a 'colon' token
                // and one doesn't.
                // Since the transformation we're doing here might change
                // `x: x` to `x: verus_tmp_x`, we can't output it using the shorthand.
                // So we need to add the colon token in.
                for field_pat in pat_struct.fields.iter_mut() {
                    if field_pat.colon_token.is_none() {
                        let span = field_pat.member.span();
                        field_pat.colon_token = Some(token::Colon { spans: [span] });
                    }
                }
            }
            Pat::Ident(id)
                if (self.tracked.is_some() || self.ghost.is_some()) && self.inside_ghost == 0 =>
            {
                if id.by_ref.is_some() || id.subpat.is_some() {
                    return;
                }
                let tmp_x = mk_ident_tmp(&id.ident);
                let mut x = id.clone();
                x.mutability = None;
                let span = id.span();
                let decl = if self.ghost.is_some() {
                    parse_quote_spanned!(span => #[verus::internal(spec)] let mut #x;)
                } else if id.mutability.is_some() {
                    parse_quote_spanned!(span => #[verus::internal(proof)] let mut #x;)
                } else {
                    parse_quote_spanned!(span => #[verus::internal(proof)] let #x;)
                };
                let assign = quote_spanned!(span => #x = #tmp_x);
                id.ident = tmp_x;
                self.x_decls.push(decl);
                self.x_assigns
                    .push(Stmt::Semi(Expr::Verbatim(assign), Semi { spans: [span] }));
                return;
            }
            _ => {}
        }*/
        syn_verus::visit_mut::visit_pat_mut(self, pat);
    }
}

impl Visitor {
    fn visit_local_extend(&mut self, local: &mut Local) -> (bool, Vec<Stmt>) {
        if self.erase_ghost && (local.tracked.is_some() || local.ghost.is_some()) {
            return (false, vec![]);
        }
        if local.init.is_none() {
            return (false, vec![]);
        }

        // Replace
        //   let [mode] pat[Tracked(x), Ghost(y), z] = init;
        // with (for mode != exec and inside_ghost != 0):
        //   let pat[tmp_x, tmp_y, z] = init;
        //   let x = tmp_x.get();
        //   let y = tmp_y.view();
        // with (for mode = exec):
        //   let pat[tmp_x, tmp_y, z] = init;
        //   let tracked x;
        //   let ghost mut y;
        //   proof {
        //       x = tmp_x.get();
        //       y = tmp_y.view();
        //   }
        // with (for mode != exec and inside_ghost == 0):
        //   let [mode] mut tmp;
        //   proof { tmp = init; } // save init in tmp to guard against name conflicts with x, y, z
        //   let tracked x;
        //   let ghost mut y;
        //   let [mode] mut z;
        //   proof {
        //       let pat[tmp_x, tmp_y, tmp_z] = tmp;
        //       x = tmp_x.get();
        //       y = tmp_y.view();
        //       z = tmp_z;
        //   }

        let stmts: Vec<Stmt> = Vec::new();
        if local.tracked.is_some() || local.ghost.is_some() {
            self.inside_ghost += 1;
        }
        let mut visit_pat = ExecGhostPatVisitor {
            inside_ghost: self.inside_ghost,
            tracked: local.tracked.clone(),
            ghost: local.ghost.clone(),
            x_decls: Vec::new(),
            x_assigns: Vec::new(),
        };

        visit_pat.visit_pat_mut(&mut local.pat);
        if local.tracked.is_some() || local.ghost.is_some() {
            self.inside_ghost -= 1;
        }
        if visit_pat.x_decls.len() == 0 && local.tracked.is_none() && local.ghost.is_none() {
            assert!(visit_pat.x_assigns.len() == 0);
            return (false, vec![]);
        }
        if self.erase_ghost {
            return (false, vec![]);
        }

        let _span = local.span();
        // Make proof block that will be subsequently visited with inside_ghost > 0
        /*let mk_proof_block = |block: Block| {
            let expr_block = syn_verus::ExprBlock { attrs: vec![], label: None, block };
            let op = UnOp::Proof(token::Proof { span });
            Expr::Unary(ExprUnary { attrs: vec![], expr: Box::new(Expr::Block(expr_block)), op })
        };*/

        if self.inside_ghost != 0 {
            assert!(visit_pat.x_assigns.len() == 0);
            //stmts.extend(visit_pat.x_decls);
            (false, stmts)
        } else if local.tracked.is_none() && local.ghost.is_none() {
            /*stmts.extend(visit_pat.x_decls);
            let block = Block { brace_token: Brace(span), stmts: visit_pat.x_assigns };
            stmts.push(Stmt::Semi(mk_proof_block(block), Semi { spans: [span] }));
            */
            (false, stmts)
        } else {
            /*use syn_verus::parse_quote_spanned;
            let tmp = Ident::new("verus_tmp", Span::mixed_site().located_at(local.span()));
            let tmp_decl = if local.tracked.is_some() {
                parse_quote_spanned!(span => #[verus::internal(proof)] #[verus::internal(unwrapped_binding)] let #tmp;)
            } else {
                parse_quote_spanned!(span => #[verus::internal(spec)] #[verus::internal(unwrapped_binding)] let mut #tmp;)
            };
            stmts.push(tmp_decl);
            let pat = take_pat(&mut local.pat);
            let init = take_expr(&mut local.init.as_mut().expect("init").1);
            let block1 = parse_quote_spanned!(span => { #tmp = #init });
            stmts.push(Stmt::Semi(mk_proof_block(block1), Semi { spans: [span] }));
            stmts.extend(visit_pat.x_decls);
            let let_pat = if local.tracked.is_some() {
                parse_quote_spanned!(span => #[verus::internal(proof)] let #pat = #tmp;)
            } else {
                parse_quote_spanned!(span => #[verus::internal(spec)] let #pat = #tmp;)
            };
            let mut block_stmts = vec![let_pat];
            block_stmts.extend(visit_pat.x_assigns);
            let block2 = Block { brace_token: Brace(span), stmts: block_stmts };
            stmts.push(Stmt::Semi(mk_proof_block(block2), Semi { spans: [span] }));
            */
            (false, stmts)
        }
    }

    fn visit_stmt_extend(&mut self, stmt: &mut Stmt) -> (bool, Vec<Stmt>) {
        match stmt {
            Stmt::Local(local) => self.visit_local_extend(local),
            _ => (false, vec![]),
        }
    }

    fn visit_stream_expr(&mut self, stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
        use quote::ToTokens;
        let mut expr: Expr = parse_macro_input!(stream as Expr);
        let mut new_stream = TokenStream::new();
        self.visit_expr_mut(&mut expr);
        expr.to_tokens(&mut new_stream);
        proc_macro::TokenStream::from(new_stream)
    }

    fn visit_items_prefilter(&mut self, items: &mut Vec<Item>) {
        let erase_ghost = self.erase_ghost;
        // We'd like to erase ghost items, but there may be dangling references to the ghost items:
        // - "use" declarations may refer to the items ("use m::f;" makes it hard to erase f)
        // - "impl" may refer to struct and enum items ("impl<A> S<A> { ... }" impedes erasing S)
        // Therefore, we leave arbitrary named stubs in the place of the erased ghost items:
        // - For erased pub spec or proof Fn item x, keep decl, replace body with panic!()
        // - For erased pub Const item x, keep as-is (REVIEW: it's not clear what expressions we can support)
        // - For erased non-pub Fn and Const item x, leave "use bool as x;"
        // - Leave Struct and Enum as-is (REVIEW: we could leave stubs with PhantomData fields)
        for item in items.iter_mut() {
            let span = item.span();
            match item {
                Item::Fn(fun) => match (&fun.vis, &fun.sig.mode) {
                    (
                        Visibility::Public(_),
                        FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_),
                    ) if erase_ghost => {
                        // replace body with panic!()
                        let expr: Expr = Expr::Verbatim(quote_spanned! {
                            span => { panic!() }
                        });
                        let stmt = Stmt::Expr(expr);
                        fun.block.stmts = vec![stmt];
                        fun.semi_token = None;
                        continue;
                    }
                    _ => {}
                },
                _ => {}
            }
            let erase_fn = match item {
                Item::Fn(fun) => match fun.sig.mode {
                    FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_) if erase_ghost => {
                        Some((fun.sig.ident.clone(), fun.vis.clone()))
                    }
                    _ => None,
                },
                Item::Const(c) => match (&c.vis, &c.mode) {
                    (Visibility::Public(_), _) => None,
                    (_, FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_))
                        if erase_ghost =>
                    {
                        Some((c.ident.clone(), c.vis.clone()))
                    }
                    _ => None,
                },
                /*
                Item::Struct(s) => match s.mode {
                    DataMode::Ghost(_) | DataMode::Tracked(_) if erase_ghost => {
                        ...
                    }
                    _ => None,
                },
                Item::Enum(e) => match e.mode {
                    DataMode::Ghost(_) | DataMode::Tracked(_) if erase_ghost => {
                        ...
                    }
                    _ => None,
                },
                */
                _ => None,
            };
            if let Some((name, vis)) = erase_fn {
                *item = Item::Verbatim(quote_spanned! {
                    span => #[allow(unused_imports)] #vis use bool as #name;
                });
            }
        }
    }

    fn visit_impl_items_prefilter(&mut self, items: &mut Vec<ImplItem>, for_trait: bool) {
        let erase_ghost = self.erase_ghost;
        // Unfortunately, we just have to assume that if for_trait == true,
        // the methods might be public
        items.retain(|item| match item {
            ImplItem::Method(fun) => match ((&fun.vis, for_trait), &fun.sig.mode) {
                (
                    (Visibility::Public(_), _) | (_, true),
                    FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_),
                ) => true,
                (_, FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_)) => !erase_ghost,
                (_, FnMode::Exec(_) | FnMode::Default) => true,
            },
            ImplItem::Const(c) => match (&c.vis, &c.mode) {
                (Visibility::Public(_), _) => true,
                (_, FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_)) => !erase_ghost,
                (_, FnMode::Exec(_) | FnMode::Default) => true,
            },
            _ => true,
        });
        for item in items.iter_mut() {
            let span = item.span();
            match item {
                ImplItem::Method(fun) => match ((&fun.vis, for_trait), &fun.sig.mode) {
                    (
                        (Visibility::Public(_), _) | (_, true),
                        FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_),
                    ) if erase_ghost => {
                        // replace body with panic!()
                        let expr: Expr = Expr::Verbatim(quote_spanned! {
                            span => { panic!() }
                        });
                        let stmt = Stmt::Expr(expr);
                        fun.block.stmts = vec![stmt];
                        fun.semi_token = None;
                        continue;
                    }
                    _ => {}
                },
                _ => {}
            }
        }
    }

    fn visit_trait_items_prefilter(&mut self, items: &mut Vec<TraitItem>) {
        // In addition to prefiltering ghost code, we also split methods declarations
        // into separate spec and implementation declarations.  For example:
        //   fn f() requires x;
        // becomes
        //   fn VERUS_SPEC__f() requires x;
        //   fn f();
        // In a later pass, this becomes:
        //   fn VERUS_SPEC__f() { requires(x); ... }
        //   fn f();
        // Note: we don't do this if there's a default body (although default bodies
        // aren't supported yet anyway), because it turns out that the parameter names
        // don't exactly match between fun and fun.clone() (they have different macro contexts),
        // which would cause the body and specs to mismatch.
        let erase_ghost = self.erase_ghost;
        let mut spec_items: Vec<TraitItem> = Vec::new();
        for item in items.iter_mut() {
            match item {
                TraitItem::Method(ref mut fun) => match fun.sig.mode {
                    FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_) if erase_ghost => {
                        fun.default = None;
                        continue;
                    }
                    _ if !erase_ghost && fun.default.is_none() => {
                        // Copy into separate spec method, then remove spec from original method
                        let mut spec_fun = fun.clone();
                        let x = &fun.sig.ident;
                        let span = x.span();
                        spec_fun.sig.ident = Ident::new(&format!("{VERUS_SPEC}{x}"), span);
                        spec_fun
                            .attrs
                            .push(mk_rust_attr(span, "doc", quote! { hidden }));
                        fun.sig.erase_spec_fields();
                        spec_items.push(TraitItem::Method(spec_fun));
                    }
                    _ => {}
                },
                _ => {}
            }
        }
        items.append(&mut spec_items);
    }
}

fn chain_count(expr: &Expr) -> u32 {
    if let Expr::Binary(binary) = expr {
        match binary.op {
            BinOp::Le(_) | BinOp::Lt(_) | BinOp::Ge(_) | BinOp::Gt(_) | BinOp::Eq(_) => {
                1 + chain_count(&binary.left)
            }
            _ => 0,
        }
    } else {
        0
    }
}

const ILLEGAL_CALLEES: &[&str] = &["forall", "exists", "choose"];

impl Visitor {
    /// Turn `forall|x| ...`
    /// into `::builtin::forall(|x| ...)`
    /// and similarly for `exists` and `choose`
    ///
    /// Also handle trigger attributes.
    ///
    /// Returns true if the transform is attempted, false if the transform is inapplicable.

    fn closure_quant_operators(&mut self, expr: &mut Expr) -> bool {
        let unary = match expr {
            Expr::Unary(
                u @ ExprUnary {
                    op: UnOp::Forall(..),
                    ..
                },
            ) => u,
            Expr::Unary(
                u @ ExprUnary {
                    op: UnOp::Exists(..),
                    ..
                },
            ) => u,
            Expr::Unary(
                u @ ExprUnary {
                    op: UnOp::Choose(..),
                    ..
                },
            ) => u,
            Expr::Call(ExprCall {
                attrs: _,
                func,
                paren_token: _,
                args: _,
            }) => {
                if let Expr::Path(syn_verus::ExprPath {
                    path,
                    qself: None,
                    attrs: _,
                }) = &**func
                {
                    if path.segments.len() == 1
                        && ILLEGAL_CALLEES.contains(&path.segments[0].ident.to_string().as_str())
                    {
                        let err = format!(
                            "forall, choose, and exists do not allow parentheses, use `{}|<vars>| expr` instead",
                            path.segments[0].ident.to_string()
                        );
                        *expr = Expr::Verbatim(quote_spanned!(expr.span() => compile_error!(#err)));
                        return true;
                    }
                }
                return false;
            }
            _ => {
                return false;
            }
        };

        // Recursively visit the closure expression, but *don't* call our
        // custom visitor fn on the closure node itself.
        visit_expr_mut(self, &mut unary.expr);

        let span = unary.span();

        let attrs = std::mem::take(&mut unary.attrs);

        let arg = &mut *unary.expr;
        let (inner_attrs, n_inputs) = match &mut *arg {
            Expr::Closure(closure) => {
                if closure.requires.is_some() || closure.ensures.is_some() {
                    let err = "quantifiers cannot have requires/ensures";
                    *expr = Expr::Verbatim(quote_spanned!(span => compile_error!(#err)));
                    return true;
                }
                (
                    std::mem::take(&mut closure.inner_attrs),
                    closure.inputs.len(),
                )
            }
            _ => panic!("expected closure for quantifier"),
        };

        match extract_quant_triggers(inner_attrs, span) {
            Ok(ExtractQuantTriggersFound::Auto) => match &mut *arg {
                Expr::Closure(closure) => {
                    let body = take_expr(&mut closure.body);
                    closure.body = Box::new(Expr::Verbatim(
                        quote_spanned!(span => #[verus::internal(auto_trigger)] (#body)),
                    ));
                }
                _ => panic!("expected closure for quantifier"),
            },
            Ok(ExtractQuantTriggersFound::Triggers(tuple)) => match &mut *arg {
                Expr::Closure(closure) => {
                    let body = take_expr(&mut closure.body);
                    closure.body = Box::new(Expr::Verbatim(
                        quote_spanned!(span => ::builtin::with_triggers(#tuple, #body)),
                    ));
                }
                _ => panic!("expected closure for quantifier"),
            },
            Ok(ExtractQuantTriggersFound::None) => {}
            Err(err_expr) => {
                *expr = err_expr;
                return true;
            }
        }

        match unary.op {
            UnOp::Forall(..) => {
                *expr = quote_verbatim!(span, attrs => ::builtin::forall(#arg));
            }
            UnOp::Exists(..) => {
                *expr = quote_verbatim!(span, attrs => ::builtin::exists(#arg));
            }
            UnOp::Choose(..) => {
                if n_inputs == 1 {
                    *expr = quote_verbatim!(span, attrs => ::builtin::choose(#arg));
                } else {
                    *expr = quote_verbatim!(span, attrs => ::builtin::choose_tuple(#arg));
                }
            }
            _ => panic!("unary= {}", quote! {unary}),
        }

        true
    }

    fn add_loop_specs(
        &mut self,
        stmts: &mut Vec<Stmt>,
        invariants: Option<Invariant>,
        invariant_ensures: Option<InvariantEnsures>,
        ensures: Option<Ensures>,
        decreases: Option<Decreases>,
    ) {
        // TODO: wrap specs inside ghost blocks
        self.inside_ghost += 1;
        if let Some(Invariant { token, mut exprs }) = invariants {
            if exprs.exprs.len() > 0 {
                for expr in exprs.exprs.iter_mut() {
                    self.visit_expr_mut(expr);
                }
                stmts.push(stmt_with_semi!(token.span => ::builtin::invariant([#exprs])));
            }
        }
        if let Some(InvariantEnsures { token, mut exprs }) = invariant_ensures {
            if exprs.exprs.len() > 0 {
                for expr in exprs.exprs.iter_mut() {
                    self.visit_expr_mut(expr);
                }
                stmts.push(stmt_with_semi!(token.span => ::builtin::invariant_ensures([#exprs])));
            }
        }
        if let Some(Ensures {
            attrs: _,
            token: _,
            mut exprs,
        }) = ensures
        {
            if exprs.exprs.len() > 0 {
                for expr in exprs.exprs.iter_mut() {
                    self.visit_expr_mut(expr);
                }
                //stmts.push(stmt_with_semi!(token.span => ::builtin::ensures([#exprs])));
            }
        }
        if let Some(Decreases { token, mut exprs }) = decreases {
            for expr in exprs.exprs.iter_mut() {
                self.visit_expr_mut(expr);
                if matches!(expr, Expr::Tuple(..)) {
                    let err = "decreases cannot be a tuple; use `decreases x, y` rather than `decreases (x, y)`";
                    let expr = Expr::Verbatim(quote_spanned!(token.span => compile_error!(#err)));
                    stmts.push(Stmt::Semi(
                        expr,
                        Semi {
                            spans: [token.span],
                        },
                    ));
                }
            }
            stmts.push(stmt_with_semi!(token.span => ::builtin::decreases((#exprs))));
        }
        //println!("end add_loop_spec inside_ghost = {}", self.inside_ghost);
        self.inside_ghost -= 1;
    }
}

enum ExtractQuantTriggersFound {
    Auto,
    Triggers(ExprTuple),
    None,
}

fn extract_quant_triggers(
    inner_attrs: Vec<Attribute>,
    span: Span,
) -> Result<ExtractQuantTriggersFound, Expr> {
    let mut triggers: Vec<Expr> = Vec::new();
    for attr in inner_attrs {
        let trigger: syn_verus::Result<syn_verus::Specification> =
            syn_verus::parse2(attr.tokens.clone());
        let path_segments_str = attr
            .path
            .segments
            .iter()
            .map(|x| x.ident.to_string())
            .collect::<Vec<_>>();
        let ident_str = match &path_segments_str[..] {
            [attr_name] => Some(attr_name),
            _ => None,
        };
        match (trigger, ident_str) {
            (Ok(trigger), Some(id)) if id == &"auto" && trigger.exprs.len() == 0 => {
                return Ok(ExtractQuantTriggersFound::Auto);
            }
            (Ok(trigger), Some(id)) if id == &"trigger" => {
                let tuple = ExprTuple {
                    attrs: vec![],
                    paren_token: Paren(span),
                    elems: trigger.exprs,
                };
                triggers.push(Expr::Tuple(tuple));
            }
            (Err(err), _) => {
                let span = attr.span();
                let err = err.to_string();

                return Err(Expr::Verbatim(quote_spanned!(span => compile_error!(#err))));
            }
            _ => {
                let span = attr.span();
                return Err(Expr::Verbatim(
                    quote_spanned!(span => compile_error!("expected trigger")),
                ));
            }
        }
    }

    Ok(if triggers.len() > 0 {
        let mut elems = Punctuated::new();
        for elem in triggers {
            elems.push(elem);
            elems.push_punct(Token![,](span));
        }
        ExtractQuantTriggersFound::Triggers(ExprTuple {
            attrs: vec![],
            paren_token: Paren(span),
            elems,
        })
    } else {
        ExtractQuantTriggersFound::None
    })
}

impl VisitMut for Visitor {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        //println!("expr = {}, inside_ghot = {}", quote!{#expr}, self.inside_ghost);
        let is_inside_bitvector = match &expr {
            Expr::Assert(a) => match &a.prover {
                Some((_, id)) => {
                    if id.to_string() == "bit_vector" {
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

        let is_auto_proof_block = if self.inside_ghost == 0 {
            match &expr {
                Expr::Assume(a) => Some(a.assume_token.span),
                Expr::Assert(a) => Some(a.assert_token.span),
                Expr::AssertForall(a) => Some(a.assert_token.span),
                _ => None,
            }
        } else {
            None
        };
        if let Some(_) = is_auto_proof_block {
            self.inside_ghost += 1;
        }

        let mode_block = match expr {
            Expr::Unary(ExprUnary {
                op: UnOp::Proof(..),
                ..
            }) => Some((false, false)),
            Expr::Call(ExprCall {
                func: box Expr::Path(path),
                args,
                ..
            }) if path.qself.is_none() && args.len() == 1 => {
                if path_is_ident(&path.path, "Ghost") {
                    Some((true, false))
                } else if path_is_ident(&path.path, "Tracked") {
                    Some((true, true))
                } else {
                    None
                }
            }
            _ => None,
        };

        let sub_inside_arith = match expr {
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
        let sub_assign_to = match expr {
            Expr::Field(..) => self.assign_to,
            _ => false,
        };

        // Recursively call visit_expr_mut
        let is_inside_ghost = self.inside_ghost > 0;
        let is_inside_arith = self.inside_arith;
        let is_assign_to = self.assign_to;
        let use_spec_traits = self.use_spec_traits && is_inside_ghost;
        if mode_block.is_some() {
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
        if !(is_inside_ghost && self.erase_ghost) {
            visit_expr_mut(self, expr);
        }
        if let Expr::Assign(assign) = expr {
            assign.left = Box::new(assign_left.expect("assign_left"));
        }
        if mode_block.is_some() {
            //println!("mode_block.is_some() inside_ghost -1 = {}", self.inside_ghost);
            self.inside_ghost -= 1;
        }
        self.inside_arith = is_inside_arith;
        self.assign_to = is_assign_to;
        let do_replace = match &expr {
            Expr::Lit(ExprLit {
                lit: Lit::Int(..), ..
            }) => true,
            Expr::Cast(..) => true,
            Expr::Index(..) if !self.inside_external => true,
            Expr::Unary(ExprUnary {
                op: UnOp::Neg(..), ..
            }) => true,
            Expr::Unary(ExprUnary {
                op: UnOp::Not(..), ..
            }) => true,
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
            Expr::Assume(..) | Expr::Assert(..) | Expr::AssertForall(..) => true,
            Expr::View(..) => true,
            Expr::Closure(..) => true,
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
                Expr::Lit(ExprLit {
                    lit: Lit::Int(lit),
                    attrs,
                }) => {
                    ////println!("expr = {}", lit);
                    let span = lit.span();
                    let n = lit.base10_digits().to_string();
                    if lit.suffix() == "" {
                        match is_inside_arith {
                            InsideArith::None => {
                                // We don't know which integer type to use,
                                // so defer the decision to type inference.
                                // *expr = quote_verbatim!(span, attrs => ::builtin::spec_literal_integer(#n));
                                *expr = if !use_sec_type {
                                    quote_verbatim!(span, attrs => ::builtin::spec_literal_integer(#n))
                                } else {
                                    let lit = Expr::Lit(ExprLit {
                                        lit: Lit::Int(lit),
                                        attrs: vec![],
                                    });
                                    quote_verbatim! {span, attrs => #sec_const(#lit) }
                                };
                            }
                            InsideArith::Widen if n.starts_with("-") => {
                                // Use int inside +, -, etc., since these promote to int anyway
                                //*expr =
                                //    quote_verbatim!(span, attrs => ::builtin::spec_literal_int(#n));
                                *expr = if !use_sec_type {
                                    quote_verbatim! {span, attrs => (::builtin::spec_literal_int(#n)) }
                                } else {
                                    let lit = Expr::Lit(ExprLit {
                                        lit: Lit::Int(lit),
                                        attrs: vec![],
                                    });
                                    quote_verbatim! {span, attrs => #sec_const(#lit) }
                                };
                            }
                            InsideArith::Widen => {
                                // Use int inside +, -, etc., since these promote to int anyway
                                *expr = if !use_sec_type {
                                    quote_verbatim! {span, attrs => (::builtin::spec_literal_nat(#n)) }
                                } else {
                                    let lit = Expr::Lit(ExprLit {
                                        lit: Lit::Int(lit),
                                        attrs: vec![],
                                    });
                                    quote_verbatim! {span, attrs => #sec_const(#lit) }
                                };
                            }
                            InsideArith::Fixed => {
                                // We generally won't want int/nat literals for bitwise ops,
                                // so use Rust's native integer literals
                                let newexpr = Expr::Lit(ExprLit {
                                    lit: Lit::Int(lit),
                                    attrs: vec![],
                                });
                                *expr = if !use_sec_type {
                                    quote_verbatim! {span, attrs => (#newexpr) }
                                } else {
                                    quote_verbatim! {span, attrs => #sec_const(#newexpr) }
                                };
                            }
                        }
                    } else if lit.suffix() == "int" {
                        // *expr = quote_verbatim!(span, attrs => ::builtin::spec_literal_int(#n));
                        *expr = if use_spec_traits {
                            quote_verbatim! {span, attrs => (::builtin::spec_literal_int(#n)) }
                        } else {
                            panic!("No int in exe")
                        };
                    } else if lit.suffix() == "nat" {
                        //*expr = quote_verbatim!(span, attrs => ::builtin::spec_literal_nat(#n));
                        *expr = quote_verbatim! {span, attrs => (::builtin::spec_literal_nat(#n))};
                    } else if lit.suffix().ends_with("_s") {
                        let tmp = Expr::Lit(ExprLit {
                            lit: Lit::Int(LitInt::new(
                                &lit.to_string().as_str().replace("_s", ""),
                                lit.span(),
                            )),
                            attrs: vec![],
                        });
                        let ident = Ident::new(lit.suffix(), lit.span());

                        *expr = quote_verbatim! {span, attrs => #ident::#const_fn(#tmp)};
                    } else if lit.suffix().ends_with("_t") {
                        let tmp = Expr::Lit(ExprLit {
                            lit: Lit::Int(LitInt::new(
                                &lit.to_string().as_str().replace("_t", ""),
                                lit.span(),
                            )),
                            attrs: vec![],
                        });
                        let _ident = Ident::new(lit.suffix(), lit.span());

                        *expr = quote_verbatim! {span, attrs => #tmp};
                    } else {
                        // Has a native Rust integer suffix, so leave it as a secure literal
                        *expr = if !use_sec_type {
                            let tmp = Expr::Lit(ExprLit {
                                lit: Lit::Int(lit),
                                attrs: vec![],
                            });
                            quote_verbatim! {span, attrs => (#tmp) }
                        } else {
                            let ident =
                                Ident::new(format!("{}_s", lit.suffix()).as_str(), lit.span());
                            let tmp = Expr::Lit(ExprLit {
                                lit: Lit::Int(lit),
                                attrs: vec![],
                            });
                            quote_verbatim! {span, attrs => #ident::#const_fn(#tmp) }
                        };
                    }
                    ////println!("expr = {:?}", expr);
                }
                Expr::Cast(cast) => {
                    let span = cast.span();
                    let src = &cast.expr;
                    let attrs: Vec<Attribute> = cast.attrs.clone();
                    let mut ty = cast.ty.clone();
                    *expr = if self.inside_ghost > 0 {
                        quote_verbatim!(span, attrs => VTypeCast::<#ty>::vspec_cast_to(#src))
                    } else if !self.inside_external {
                        self.replace_stype(&mut ty, true);
                        quote_verbatim!(span, attrs => core::convert::Into::<#ty>::into(#src))
                    } else {
                        Expr::Cast(cast)
                    };
                }
                Expr::Index(idx) => {
                    let span = idx.span();
                    let src = idx.expr;
                    let attrs = idx.attrs;
                    let index = idx.index;
                    if use_spec_traits && is_inside_ghost {
                        *expr = quote_verbatim!(span, attrs => #src.spec_index(#index));
                    } else if replace_exe_op {
                        *expr = quote_verbatim!(span, attrs => #src.index(#index));
                    }
                }
                Expr::Unary(unary) => {
                    let span = unary.span();
                    let attrs = unary.attrs;
                    match unary.op {
                        UnOp::Neg(_neg) => {
                            let arg = unary.expr;
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => (#arg).spec_neg());
                            } else if replace_exe_op {
                                *expr = quote_verbatim!(span, attrs => (#arg).neg());
                            }
                        }
                        UnOp::Not(_neg) => {
                            let arg = unary.expr;
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
                    let left = b.left;
                    let right = b.right;
                    match b.op {
                        BinOp::Eq(..) => {
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => (#left).spec_eq(#right));
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => (#left).eq(&#right));
                            }
                        }
                        BinOp::Ne(..) => {
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => !((#left).spec_eq(#right)));
                            } else if !is_inside_ghost {
                                *expr = Expr::Verbatim(quote! {!((#left).eq(&#right))});
                            }
                        }
                        BinOp::Le(..) => {
                            let left = quote_spanned! { left.span() => (#left) };
                            if use_spec_traits {
                                *expr = Expr::Binary(binary);
                            } else if !is_inside_ghost {
                                //println!("{:?}", self);
                                *expr = quote_verbatim!(span, attrs => #left.le(&#right));
                            }
                        }
                        BinOp::Lt(..) => {
                            let left = quote_spanned! { left.span() => (#left) };
                            if use_spec_traits {
                                *expr = Expr::Binary(binary);
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.lt(&#right));
                            }
                        }
                        BinOp::Ge(..) => {
                            let left = quote_spanned! { left.span() => (#left) };
                            if use_spec_traits {
                                *expr = Expr::Binary(binary);
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.ge(&#right));
                            }
                        }
                        BinOp::Gt(..) => {
                            let left = quote_spanned! { left.span() => (#left) };
                            if use_spec_traits {
                                *expr = Expr::Binary(binary);
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.gt(&#right));
                            }
                        }
                        BinOp::Add(..) if !self.inside_bitvector => {
                            let left = quote_spanned! { left.span() => (#left) };
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_add(#right));
                            } else if replace_exe_op {
                                *expr = quote_verbatim!(span, attrs => #left.add(#right));
                            }
                        }
                        BinOp::Sub(..) if !self.inside_bitvector => {
                            let left = quote_spanned! { left.span() => (#left) };
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_sub(#right));
                            } else if replace_exe_op {
                                *expr = quote_verbatim!(span, attrs => #left.sub(#right));
                            }
                        }
                        BinOp::Mul(..) if !self.inside_bitvector => {
                            let left = quote_spanned! { left.span() => (#left) };
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
                            let left = quote_spanned! { left.span() => (#left) };
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_euclidean_div(#right));
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.div(#right));
                            }
                        }
                        BinOp::Rem(..) => {
                            let left = quote_spanned! { left.span() => (#left) };
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_euclidean_mod(#right));
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.rem(#right));
                            };
                        }
                        BinOp::BitAnd(..) => {
                            let left = quote_spanned! { left.span() => (#left) };
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_bitand(#right));
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.bitand(#right));
                            }
                        }
                        BinOp::BitOr(..) => {
                            let left = quote_spanned! { left.span() => (#left) };
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_bitor(#right));
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.bitor(#right));
                            }
                        }
                        BinOp::BitXor(..) => {
                            let left = quote_spanned! { left.span() => (#left) };
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_bitxor(#right));
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.bitxor(#right));
                            }
                        }
                        BinOp::Shl(..) => {
                            let left = quote_spanned! { left.span() => (#left) };
                            if use_spec_traits {
                                *expr = quote_verbatim!(span, attrs => #left.spec_shl(#right));
                            } else if !is_inside_ghost {
                                *expr = quote_verbatim!(span, attrs => #left.shl(#right));
                            }
                        }
                        BinOp::Shr(..) => {
                            let left = quote_spanned! { left.span() => (#left) };
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
        if let Some(_) = is_auto_proof_block {
            self.inside_ghost -= 1;
        }
    }

    fn visit_attribute_mut(&mut self, attr: &mut Attribute) {
        if let syn_verus::AttrStyle::Outer = attr.style {
            match &attr
                .path
                .segments
                .iter()
                .map(|x| &x.ident)
                .collect::<Vec<_>>()[..]
            {
                [attr_name] if attr_name.to_string() == "trigger" => {
                    *attr = mk_verus_attr(attr.span(), quote! { trigger });
                }
                [attr_name] if attr_name.to_string() == "via_fn" => {
                    *attr = mk_verus_attr(attr.span(), quote! { via });
                }
                [attr_name] if attr_name.to_string() == "verifier" => {
                    let parsed = attr.parse_meta().expect("failed to parse attribute");
                    match parsed {
                        syn_verus::Meta::List(meta_list) if meta_list.nested.len() == 1 => {
                            let span = attr.span();
                            let (second_segment, nested) = match &meta_list.nested[0] {
                                syn_verus::NestedMeta::Meta(syn_verus::Meta::List(meta_list)) => {
                                    let rest = &meta_list.nested[0];
                                    (&meta_list.path.segments[0], Some(quote! { (#rest) }))
                                }
                                syn_verus::NestedMeta::Meta(syn_verus::Meta::Path(meta_path)) => {
                                    (&meta_path.segments[0], None)
                                }
                                _ => {
                                    panic!("invalid verifier attribute (1)"); // TODO(main_new) use compile_error! if possible
                                }
                            };
                            let mut path_segments = Punctuated::new();
                            path_segments.push(PathSegment {
                                ident: Ident::new("verifier", span),
                                arguments: PathArguments::None,
                            });
                            path_segments.push(second_segment.clone());
                            *attr = Attribute {
                                pound_token: token::Pound { spans: [span] },
                                style: AttrStyle::Outer,
                                bracket_token: token::Bracket { span },
                                path: Path {
                                    leading_colon: None,
                                    segments: path_segments,
                                },
                                tokens: if let Some(nested) = nested {
                                    quote! { #nested }
                                } else {
                                    quote! {}
                                },
                            };
                        }
                        _ => panic!("invalid verifier attribute (2)"), // TODO(main_new) use compile_error! if possible
                    }
                }
                _ => (),
            }
        }

        if let syn_verus::AttrStyle::Inner(_) = attr.style {
            match &attr
                .path
                .segments
                .iter()
                .map(|x| &x.ident)
                .collect::<Vec<_>>()[..]
            {
                [attr_name] if attr_name.to_string() == "trigger" => {
                    // process something like: #![trigger f(a, b), g(c, d)]
                    // attr.tokens is f(a, b), g(c, d)
                    // turn this into a tuple (f(a, b), g(c, d)),
                    // parse it into an Expr, visit the Expr, turn the Expr back into tokens,
                    // remove the ( and ).
                    let old_stream = proc_macro::TokenStream::from(attr.tokens.clone());
                    let mut tuple_stream = proc_macro::TokenStream::new();
                    let group =
                        proc_macro::Group::new(proc_macro::Delimiter::Parenthesis, old_stream);
                    tuple_stream.extend(vec![proc_macro::TokenTree::Group(group)]);
                    let mut new_tuples = self.visit_stream_expr(tuple_stream).into_iter();
                    let new_tuple = new_tuples.next().expect("visited tuple");
                    assert!(new_tuples.next().is_none());
                    if let proc_macro::TokenTree::Group(group) = new_tuple {
                        assert!(group.delimiter() == proc_macro::Delimiter::Parenthesis);
                        attr.tokens = proc_macro2::TokenStream::from(group.stream());
                    } else {
                        panic!("expected tuple");
                    }
                }
                _ => (),
            }
        }
    }

    fn visit_expr_while_mut(&mut self, expr_while: &mut ExprWhile) {
        //let invariants = self.take_ghost(&mut expr_while.invariant);
        //let invariant_ensures = self.take_ghost(&mut expr_while.invariant_ensures);
        //let ensures = self.take_ghost(&mut expr_while.ensures);
        //let decreases = self.take_ghost(&mut expr_while.decreases);
        let stmts: Vec<Stmt> = Vec::new();
        if expr_while.invariant.is_some() {
            self.visit_invariant_mut(expr_while.invariant.as_mut().unwrap());
        }
        if expr_while.invariant_ensures.is_some() {
            self.visit_invariant_ensures_mut(&mut expr_while.invariant_ensures.as_mut().unwrap());
        }
        if expr_while.ensures.is_some() {
            self.visit_ensures_mut(&mut expr_while.ensures.as_mut().unwrap());
        }
        expr_while.body.stmts.splice(0..0, stmts);
        visit_expr_while_mut(self, expr_while);
    }

    fn visit_expr_loop_mut(&mut self, expr_loop: &mut ExprLoop) {
        //let invariants = self.take_ghost(&mut expr_loop.invariant);
        //let invariant_ensures = self.take_ghost(&mut expr_loop.invariant_ensures);
        //let ensures = self.take_ghost(&mut expr_loop.ensures);
        //let decreases = self.take_ghost(&mut expr_loop.decreases);
        let stmts: Vec<Stmt> = Vec::new();
        /*self.add_loop_specs(
            &mut stmts,
            invariants,
            invariant_ensures,
            ensures,
            decreases,
        );*/
        expr_loop.body.stmts.splice(0..0, stmts);
        visit_expr_loop_mut(self, expr_loop);
    }

    fn visit_local_mut(&mut self, local: &mut Local) {
        // Note: exec-mode "let ghost" and "let tracked" have already been transformed
        // into proof blocks by point, so we don't need to change inside_ghost here.
        let is_ghost = local.tracked.is_some() || local.ghost.is_some();
        if is_ghost {
            self.inside_ghost += 1;
        }
        visit_local_mut(self, local);
        if is_ghost {
            self.inside_ghost -= 1;
        }
    }

    fn visit_block_mut(&mut self, block: &mut Block) {
        /*let mut stmts: Vec<Stmt> = Vec::new();
        let block_stmts = std::mem::replace(&mut block.stmts, vec![]);
        for mut stmt in block_stmts {
            let (skip, extra_stmts) = self.visit_stmt_extend(&mut stmt);
            if !skip {
                stmts.push(stmt);
            }
            stmts.extend(extra_stmts);
        }
        block.stmts = stmts;*/
        visit_block_mut(self, block);
    }

    fn visit_requires_mut(&mut self, i: &mut Requires) {
        self.inside_ghost += 1;
        syn_verus::visit_mut::visit_requires_mut(self, i);
        self.inside_ghost -= 1;
    }

    fn visit_ensures_mut(&mut self, i: &mut Ensures) {
        self.inside_ghost += 1;
        syn_verus::visit_mut::visit_ensures_mut(self, i);
        self.inside_ghost -= 1;
    }

    fn visit_decreases_mut(&mut self, i: &mut Decreases) {
        self.inside_ghost += 1;
        syn_verus::visit_mut::visit_decreases_mut(self, i);
        self.inside_ghost -= 1;
    }

    fn visit_recommends_mut(&mut self, i: &mut Recommends) {
        self.inside_ghost += 1;
        syn_verus::visit_mut::visit_recommends_mut(self, i);
        self.inside_ghost -= 1;
    }

    fn visit_invariant_mut(&mut self, i: &mut Invariant) {
        self.inside_ghost += 1;
        syn_verus::visit_mut::visit_invariant_mut(self, i);
        self.inside_ghost -= 1;
    }

    fn visit_invariant_ensures_mut(&mut self, i: &mut InvariantEnsures) {
        self.inside_ghost += 1;
        syn_verus::visit_mut::visit_invariant_ensures_mut(self, i);
        self.inside_ghost -= 1;
    }

    fn visit_item_fn_mut(&mut self, fun: &mut ItemFn) {
        let is_external = self.inside_external;
        self.inside_external = attr_is_external(&fun.attrs);

        // Process rustdoc before processing the ItemFn itself.
        // That way, the generated rustdoc gets the prettier syntax instead of the
        // de-sugared syntax.
        if self.rustdoc {
            crate::rustdoc::process_item_fn(fun);
        }
        self.inside_ghost = if !is_exe(&fun.sig) { 1 } else { 0 };
        let _stmts = self.visit_fn(
            &mut fun.attrs,
            Some(&fun.vis),
            &mut fun.sig,
            fun.semi_token,
            false,
        );
        fun.semi_token = None;
        visit_item_fn_mut(self, fun);
        self.inside_ghost = 0;
        //println!("visit_item_fn_mut self.inside_ghost = 0");
        self.inside_external = is_external;
    }

    fn visit_impl_item_method_mut(&mut self, method: &mut ImplItemMethod) {
        let is_external = self.inside_external;
        self.inside_external = attr_is_external(&method.attrs);
        self.inside_ghost = if !is_exe(&method.sig) { 1 } else { 0 };
        if self.rustdoc {
            crate::rustdoc::process_impl_item_method(method);
        }

        let stmts = self.visit_fn(
            &mut method.attrs,
            Some(&method.vis),
            &mut method.sig,
            method.semi_token,
            false,
        );
        method.block.stmts.splice(0..0, stmts);
        method.semi_token = None;
        visit_impl_item_method_mut(self, method);
        self.inside_external = is_external;
        self.inside_ghost = 0;
        //println!("visit_impl_item_method_mut self.inside_ghost = 0");
    }

    fn visit_trait_item_method_mut(&mut self, method: &mut TraitItemMethod) {
        if self.rustdoc {
            crate::rustdoc::process_trait_item_method(method);
        }
        self.inside_ghost = if !is_exe(&method.sig) { 1 } else { 0 };
        let _is_spec_method = method.sig.ident.to_string().starts_with(VERUS_SPEC);
        let _stmts = self.visit_fn(
            &mut method.attrs,
            None,
            &mut method.sig,
            method.semi_token,
            true,
        );
        visit_trait_item_method_mut(self, method);
        self.inside_ghost = 0;
        //println!("visit_trait_item_method_mut self.inside_ghost = 0");
    }

    fn visit_item_const_mut(&mut self, con: &mut ItemConst) {
        let is_external = self.inside_external;
        self.inside_external = attr_is_external(&con.attrs);
        /*self.visit_const(
            con.const_token.span,
            &mut con.attrs,
            Some(&con.vis),
            &mut con.publish,
            &mut con.mode,
        );*/
        visit_item_const_mut(self, con);
        self.inside_external = is_external;
    }

    fn visit_field_mut(&mut self, field: &mut Field) {
        visit_field_mut(self, field);
        field.mode = DataMode::Default;
    }

    fn visit_item_enum_mut(&mut self, item: &mut ItemEnum) {
        let is_external = self.inside_external;
        self.inside_external = attr_is_external(&item.attrs);
        visit_item_enum_mut(self, item);
        item.mode = DataMode::Default;
        self.inside_external = is_external;
    }

    fn visit_item_struct_mut(&mut self, item: &mut ItemStruct) {
        let is_external = self.inside_external;
        self.inside_external = attr_is_external(&item.attrs);
        visit_item_struct_mut(self, item);
        item.attrs.extend(data_mode_attrs(&item.mode));
        item.attrs
            .extend(struct_data_mode_attrs(&item.mode, self.inside_external));

        item.mode = DataMode::Default;
        self.inside_external = is_external;
    }

    fn visit_type_mut(&mut self, ty: &mut Type) {
        self.inside_type += 1;
        syn_verus::visit_mut::visit_type_mut(self, ty);
        self.inside_type -= 1;

        let _span = ty.span();
        self.replace_stype(ty, false);
    }

    fn visit_path_mut(&mut self, path: &mut Path) {
        // generic type arguments can appear inside paths
        self.inside_type += 1;
        syn_verus::visit_mut::visit_path_mut(self, path);
        self.inside_type -= 1;
    }

    fn visit_generic_method_argument_mut(&mut self, arg: &mut syn_verus::GenericMethodArgument) {
        self.inside_type += 1;
        syn_verus::visit_mut::visit_generic_method_argument_mut(self, arg);
        self.inside_type -= 1;
    }

    fn visit_item_mod_mut(&mut self, item: &mut ItemMod) {
        let is_external = self.inside_external;
        self.inside_external = attr_is_external(&item.attrs);
        /*if let Some((_, items)) = &mut item.content {
            self.visit_items_prefilter(items);
        }*/
        syn_verus::visit_mut::visit_item_mod_mut(self, item);
        self.inside_external = is_external;
    }

    fn visit_item_impl_mut(&mut self, imp: &mut ItemImpl) {
        let is_external = self.inside_external;
        self.inside_external = attr_is_external(&imp.attrs);
        //self.visit_impl_items_prefilter(&mut imp.items, imp.trait_.is_some());
        syn_verus::visit_mut::visit_item_impl_mut(self, imp);
        self.inside_external = is_external;
    }

    fn visit_item_trait_mut(&mut self, tr: &mut ItemTrait) {
        let is_external = self.inside_external;
        self.inside_external = attr_is_external(&tr.attrs);
        //self.visit_trait_items_prefilter(&mut tr.items);
        syn_verus::visit_mut::visit_item_trait_mut(self, tr);
        self.inside_external = is_external;
    }
}

struct Items {
    items: Vec<Item>,
}

impl Parse for Items {
    fn parse(input: ParseStream) -> syn_verus::parse::Result<Items> {
        let mut items = Vec::new();
        while !input.is_empty() {
            items.push(input.parse()?);
        }
        Ok(Items { items })
    }
}

#[derive(Debug)]
enum MacroElement {
    Comma(Token![,]),
    Semi(Token![;]),
    FatArrow(Token![=>]),
    Expr(Expr),
}

#[derive(Debug)]
enum MacroElementExplicitExpr {
    Comma(Token![,]),
    Semi(Token![;]),
    FatArrow(Token![=>]),
    ExplicitExpr(Token![@], Token![@], Expr),
    TT(TokenTree),
}

#[derive(Debug)]
struct MacroElements {
    elements: Vec<MacroElement>,
}

#[derive(Debug)]
struct MacroElementsExplicitExpr {
    elements: Vec<MacroElementExplicitExpr>,
}

#[derive(Debug)]
enum Delimiter {
    Paren(Paren),
    Bracket(Bracket),
    Brace(Brace),
}

#[derive(Debug)]
struct MacroInvoke {
    path: Path,
    bang: Token![!],
    delimiter: Delimiter,
    elements: MacroElements,
}

#[derive(Debug)]
struct MacroInvokeExplicitExpr {
    path: Path,
    bang: Token![!],
    delimiter: Delimiter,
    elements: MacroElementsExplicitExpr,
}

impl Parse for MacroElement {
    fn parse(input: ParseStream) -> syn_verus::parse::Result<MacroElement> {
        if input.peek(Token![,]) {
            Ok(MacroElement::Comma(input.parse()?))
        } else if input.peek(Token![;]) {
            Ok(MacroElement::Semi(input.parse()?))
        } else if input.peek(Token![=>]) {
            Ok(MacroElement::FatArrow(input.parse()?))
        } else {
            Ok(MacroElement::Expr(input.parse()?))
        }
    }
}

impl Parse for MacroElementExplicitExpr {
    fn parse(input: ParseStream) -> syn_verus::parse::Result<MacroElementExplicitExpr> {
        if input.peek(Token![,]) {
            Ok(MacroElementExplicitExpr::Comma(input.parse()?))
        } else if input.peek(Token![;]) {
            Ok(MacroElementExplicitExpr::Semi(input.parse()?))
        } else if input.peek(Token![=>]) {
            Ok(MacroElementExplicitExpr::FatArrow(input.parse()?))
        } else if input.peek(Token![@]) && input.peek2(Token![@]) {
            let at1 = input.parse()?;
            let at2 = input.parse()?;
            let e = input.parse()?;
            Ok(MacroElementExplicitExpr::ExplicitExpr(at1, at2, e))
        } else {
            Ok(MacroElementExplicitExpr::TT(input.parse()?))
        }
    }
}

impl Parse for MacroElements {
    fn parse(input: ParseStream) -> syn_verus::parse::Result<MacroElements> {
        let mut elements = Vec::new();
        while !input.is_empty() {
            elements.push(input.parse()?);
        }
        Ok(MacroElements { elements })
    }
}

impl Parse for MacroElementsExplicitExpr {
    fn parse(input: ParseStream) -> syn_verus::parse::Result<MacroElementsExplicitExpr> {
        let mut elements = Vec::new();
        while !input.is_empty() {
            elements.push(input.parse()?);
        }
        Ok(MacroElementsExplicitExpr { elements })
    }
}

impl Parse for MacroInvoke {
    fn parse(input: ParseStream) -> syn_verus::parse::Result<MacroInvoke> {
        let path = input.parse()?;
        let bang = input.parse()?;
        let content;
        if input.peek(syn_verus::token::Paren) {
            let paren = parenthesized!(content in input);
            let elements = content.parse()?;
            Ok(MacroInvoke {
                path,
                bang,
                delimiter: Delimiter::Paren(paren),
                elements,
            })
        } else if input.peek(syn_verus::token::Bracket) {
            let bracket = bracketed!(content in input);
            let elements = content.parse()?;
            Ok(MacroInvoke {
                path,
                bang,
                delimiter: Delimiter::Bracket(bracket),
                elements,
            })
        } else {
            let brace = braced!(content in input);
            let elements = content.parse()?;
            Ok(MacroInvoke {
                path,
                bang,
                delimiter: Delimiter::Brace(brace),
                elements,
            })
        }
    }
}

impl Parse for MacroInvokeExplicitExpr {
    fn parse(input: ParseStream) -> syn_verus::parse::Result<MacroInvokeExplicitExpr> {
        let path = input.parse()?;
        let bang = input.parse()?;
        let content;
        if input.peek(syn_verus::token::Paren) {
            let paren = parenthesized!(content in input);
            let elements = content.parse()?;
            Ok(MacroInvokeExplicitExpr {
                path,
                bang,
                delimiter: Delimiter::Paren(paren),
                elements,
            })
        } else if input.peek(syn_verus::token::Bracket) {
            let bracket = bracketed!(content in input);
            let elements = content.parse()?;
            Ok(MacroInvokeExplicitExpr {
                path,
                bang,
                delimiter: Delimiter::Bracket(bracket),
                elements,
            })
        } else {
            let brace = braced!(content in input);
            let elements = content.parse()?;
            Ok(MacroInvokeExplicitExpr {
                path,
                bang,
                delimiter: Delimiter::Brace(brace),
                elements,
            })
        }
    }
}

impl quote::ToTokens for MacroElement {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            MacroElement::Comma(e) => e.to_tokens(tokens),
            MacroElement::Semi(e) => e.to_tokens(tokens),
            MacroElement::FatArrow(e) => e.to_tokens(tokens),
            MacroElement::Expr(e) => e.to_tokens(tokens),
        }
    }
}

impl quote::ToTokens for MacroElementExplicitExpr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            MacroElementExplicitExpr::Comma(e) => e.to_tokens(tokens),
            MacroElementExplicitExpr::Semi(e) => e.to_tokens(tokens),
            MacroElementExplicitExpr::FatArrow(e) => e.to_tokens(tokens),
            MacroElementExplicitExpr::ExplicitExpr(_at1, _at2, e) => e.to_tokens(tokens),
            MacroElementExplicitExpr::TT(e) => e.to_tokens(tokens),
        }
    }
}

impl quote::ToTokens for MacroElements {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for element in &self.elements {
            element.to_tokens(tokens);
        }
    }
}

impl quote::ToTokens for MacroElementsExplicitExpr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for element in &self.elements {
            element.to_tokens(tokens);
        }
    }
}

impl quote::ToTokens for MacroInvoke {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.path.to_tokens(tokens);
        self.bang.to_tokens(tokens);
        match self.delimiter {
            Delimiter::Paren(d) => {
                d.surround(tokens, |tokens| {
                    self.elements.to_tokens(tokens);
                });
            }
            Delimiter::Bracket(d) => {
                d.surround(tokens, |tokens| {
                    self.elements.to_tokens(tokens);
                });
            }
            Delimiter::Brace(d) => {
                d.surround(tokens, |tokens| {
                    self.elements.to_tokens(tokens);
                });
            }
        }
    }
}

impl quote::ToTokens for MacroInvokeExplicitExpr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.path.to_tokens(tokens);
        self.bang.to_tokens(tokens);
        match self.delimiter {
            Delimiter::Paren(d) => {
                d.surround(tokens, |tokens| {
                    self.elements.to_tokens(tokens);
                });
            }
            Delimiter::Bracket(d) => {
                d.surround(tokens, |tokens| {
                    self.elements.to_tokens(tokens);
                });
            }
            Delimiter::Brace(d) => {
                d.surround(tokens, |tokens| {
                    self.elements.to_tokens(tokens);
                });
            }
        }
    }
}

pub(crate) fn rewrite_items(
    stream: proc_macro::TokenStream,
    erase_ghost: bool,
    use_spec_traits: bool,
    for_non_secret: bool,
    update_conditions: bool,
) -> proc_macro::TokenStream {
    use quote::ToTokens;
    let stream = rejoin_tokens(stream);
    let items: Items = parse_macro_input!(stream as Items);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits,
        inside_ghost: 0,
        inside_type: 0,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
        inside_bitvector: false,
        inside_external: false,
        for_non_secret,
        update_conditions,
    };
    for mut item in items.items {
        visitor.visit_item_mut(&mut item);
        visitor.inside_ghost = 0;
        //println!("new_item = {}", quote! {#item});
        //println!("rewrite_items self.inside_ghost = 0");
        visitor.inside_arith = InsideArith::None;
        item.to_tokens(&mut new_stream);
    }
    //println!("new_stream = {}", new_stream);
    proc_macro::TokenStream::from(quote! {verus!{#new_stream}})
}

pub(crate) fn rewrite_expr(
    erase_ghost: bool,
    inside_ghost: bool,
    stream: proc_macro::TokenStream,
    for_non_secret: bool,
) -> proc_macro::TokenStream {
    use quote::ToTokens;
    let stream = rejoin_tokens(stream);
    let mut expr: Expr = parse_macro_input!(stream as Expr);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        inside_ghost: if inside_ghost { 1 } else { 0 },
        inside_type: 0,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
        inside_bitvector: false,
        inside_external: false,
        for_non_secret,
        update_conditions: true,
    };
    visitor.visit_expr_mut(&mut expr);
    expr.to_tokens(&mut new_stream);
    proc_macro::TokenStream::from(new_stream)
}

pub(crate) fn rewrite_expr_node(
    erase_ghost: bool,
    inside_ghost: bool,
    expr: &mut Expr,
    for_non_secret: bool,
) {
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        inside_ghost: if inside_ghost { 1 } else { 0 },
        inside_type: 0,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
        inside_bitvector: false,
        inside_external: false,
        for_non_secret,
        update_conditions: true,
    };
    visitor.visit_expr_mut(expr);
}

// Unfortunately, the macro_rules tt tokenizer breaks tokens like &&& and ==> into smaller tokens.
// Try to put the original tokens back together here.
fn rejoin_tokens(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    use proc_macro::Spacing::*;
    use proc_macro::{Group, Punct, Span, TokenTree};
    let mut tokens: Vec<TokenTree> = stream.into_iter().collect();
    let pun = |t: &TokenTree| match t {
        TokenTree::Punct(p) => Some((p.as_char(), p.spacing(), p.span())),
        _ => None,
    };
    let adjacent = |s1: Span, s2: Span| {
        let l1 = s1.end();
        let l2 = s2.start();
        s1.source_file() == s2.source_file() && l1.eq(&l2)
    };
    for i in 0..(if tokens.len() >= 2 {
        tokens.len() - 2
    } else {
        0
    }) {
        let t0 = pun(&tokens[i]);
        let t1 = pun(&tokens[i + 1]);
        let t2 = pun(&tokens[i + 2]);
        let t3 = if i + 3 < tokens.len() {
            pun(&tokens[i + 3])
        } else {
            None
        };
        match (t0, t1, t2, t3) {
            (
                Some(('<', Joint, _)),
                Some(('=', Alone, s1)),
                Some(('=', Joint, s2)),
                Some(('>', Alone, _)),
            )
            | (Some(('=', Joint, _)), Some(('=', Alone, s1)), Some(('=', Alone, s2)), _)
            | (Some(('!', Joint, _)), Some(('=', Alone, s1)), Some(('=', Alone, s2)), _)
            | (Some(('=', Joint, _)), Some(('=', Alone, s1)), Some(('>', Alone, s2)), _)
            | (Some(('<', Joint, _)), Some(('=', Alone, s1)), Some(('=', Alone, s2)), _)
            | (Some(('&', Joint, _)), Some(('&', Alone, s1)), Some(('&', Alone, s2)), _)
            | (Some(('|', Joint, _)), Some(('|', Alone, s1)), Some(('|', Alone, s2)), _) => {
                if adjacent(s1, s2) {
                    let (op, _, span) = t1.unwrap();
                    let mut punct = Punct::new(op, Joint);
                    punct.set_span(span);
                    tokens[i + 1] = TokenTree::Punct(punct);
                }
            }
            _ => {}
        }
    }
    for tt in &mut tokens {
        match tt {
            TokenTree::Group(group) => {
                let mut new_group = Group::new(group.delimiter(), rejoin_tokens(group.stream()));
                new_group.set_span(group.span());
                *group = new_group;
            }
            _ => {}
        }
    }
    proc_macro::TokenStream::from_iter(tokens.into_iter())
}

pub(crate) fn proof_macro_exprs(
    erase_ghost: bool,
    inside_ghost: bool,
    stream: proc_macro::TokenStream,
    for_non_secret: bool,
) -> proc_macro::TokenStream {
    use quote::ToTokens;
    let stream = rejoin_tokens(stream);
    let mut invoke: MacroInvoke = parse_macro_input!(stream as MacroInvoke);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        inside_ghost: if inside_ghost { 1 } else { 0 },
        inside_type: 0,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
        inside_bitvector: false,
        inside_external: false,
        for_non_secret,
        update_conditions: true,
    };
    for element in &mut invoke.elements.elements {
        match element {
            MacroElement::Expr(expr) => visitor.visit_expr_mut(expr),
            _ => {}
        }
    }
    invoke.to_tokens(&mut new_stream);
    proc_macro::TokenStream::from(new_stream)
}

pub(crate) fn inv_macro_exprs(
    erase_ghost: bool,
    stream: proc_macro::TokenStream,
    for_non_secret: bool,
) -> proc_macro::TokenStream {
    use quote::ToTokens;
    let stream = rejoin_tokens(stream);
    let mut invoke: MacroInvoke = parse_macro_input!(stream as MacroInvoke);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        inside_ghost: 1,
        inside_type: 0,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
        inside_bitvector: false,
        inside_external: false,
        for_non_secret,
        update_conditions: true,
    };
    for element in &mut invoke.elements.elements {
        match element {
            MacroElement::Expr(expr) => visitor.visit_expr_mut(expr),
            _ => {}
        }
        // After the first element, parse as 'exec' expression
        visitor.inside_ghost = 0;
    }
    invoke.to_tokens(&mut new_stream);
    proc_macro::TokenStream::from(new_stream)
}

pub(crate) fn proof_macro_explicit_exprs(
    erase_ghost: bool,
    inside_ghost: bool,
    stream: proc_macro::TokenStream,
    for_non_secret: bool,
) -> proc_macro::TokenStream {
    use quote::ToTokens;
    let stream = rejoin_tokens(stream);
    let mut invoke: MacroInvokeExplicitExpr = parse_macro_input!(stream as MacroInvokeExplicitExpr);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        inside_ghost: if inside_ghost { 1 } else { 0 },
        inside_type: 0,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
        inside_bitvector: false,
        inside_external: false,
        for_non_secret,
        update_conditions: true,
    };
    for element in &mut invoke.elements.elements {
        match element {
            MacroElementExplicitExpr::ExplicitExpr(_at1, _at2, expr) => {
                visitor.visit_expr_mut(expr)
            }
            _ => {}
        }
    }
    invoke.to_tokens(&mut new_stream);
    proc_macro::TokenStream::from(new_stream)
}

/// Constructs #[name(tokens)]
fn mk_rust_attr(span: Span, name: &str, tokens: TokenStream) -> Attribute {
    let mut path_segments = Punctuated::new();
    path_segments.push(PathSegment {
        ident: Ident::new(name, span),
        arguments: PathArguments::None,
    });
    Attribute {
        pound_token: token::Pound { spans: [span] },
        style: AttrStyle::Outer,
        bracket_token: token::Bracket { span },
        path: Path {
            leading_colon: None,
            segments: path_segments,
        },
        tokens: quote! { (#tokens) },
    }
}

/// Constructs #[verus::internal(tokens)]
fn mk_verus_attr(span: Span, tokens: TokenStream) -> Attribute {
    let mut path_segments = Punctuated::new();
    path_segments.push(PathSegment {
        ident: Ident::new("verus", span),
        arguments: PathArguments::None,
    });
    path_segments.push(PathSegment {
        ident: Ident::new("internal", span),
        arguments: PathArguments::None,
    });
    Attribute {
        pound_token: token::Pound { spans: [span] },
        style: AttrStyle::Outer,
        bracket_token: token::Bracket { span },
        path: Path {
            leading_colon: None,
            segments: path_segments,
        },
        tokens: quote! { (#tokens) },
    }
}

fn struct_data_mode_attrs(mode: &DataMode, inside_external: bool) -> Vec<Attribute> {
    let tk = if inside_external {
        quote! { ExecStruct, NotPrimitive }
    } else {
        quote! { ExecStruct, NotPrimitive, VTypeCastSec, SpecSize, SpecOffset, WellFormed, IsConstant }
    };
    let ret = vec![mk_rust_attr(mode.span(), "derive", tk)];
    match mode {
        DataMode::Default => ret,
        DataMode::Exec(_token) => ret,
        _ => {
            vec![]
        }
    }
}

fn attr_is_external(attrs: &Vec<Attribute>) -> bool {
    for a in attrs {
        if a.tokens.to_string() == "(external_body)"
            || a.tokens.to_string() == "(external)"
            || a.tokens.to_string() == "(external_fn_specification)"
        {
            return true;
        }
    }
    false
}

fn attr_is_call_external(attrs: &Vec<Attribute>) -> bool {
    for a in attrs {
        if a.tokens.to_string() == "(external_fn_specification)" {
            //println!("external_fn_specification");
            return true;
        }
    }
    false
}

impl Visitor {
    fn replace_stype(&self, ty: &mut Type, must_replace: bool) {
        let span = ty.span();

        match ty {
            Type::Array(TypeArray {
                bracket_token: _,
                elem,
                semi_token: _,
                len,
            }) => {
                if !self.inside_external || must_replace {
                    *ty = Type::Verbatim(quote_spanned! { span =>
                        Array<#elem, #len>
                    });
                } else {
                    *ty = Type::Verbatim(quote_spanned! { span =>
                        [#elem; #len]
                    });
                }
            }
            Type::Path(patht)
                if (!self.inside_external && self.inside_ghost == 0 && !self.inside_bitvector)
                    || must_replace =>
            {
                let tpath = &patht.path;
                if path_is_ident(tpath, "u64") {
                    ////println!("{:?}", self);
                    *ty = Type::Verbatim(quote_spanned! { span =>
                        u64_s
                    });
                } else if path_is_ident(tpath, "u32") {
                    *ty = Type::Verbatim(quote_spanned! { span =>
                        u32_s
                    });
                } else if path_is_ident(tpath, "u16") {
                    *ty = Type::Verbatim(quote_spanned! { span =>
                        u16_s
                    });
                } else if path_is_ident(tpath, "u8") {
                    *ty = Type::Verbatim(quote_spanned! { span =>
                        u8_s
                    });
                } else if path_is_ident(tpath, "usize") {
                    ////println!("{:?}", self);
                    *ty = Type::Verbatim(quote_spanned! { span =>
                        usize_s
                    });
                }
            }
            _ => {}
        }
    }
}

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
    match &ty {
        Type::Array(_) | Type::Path(_) | Type::Slice(_) => {
            if is_ghost_or_tracked_type(&ty) {
                return;
            }
            if is_generic(&ty, generics) {
                return;
            }
            if is_param {
                ret.push((Some(Expr::Verbatim(quote! {(#prefix(#pat))})), None));
            } else {
                ret.push((None, Some(Expr::Verbatim(quote! {(#prefix(#pat))}))));
            }
        }
        Type::BareFn(_) => {}
        Type::Group(_) => todo!(),
        Type::ImplTrait(_) => todo!(),
        Type::Infer(_) => todo!(),
        Type::Macro(_) => todo!(),
        Type::Never(_) => {}
        Type::Paren(_) => todo!(),
        Type::Reference(r) => {
            let ty: &Box<Type> = &r.elem;
            param_list(&pat, &ty, r.mutability.is_some(), ret, generics, is_param);
        }
        Type::TraitObject(_) => todo!(),
        Type::Tuple(tup) => {
            let mut i = 0;
            for ty in &tup.elems {
                let index = LitInt::new(format! {"{}", i}.as_str(), tup.span());
                let p = Pat::Verbatim(quote! {(#prefix(#pat)).#index});
                param_list(&p, &ty, false, ret, generics, is_param);
                i = i + 1;
            }
        }
        Type::Verbatim(_) => {}
        Type::FnSpec(_) => {}
        _ => todo!(),
    }
}

fn is_exe(sig: &Signature) -> bool {
    match sig.mode {
        FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_) => false,
        FnMode::Exec(_) => true,
        FnMode::Default => true,
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

pub fn is_generic(ty: &Type, generics: &Generics) -> bool {
    for generic in &generics.params {
        match generic {
            syn_verus::GenericParam::Type(typaram) => {
                if let Type::Path(tpath) = ty {
                    if let Some(name) = tpath.path.segments.last() {
                        if name.ident.to_string() == typaram.ident.to_string() {
                            return true;
                        }
                    }
                }
            }
            syn_verus::GenericParam::Lifetime(_) => {}
            syn_verus::GenericParam::Const(_) => {}
        }
    }
    return false;
}
