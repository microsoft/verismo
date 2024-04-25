use proc_macro2::TokenStream;
use quote::quote;
use serde_json::json;
use std::fs::OpenOptions;
use std::io::Write;
use std::iter::FromIterator;
use syn_verus::{
    braced, bracketed, parenthesized,
    parse::{Parse, ParseStream},
    parse2,
    spanned::Spanned,
    token::{Brace, Bracket, Paren},
    visit_mut::{
        visit_attribute_mut, visit_block_mut, visit_expr_loop_mut, visit_expr_mut,
        visit_expr_while_mut, visit_field_mut, visit_impl_item_method_mut, visit_item_const_mut,
        visit_item_enum_mut, visit_item_fn_mut, visit_item_struct_mut, visit_local_mut,
        visit_trait_item_method_mut, VisitMut,
    },
    Attribute, Block, DataMode, Expr, ExprLoop, ExprUnary, ExprWhile, Field, FnMode, ImplItem,
    ImplItemMethod, Item, ItemConst, ItemEnum, ItemFn, ItemImpl, ItemMod, ItemStruct, ItemTrait,
    Local, Path, Token, TraitItemMethod, Type, UnOp,
};

pub struct Visitor {
    remove_proof: bool,
    removed_lines: Vec<Vec<Vec<u32>>>,
    codes: Vec<(String, String, String)>,
    proof_count: usize,
    proof_loop_count: usize,
    spec_count: usize,
    trusted_proof: usize,
    trusted_exe: usize,
    ghost_struct_count: usize,
}

impl Visitor {
    pub fn total_ghost(&self) -> usize {
        self.ghost_struct_count
            + self.proof_count
            + self.proof_loop_count
            + self.spec_count
            + self.trusted_proof
            + self.trusted_exe
    }

    pub fn merge(&mut self, other: &Self) {
        self.proof_count += other.proof_count;
        self.proof_loop_count += other.proof_loop_count;
        self.spec_count += other.spec_count;
        self.trusted_proof += other.trusted_proof;
        self.trusted_exe += other.trusted_exe;
        self.ghost_struct_count += other.ghost_struct_count;
    }

    pub fn to_json(&self, show_line: bool, cloc: usize, filepath: &String) -> String {
        let total = self.total_ghost();
        let data = format! {
            "file\t{} proof {}\tghost struct\t{}\t", filepath, self.proof_count, self.ghost_struct_count
        };
        //return data.to_string()+ "\n";
        let data = json!({
            "1file": filepath,
            //"cleancode": input,
            //"2lines": if show_line {self.removed_lines.clone()} else {vec!{}},
            "3proof": self.proof_count,
            "4ghost_struct_count": self.ghost_struct_count,
            "5spec": self.spec_count,
            "6loop_proof": self.proof_loop_count,
            "7trusted_exe": self.trusted_exe,
            "8trusted_proof": self.trusted_proof,
            "9erase": total,
            "9cloc": cloc,
            "end": 0,
        });
        data.to_string() + "\n"
    }
}

fn update_removed_lines<T: Spanned + std::fmt::Debug>(lines: &mut Vec<Vec<Vec<u32>>>, item: T) {
    let span = item.span();
    let start = span.start();
    let end = span.end();
    //println!("{:?}: {:?} - {:?}\n", item, start, end);
    lines.push(vec![
        vec![start.line as u32, start.column as u32],
        vec![end.line as u32, end.column as u32],
    ]);
}

fn update_line_count<T: Spanned + std::fmt::Debug>(lines: &mut usize, item: T) {
    let span = item.span();
    let start = span.start();
    let end = span.end();
    //println!("{:?}: {:?} - {:?}\n", item, start, end);
    *lines = *lines + end.line - start.line + 1;
}

impl VisitMut for Visitor {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        let mode_block = match expr {
            Expr::Unary(ExprUnary {
                op: UnOp::Proof(_), ..
            })
            | Expr::Assert(_)
            | Expr::AssertForall(_) => {
                update_line_count(&mut self.proof_count, &expr);
                update_removed_lines(&mut self.removed_lines, &expr);
                if self.remove_proof {
                    *expr = Expr::Verbatim(quote! {});
                }
            }
            _ => visit_expr_mut(self, expr),
        };
    }

    fn visit_attribute_mut(&mut self, attr: &mut Attribute) {
        visit_attribute_mut(self, attr);
    }

    fn visit_expr_while_mut(&mut self, expr_while: &mut ExprWhile) {
        //println!("====={}", quote!{#expr_while});
        if expr_while.invariant.is_some() {
            update_line_count(&mut self.proof_loop_count, &expr_while.invariant);
            update_removed_lines(&mut self.removed_lines, &expr_while.invariant);
        }
        if expr_while.ensures.is_some() {
            update_line_count(&mut self.proof_loop_count, &expr_while.ensures);
            update_removed_lines(&mut self.removed_lines, &expr_while.ensures);
        }
        if expr_while.decreases.is_some() {
            update_line_count(&mut self.proof_loop_count, &expr_while.decreases);
            update_removed_lines(&mut self.removed_lines, &expr_while.decreases);
        }
        if self.remove_proof {
            expr_while.invariant = None;
            expr_while.ensures = None;
            expr_while.decreases = None;
        }
        visit_expr_while_mut(self, expr_while);
    }

    fn visit_expr_loop_mut(&mut self, expr_while: &mut ExprLoop) {
        if expr_while.invariant.is_some() {
            update_line_count(&mut self.proof_loop_count, &expr_while.invariant);
            update_removed_lines(&mut self.removed_lines, &expr_while.invariant);
        }
        if expr_while.ensures.is_some() {
            update_line_count(&mut self.proof_loop_count, &expr_while.ensures);
            update_removed_lines(&mut self.removed_lines, &expr_while.ensures);
        }
        if expr_while.decreases.is_some() {
            update_line_count(&mut self.proof_loop_count, &expr_while.decreases);
            update_removed_lines(&mut self.removed_lines, &expr_while.decreases);
        }
        if self.remove_proof {
            expr_while.invariant = None;
            expr_while.ensures = None;
            expr_while.decreases = None;
        }
        visit_expr_loop_mut(self, expr_while);
    }

    fn visit_local_mut(&mut self, local: &mut Local) {
        if local.ghost.is_some() || local.tracked.is_some() {
            update_line_count(&mut self.proof_count, &local);
            update_removed_lines(&mut self.removed_lines, &local);
        } else {
            visit_local_mut(self, local);
        }
    }

    fn visit_block_mut(&mut self, block: &mut Block) {
        visit_block_mut(self, block);
    }

    fn visit_item_fn_mut(&mut self, fun: &mut ItemFn) {
        let mut sig = fun.sig.clone();
        let external = attr_is_external(&fun.attrs);

        match sig.mode {
            FnMode::Spec(_) => {
                update_removed_lines(&mut self.removed_lines, &fun);
                update_line_count(&mut self.spec_count, &fun);
            }
            FnMode::Proof(_) => {
                update_removed_lines(&mut self.removed_lines, &fun);
                //update_removed_lines(&mut self.removed_lines, &fun);
                if external {
                    update_line_count(&mut self.trusted_proof, &fun);
                } else {
                    update_line_count(&mut self.proof_count, &fun);
                }

                if self.remove_proof {
                    fun.block.stmts.clear();
                    fun.sig.decreases = Option::None;
                }
            }
            _ => {
                if external {
                    update_removed_lines(&mut self.removed_lines, &fun);
                    update_line_count(&mut self.trusted_exe, &fun);
                } else {
                    if fun.sig.decreases.is_some() {
                        update_removed_lines(&mut self.removed_lines, &fun.sig.decreases);
                        update_line_count(&mut self.proof_count, &fun.sig.decreases);
                    }

                    if fun.sig.requires.is_some() {
                        update_removed_lines(&mut self.removed_lines, &fun.sig.requires);
                        update_line_count(&mut self.proof_count, &fun.sig.requires);
                    }

                    if fun.sig.ensures.is_some() {
                        update_removed_lines(&mut self.removed_lines, &fun.sig.ensures);
                        update_line_count(&mut self.proof_count, &fun.sig.ensures);
                    }

                    if fun.sig.invariants.is_some() {
                        update_removed_lines(&mut self.removed_lines, &fun.sig.invariants);
                        update_line_count(&mut self.proof_count, &fun.sig.invariants);
                    }

                    if fun.sig.recommends.is_some() {
                        update_removed_lines(&mut self.removed_lines, &fun.sig.recommends);
                        update_line_count(&mut self.proof_count, &fun.sig.recommends);
                    }

                    sig.recommends = Option::None;
                    sig.requires = Option::None;
                    sig.ensures = Option::None;
                    sig.decreases = Option::None;
                    self.codes.push((
                        "fn".to_string(),
                        format!("{}", quote! {#sig},),
                        format!("{}", quote! {#fun}),
                    ));
                    visit_item_fn_mut(self, fun);
                }
            }
        }
    }

    fn visit_impl_item_method_mut(&mut self, fun: &mut ImplItemMethod) {
        let mut sig = fun.sig.clone();
        let external = attr_is_external(&fun.attrs);
        match sig.mode {
            FnMode::Spec(_) => {
                update_removed_lines(&mut self.removed_lines, &fun);
                update_line_count(&mut self.spec_count, &fun);
                /*for stmt in &fun.block.stmts {
                    update_removed_lines(&mut self.removed_lines, stmt);
                    update_line_count(&mut self.spec_count, stmt);
                }*/
            }
            FnMode::Proof(_) => {
                update_removed_lines(&mut self.removed_lines, &fun);
                if external {
                    update_line_count(&mut self.trusted_proof, &fun);
                } else {
                    update_line_count(&mut self.proof_count, &fun);
                }
            }
            _ => {
                if external {
                    update_removed_lines(&mut self.removed_lines, &fun);
                    update_line_count(&mut self.trusted_exe, &fun);
                } else {
                    if fun.sig.decreases.is_some() {
                        update_removed_lines(&mut self.removed_lines, &fun.sig.decreases);
                        update_line_count(&mut self.proof_count, &fun.sig.decreases);
                    }

                    if fun.sig.requires.is_some() {
                        update_removed_lines(&mut self.removed_lines, &fun.sig.requires);
                        update_line_count(&mut self.proof_count, &fun.sig.requires);
                    }

                    if fun.sig.ensures.is_some() {
                        update_removed_lines(&mut self.removed_lines, &fun.sig.ensures);
                        update_line_count(&mut self.proof_count, &fun.sig.ensures);
                    }

                    if fun.sig.invariants.is_some() {
                        update_removed_lines(&mut self.removed_lines, &fun.sig.invariants);
                        update_line_count(&mut self.proof_count, &fun.sig.invariants);
                    }

                    if fun.sig.recommends.is_some() {
                        update_removed_lines(&mut self.removed_lines, &fun.sig.recommends);
                        update_line_count(&mut self.proof_count, &fun.sig.recommends);
                    }
                    visit_impl_item_method_mut(self, fun);
                }
            }
        }
    }

    fn visit_trait_item_method_mut(&mut self, method: &mut TraitItemMethod) {
        visit_trait_item_method_mut(self, method);
    }

    fn visit_item_const_mut(&mut self, con: &mut ItemConst) {
        visit_item_const_mut(self, con);
    }

    fn visit_field_mut(&mut self, field: &mut Field) {
        visit_field_mut(self, field);
    }

    fn visit_item_enum_mut(&mut self, item: &mut ItemEnum) {
        match item.mode {
            DataMode::Default => {}
            _ => {
                update_line_count(&mut self.ghost_struct_count, &item);
            }
        }
        visit_item_enum_mut(self, item);
        let ident = &item.ident;
        let generics = &item.generics;
        self.codes.push((
            "enum".to_string(),
            format!("{}", quote! {#ident #generics}),
            format!("{}", quote! {#item}),
        ));
    }

    fn visit_item_struct_mut(&mut self, item: &mut ItemStruct) {
        visit_item_struct_mut(self, item);
        let ident = &item.ident;
        let generics = &item.generics;
        match item.mode {
            DataMode::Default => {}
            _ => {
                update_line_count(&mut self.ghost_struct_count, &item);
            }
        }
        self.codes.push((
            "struct".to_string(),
            format!("{}", quote! {#ident #generics}),
            format!("{}", quote! {#item}),
        ));
    }

    fn visit_type_mut(&mut self, ty: &mut Type) {
        syn_verus::visit_mut::visit_type_mut(self, ty);
    }

    fn visit_path_mut(&mut self, path: &mut Path) {
        syn_verus::visit_mut::visit_path_mut(self, path);
    }

    fn visit_generic_method_argument_mut(&mut self, arg: &mut syn_verus::GenericMethodArgument) {
        syn_verus::visit_mut::visit_generic_method_argument_mut(self, arg);
    }

    fn visit_item_mod_mut(&mut self, item: &mut ItemMod) {
        syn_verus::visit_mut::visit_item_mod_mut(self, item);
    }

    fn visit_item_impl_mut(&mut self, imp: &mut ItemImpl) {
        for item in &imp.items {
            match item {
                ImplItem::Const(_) => todo!(),
                ImplItem::Method(method) => {
                    let mut imp2 = imp.clone();
                    let mut sig = method.sig.clone();
                    let self_ty = &imp2.self_ty;
                    imp2.items.clear();
                    imp2.items.push(item.clone());
                    sig.recommends = Option::None;
                    sig.requires = Option::None;
                    sig.ensures = Option::None;
                    sig.decreases = Option::None;
                    self.codes.push((
                        "assoc_fn".to_string(),
                        format!("{}", quote! {#self_ty{#sig}}),
                        format!("{}", quote! {#imp2}),
                    ));
                }
                ImplItem::Type(_) => {}
                ImplItem::Macro(_) => {
                    println!("{:?} - {:?}", imp.span().start(), imp.span().end());
                    todo!()
                }
                ImplItem::Verbatim(_) => todo!(),
                _ => todo!(),
            }
        }
        syn_verus::visit_mut::visit_item_impl_mut(self, imp);
    }

    fn visit_item_trait_mut(&mut self, tr: &mut ItemTrait) {
        syn_verus::visit_mut::visit_item_trait_mut(self, tr);
        let ident = &tr.ident;
        let generics = &tr.generics;
        self.codes.push((
            "trait".to_string(),
            format!("{}", quote! {#ident #generics}),
            format!("{}", quote! {#tr}),
        ));
    }
}

pub struct Items {
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
struct MacroElements {
    elements: Vec<MacroElement>,
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

impl Parse for MacroElements {
    fn parse(input: ParseStream) -> syn_verus::parse::Result<MacroElements> {
        let mut elements = Vec::new();
        while !input.is_empty() {
            elements.push(input.parse()?);
        }
        Ok(MacroElements { elements })
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

impl quote::ToTokens for MacroElements {
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

// Unfortunately, the macro_rules tt tokenizer breaks tokens like &&& and ==> into smaller tokens.
// Try to put the original tokens back together here.
fn rejoin_tokens(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    use proc_macro::{Group, Punct, Spacing::*, Span, TokenTree};
    let mut tokens: Vec<TokenTree> = stream.into_iter().collect();
    let pun = |t: &TokenTree| match t {
        TokenTree::Punct(p) => Some((p.as_char(), p.spacing(), p.span())),
        _ => None,
    };
    let adjacent = |s1: Span, s2: Span| {
        let l1 = s1.end();
        let l2 = s2.start();
        s1.source_file() == s2.source_file() && l1 == l2
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

// Unfortunately, the macro_rules tt tokenizer breaks tokens like &&& and ==> into smaller tokens.
// Try to put the original tokens back together here.
pub(crate) fn rejoin_tokens2(stream: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    use proc_macro2::{Group, Punct, Spacing::*, Span, TokenTree};
    let mut tokens: Vec<TokenTree> = stream.into_iter().collect();
    let pun = |t: &TokenTree| match t {
        TokenTree::Punct(p) => Some((p.as_char(), p.spacing(), p.span())),
        _ => None,
    };
    let adjacent = |s1: Span, s2: Span| false;
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
                let mut new_group = Group::new(group.delimiter(), rejoin_tokens2(group.stream()));
                new_group.set_span(group.span());
                *group = new_group;
            }
            _ => {}
        }
    }
    proc_macro2::TokenStream::from_iter(tokens.into_iter())
}

pub fn new_visitor(remove_proof: bool) -> Visitor {
    Visitor {
        remove_proof: remove_proof,
        removed_lines: vec![],
        codes: vec![],
        proof_count: 0,
        ghost_struct_count: 0,
        proof_loop_count: 0,
        spec_count: 0,
        trusted_proof: 0,
        trusted_exe: 0,
    }
}

pub(crate) fn process_verus_code(stream: proc_macro2::TokenStream, visitor: &mut Visitor) {
    let stream = rejoin_tokens2(stream);

    let mut items: Result<Items, _> = parse2(stream);
    let mut items = items.unwrap();
    //visitor.visit_items_prefilter(&mut items.items);
    let mut input: String = "".to_string();
    for mut item in items.items {
        visitor.visit_item_mut(&mut item);
        input = input + format!("{}", quote! {#item}).as_str();
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
