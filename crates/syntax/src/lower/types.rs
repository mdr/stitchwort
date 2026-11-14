//! Type declarations (`type`, `interface`, a type synonym, `ability`), their
//! binders, constructors and fields; and the types written with binders or
//! abilities: `(x: A) -> B` and `{IO} T`.

use crate::ast::{Binder, CtorDecl, Decl, Expr, NAMELESS, Name, Row};
use crate::lexer::Tok;
use crate::tree::{Element, Node, NodeKind};

use super::access::required;
use super::decls::name;
use super::definitions::{as_leaf, is_leaf, last_token};
use super::header::{Param, lower_header};
use super::{Lower, Lowering};

/// A data type's index types, each with its name if written as a binder.
type Indices = Vec<(Option<Name>, Expr)>;

/// A binder as written: its parts, whether it is in square brackets, and
/// whether it is `auto`.
struct Written {
    binder: Binder,
    implicit: bool,
    auto: bool,
    default: Option<Expr>,
}

impl<'f> Lower<'f> {
    /// `type T (a: Type) : Type = | A | B (x: a)`, `type R = { x: Nat }`,
    /// `interface I (a: Type) = { … }`, or a type without constructors.
    pub(super) fn data(&self, root: Node<'f>) -> Lowering<Decl> {
        let kind = root.kind();
        let attrs = self.leading_attributes(root)?;
        let keyword = root
            .own_leaves()
            .find(|leaf| matches!(leaf.tok(), Tok::KwType | Tok::KwInterface));
        let keyword = required(keyword, kind, "`type` or `interface`")?;
        let name = as_leaf_after(root, keyword.tok()).and_then(name);
        let name = required(name, kind, "its name")?;
        let (mut params, mut auto_params) = (Vec::new(), Vec::new());
        for binder in root.child_nodes().filter(|n| n.kind() == NodeKind::Binder) {
            let written = self.binder(binder)?;
            params.push(written.binder);
            auto_params.push(written.auto);
        }
        let (indices, sort) = match root.child(NodeKind::ResultType) {
            Some(result) => self.indices(result)?,
            None => (Vec::new(), None),
        };
        let mut ctors = Vec::new();
        if let Some(fields) = root.child(NodeKind::Fields) {
            ctors.push(self.record_fields(fields, &name)?);
        }
        for ctor in root.child_nodes() {
            if ctor.kind() == NodeKind::Constructor {
                ctors.push(self.constructor(ctor)?);
            }
        }
        let last = required(last_token(root), kind, "its tokens")?;
        Ok(Decl::Data {
            span: keyword.span().to(last),
            name,
            params,
            auto_params,
            indices,
            sort,
            ctors,
            record: kind != NodeKind::DataType,
            interface: kind == NodeKind::Interface,
            attrs,
        })
    }

    /// `type Grid (a: Type) = List (List a)`: a signature and one equation,
    /// as `def Grid (a: Type): Type := List (List a)` would be.
    pub(super) fn type_synonym(&self, root: Node<'f>) -> Lowering<Vec<Decl>> {
        let kind = NodeKind::TypeSynonym;
        let attrs = self.leading_attributes(root)?;
        let keyword = required(root.leaf(&Tok::KwType), kind, "`type`")?;
        let name = as_leaf_after(root, &Tok::KwType).and_then(name);
        let name = required(name, kind, "its name")?;
        let mut params = Vec::new();
        for binder in root.child_nodes().filter(|n| n.kind() == NodeKind::Binder) {
            let Written { binder, auto, .. } = self.binder(binder)?;
            // An `auto` parameter, `[auto ord: Ord k]`, is one of the
            // definition's.
            params.push(Param::Named {
                span: binder.names[0].span.to(binder.ty.span()),
                names: binder.names,
                ty: binder.ty,
                implicit: auto,
                auto,
                default: None,
            });
        }
        let sort = match root.child(NodeKind::ResultType) {
            Some(result) => self.indices(result)?.1,
            None => None,
        };
        let body = required(root.child(NodeKind::Body), kind, "its body")?;
        let body = required(body.after(&Tok::Equals), NodeKind::Body, "its type")?;
        let body = self.expr(body)?;
        let result = sort.unwrap_or(Expr::Type(0, name.span));
        let (ty, header) = lower_header(params, result);
        Ok(vec![
            Decl::Signature {
                name: name.clone(),
                ty,
                theorem: false,
                export: false,
                synonym: true,
                instance: false,
                decreasing: None,
                opaque: false,
                unfolding: Vec::new(),
                defaults: Vec::new(),
                attrs,
                body_error: None,
                span: keyword.span().to(name.span),
            },
            Decl::Equation {
                span: name.span.to(body.span()),
                name,
                patterns: header,
                guard: None,
                rhs: Some(body),
                arm: None,
            },
        ])
    }

    /// `ability State (s: Type) where`, then one operation per line.
    pub(super) fn ability(&self, root: Node<'f>) -> Lowering<Decl> {
        let kind = NodeKind::Ability;
        let keyword = required(root.leaf(&Tok::KwAbility), kind, "`ability`")?;
        let name = as_leaf_after(root, &Tok::KwAbility).and_then(name);
        let name = required(name, kind, "its name")?;
        let mut params = Vec::new();
        let mut ops = Vec::new();
        for node in root.child_nodes() {
            match node.kind() {
                NodeKind::Binder => params.push(self.binder(node)?.binder),
                NodeKind::AbilityOp => {
                    let op = node.own_leaves().next().and_then(super::decls::name);
                    let op = required(op, NodeKind::AbilityOp, "its name")?;
                    let ty = required(node.after(&Tok::Colon), NodeKind::AbilityOp, "its type")?;
                    ops.push((op, self.expr(ty)?));
                }
                _ => {}
            }
        }
        let last = required(last_token(root), kind, "its tokens")?;
        Ok(Decl::Ability {
            span: keyword.span().to(last),
            name,
            params,
            ops,
        })
    }

    /// A data type's `: Nat -> (n: Nat) -> Type` after its parameters: the
    /// index types, named when written as binders, and the universe.
    fn indices(&self, result: Node<'f>) -> Lowering<(Indices, Option<Expr>)> {
        let mut indices = Vec::new();
        let mut parts = result.children().skip(1).peekable();
        while let Some(part) = parts.next() {
            match part {
                Element::Leaf(leaf) if *leaf.tok() == Tok::Arrow => {}
                Element::Node(node) if node.kind() == NodeKind::Binder => {
                    let binder = self.binder(node)?.binder;
                    for name in binder.names {
                        indices.push((Some(name), binder.ty.clone()));
                    }
                }
                ty => {
                    let ty = self.expr(ty)?;
                    if parts.peek().is_some_and(|next| is_leaf(next, &Tok::Arrow)) {
                        indices.push((None, ty));
                    } else {
                        return Ok((indices, Some(ty)));
                    }
                }
            }
        }
        Ok((indices, None))
    }

    /// `| C (x: A) [n: Nat] : T n`, `| C { x: A }`, with attributes after
    /// the `|`.
    fn constructor(&self, ctor: Node<'f>) -> Lowering<CtorDecl> {
        let kind = NodeKind::Constructor;
        let attrs = self.attributes(ctor)?;
        let name = ctor.own_leaves().nth(1).and_then(name);
        let name = required(name, kind, "its name")?;
        let (mut fields, mut implicit, mut defaults) = (Vec::new(), Vec::new(), Vec::new());
        let (mut braced, mut result) = (false, None);
        for node in ctor.child_nodes() {
            match node.kind() {
                NodeKind::Binder => {
                    let written = self.binder(node)?;
                    fields.push(written.binder);
                    implicit.push(written.implicit);
                    defaults.push(written.default);
                }
                NodeKind::Fields => {
                    braced = true;
                    for (binder, default) in self.fields(node)? {
                        fields.push(binder);
                        implicit.push(false);
                        defaults.push(default);
                    }
                }
                NodeKind::ResultType => {
                    let ty = required(node.after(&Tok::Colon), NodeKind::ResultType, "its type")?;
                    result = Some(self.expr(ty)?);
                }
                _ => {}
            }
        }
        if defaults.iter().all(Option::is_none) {
            defaults.clear();
        }
        Ok(CtorDecl {
            attrs,
            name,
            fields,
            implicit,
            defaults,
            result,
            braced,
        })
    }

    /// A record's fields, `{ name: Text, age: Nat }`, as the one
    /// constructor of the data type `data`, named `%mk`, which source can't
    /// write (so `data.mk` is free for a function).
    fn record_fields(&self, fields: Node<'f>, data: &Name) -> Lowering<CtorDecl> {
        let (fields, mut defaults): (Vec<_>, Vec<_>) = self.fields(fields)?.into_iter().unzip();
        if defaults.iter().all(Option::is_none) {
            defaults.clear();
        }
        Ok(CtorDecl {
            attrs: Vec::new(),
            name: Name {
                text: "%mk".into(),
                span: data.span,
            },
            fields,
            implicit: Vec::new(),
            defaults,
            result: None,
            braced: false,
        })
    }

    /// Fields in braces, `{ name: Text, step: Nat := 1 }`: a binder for
    /// each, with its default.
    fn fields(&self, fields: Node<'f>) -> Lowering<Vec<(Binder, Option<Expr>)>> {
        let mut out = Vec::new();
        for field in fields.child_nodes() {
            let kind = NodeKind::Field;
            let attrs = self.attributes(field)?;
            let name = field.own_leaves().next().and_then(name);
            let name = required(name, kind, "its name")?;
            let ty = required(field.after(&Tok::Colon), kind, "its type")?;
            out.push((
                Binder {
                    names: vec![name],
                    ty: self.expr(ty)?,
                    attrs,
                },
                self.default(field)?,
            ));
        }
        Ok(out)
    }

    /// The default value among `node`'s children, `:= v`, if it has one.
    fn default(&self, node: Node<'f>) -> Lowering<Option<Expr>> {
        match node.child(NodeKind::Default) {
            Some(default) => {
                let value = required(default.after(&Tok::ColonEq), NodeKind::Default, "its value")?;
                Ok(Some(self.expr(value)?))
            }
            None => Ok(None),
        }
    }

    /// `(x y: A)`, `(x: A := v)`, `[x: A]`, `[auto x: P]` or `[auto P]`,
    /// with any attributes before the names.
    fn binder(&self, node: Node<'f>) -> Lowering<Written> {
        let kind = NodeKind::Binder;
        let attrs = self.attributes(node)?;
        let parts: Vec<Element<'f>> = node
            .children()
            .filter(|part| !matches!(part, Element::Node(n) if n.kind() == NodeKind::Attributes))
            .collect();
        let implicit = parts
            .first()
            .is_some_and(|open| is_leaf(open, &Tok::LBracket));
        let Some(colon) = parts.iter().position(|part| is_leaf(part, &Tok::Colon)) else {
            // `[auto Ord a]`, without a name.
            let auto = parts.get(1).and_then(as_leaf);
            let auto = required(auto, kind, "`auto`")?;
            let ty = required(parts.get(2).copied(), kind, "its type")?;
            return Ok(Written {
                binder: Binder {
                    names: vec![Name {
                        text: NAMELESS.to_string(),
                        span: auto.span(),
                    }],
                    ty: self.expr(ty)?,
                    attrs,
                },
                implicit,
                auto: true,
                default: None,
            });
        };
        let mut names: Vec<Name> = parts[1..colon]
            .iter()
            .filter_map(as_leaf)
            .filter_map(name)
            .collect();
        let auto = implicit && names.len() > 1 && names[0].text == "auto";
        if auto {
            names.remove(0);
        }
        let ty = required(parts.get(colon + 1).copied(), kind, "its type")?;
        Ok(Written {
            binder: Binder {
                names,
                ty: self.expr(ty)?,
                attrs,
            },
            implicit,
            auto,
            default: self.default(node)?,
        })
    }

    /// `(x: A) -> B` or `[x: A] -> B`.
    #[inline(never)]
    pub(super) fn function_type(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::FunctionType;
        let binder = required(node.child(NodeKind::Binder), kind, "its binder")?;
        let start = required(binder.span(), kind, "its binder")?;
        let Written {
            binder,
            implicit,
            auto,
            ..
        } = self.binder(binder)?;
        let cod = required(node.after(&Tok::Arrow), kind, "its result")?;
        let cod = self.expr(cod)?;
        Ok(Expr::Pi {
            span: start.to(cod.span()),
            names: binder.names,
            implicit,
            auto,
            dom: Box::new(binder.ty),
            cod: Box::new(cod),
        })
    }

    /// `{IO, State s} T`: a type with abilities.
    #[inline(never)]
    pub(super) fn effect(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::Effect;
        let row = required(node.child(NodeKind::Row), kind, "its row")?;
        let ty = node
            .children()
            .skip_while(|part| !matches!(part, Element::Node(n) if n.kind() == NodeKind::Row))
            .nth(1);
        let ty = required(ty, kind, "its type")?;
        Ok(Expr::Effect(self.row(row)?, Box::new(self.expr(ty)?)))
    }

    /// `{A, B args | e}`, `{A, e}`, `{e}` or `{}`: a lowercase name last
    /// is the row's variable.
    fn row(&self, node: Node<'f>) -> Lowering<Row> {
        let kind = NodeKind::Row;
        let span = required(node.span(), kind, "its tokens")?;
        let mut abilities = Vec::new();
        let mut tail = None;
        let mut parts = node.children().skip(1);
        while let Some(part) = parts.next() {
            match part {
                Element::Leaf(leaf) if matches!(leaf.tok(), Tok::Comma | Tok::RBrace) => {}
                Element::Leaf(leaf) if *leaf.tok() == Tok::Pipe => {
                    let name = parts.next().as_ref().and_then(as_leaf).and_then(name);
                    tail = Some(required(name, kind, "its variable")?);
                }
                ability => abilities.push(self.expr(ability)?),
            }
        }
        if tail.is_none()
            && let Some(Expr::Var(name)) = abilities.last()
            && name.text.starts_with(|c: char| c.is_ascii_lowercase())
        {
            tail = Some(name.clone());
            abilities.pop();
        }
        Ok(Row {
            abilities,
            tail,
            span,
        })
    }
}

/// The token right after `node`'s own token `tok`, if that is a token.
fn as_leaf_after<'f>(node: Node<'f>, tok: &Tok) -> Option<crate::tree::Leaf<'f>> {
    as_leaf(&node.after(tok)?)
}
