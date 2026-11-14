//! Definitions: `def`, `theorem` and `instance`, each a signature and its
//! equations (docs/proposals/declaration-syntax.md §2.3), and attributes.

use crate::Span;
use crate::ast::{Attribute, Decl, Expr, Guard, Name, Pattern};
use crate::lexer::Tok;
use crate::tree::{Element, Leaf, Node, NodeKind};

use super::access::required;
use super::decls::name;
use super::header::{Param, clause_match, lower_header, take_defaults};
use super::{Lower, Lowering};

/// Whether `element` is the token `tok`.
pub(super) fn is_leaf(element: &Element<'_>, tok: &Tok) -> bool {
    matches!(element, Element::Leaf(leaf) if leaf.tok() == tok)
}

/// The span of a node's last token.
pub(super) fn last_token(node: Node<'_>) -> Option<Span> {
    let end = node.token_range().end.checked_sub(1)?;
    Some(node.file().tokens().get(end)?.span)
}

/// A header as the compiler's tree has it: the signature, and the patterns
/// each equation starts with.
struct Header {
    name: Name,
    signature: Decl,
    patterns: Vec<Pattern>,
}

impl<'f> Lower<'f> {
    /// `def f (x: A): R := e`, or with arms, or with no body (a primitive);
    /// `theorem`, `instance`; with `export` or `opaque`.
    pub(super) fn definition(&self, root: Node<'f>) -> Lowering<Vec<Decl>> {
        let Header {
            name,
            signature,
            patterns: header,
        } = self.header(root)?;
        let mut decls = vec![signature];
        if let Some(body) = root.child(NodeKind::Body) {
            let rhs = required(body.after(&Tok::ColonEq), NodeKind::Body, "its expression")?;
            let rhs = self.expr(rhs)?;
            match &rhs {
                // `:= match | …` is the arms form: the same equations, so the
                // definition has the same case tree.
                Expr::Lam(_, body, _) if clause_match(body) => {
                    let Expr::Match { alts, .. } = &**body else {
                        unreachable!("`clause_match` checked")
                    };
                    for alt in alts.iter().cloned() {
                        let mut patterns = header.clone();
                        patterns.extend(alt.patterns);
                        decls.push(Decl::Equation {
                            name: name.clone(),
                            patterns,
                            guard: alt.guard,
                            rhs: alt.body,
                            arm: Some(header.len()),
                            span: alt.span,
                        });
                    }
                }
                _ => decls.push(Decl::Equation {
                    span: name.span.to(rhs.span()),
                    name,
                    patterns: header,
                    guard: None,
                    rhs: Some(rhs),
                    arm: None,
                }),
            }
        } else if let Some(arms) = root.child(NodeKind::Arms) {
            for arm in arms.child_nodes() {
                decls.push(self.arm(arm, &name, &header)?);
            }
        }
        Ok(decls)
    }

    /// A definition that didn't parse but whose header did: its signature,
    /// with no equations, marked with where its first error is.
    pub(super) fn kept_signature(&self, root: Node<'f>) -> Lowering<Decl> {
        let Header { mut signature, .. } = self.header(root)?;
        if let Decl::Signature {
            body_error, span, ..
        } = &mut signature
        {
            let range = required(root.span(), NodeKind::Error, "its tokens")?;
            let error_at = self.first_error_in(range.start as usize, range.end as usize);
            *body_error = Some(error_at.unwrap_or(*span));
        }
        Ok(signature)
    }

    /// The signature a definition's header makes: from its attributes to
    /// its `unfolding`. Stops at whatever follows (the body, the arms, or
    /// in a definition that didn't parse, what it failed in).
    fn header(&self, root: Node<'f>) -> Lowering<Header> {
        let kind = root.kind();
        let attrs = self.leading_attributes(root)?;
        let (mut start, mut keyword, mut name) = (None, None, None);
        let (mut export, mut opaque) = (false, false);
        let mut params = Vec::new();
        let (mut result, mut decreasing, mut unfolding) = (None, None, Vec::new());
        for child in root.children() {
            match child {
                Element::Leaf(leaf) if keyword.is_none() => {
                    start.get_or_insert(leaf.span());
                    match leaf.tok() {
                        Tok::KwExport => export = true,
                        Tok::KwOpaque => opaque = true,
                        Tok::KwDef | Tok::KwTheorem | Tok::KwInstance => keyword = Some(leaf),
                        _ => break,
                    }
                }
                Element::Leaf(leaf) if name.is_none() => {
                    name = Some(required(super::decls::name(leaf), kind, "its name")?)
                }
                // `theorem t ∀ (x: A) …` (D3472): cosmetic.
                Element::Leaf(leaf) if *leaf.tok() == Tok::KwForall && params.is_empty() => {}
                Element::Node(node) if node.kind() == NodeKind::Attributes => {}
                Element::Node(node) if name.is_some() && result.is_none() => match node.kind() {
                    NodeKind::Param => params.push(self.param(node)?),
                    NodeKind::ResultType => {
                        let ty = node.after(&Tok::Colon);
                        result =
                            Some(self.expr(required(ty, NodeKind::ResultType, "its type")?)?);
                    }
                    _ => break,
                },
                Element::Node(node) if node.kind() == NodeKind::Decreasing => {
                    let measure = node.after(&Tok::KwDecreasing);
                    let measure = required(measure, NodeKind::Decreasing, "its measure")?;
                    decreasing = Some(Box::new(self.expr(measure)?));
                }
                Element::Node(node) if node.kind() == NodeKind::Unfolding => {
                    unfolding = node.own_leaves().filter_map(super::decls::name).collect();
                }
                _ => break,
            }
        }
        let keyword = required(keyword, kind, "`def`, `theorem` or `instance`")?;
        let start = start.unwrap_or(keyword.span());
        let name = required(name, kind, "its name")?;
        let result = required(result, kind, "its type")?;
        let defaults = take_defaults(&mut params);
        let span = start.to(result.span());
        let (ty, patterns) = lower_header(params, result);
        let signature = Decl::Signature {
            name: name.clone(),
            ty,
            theorem: *keyword.tok() == Tok::KwTheorem,
            export,
            synonym: false,
            instance: *keyword.tok() == Tok::KwInstance,
            decreasing,
            opaque,
            unfolding,
            defaults,
            attrs,
            body_error: None,
            span,
        };
        Ok(Header {
            name,
            signature,
            patterns,
        })
    }

    /// A header's parameter: `(x y: A)`, `(x: A := v)`, `[x: A]`,
    /// `[auto h: P]`, `[auto P]` or `()`.
    pub(super) fn param(&self, node: Node<'f>) -> Lowering<Param> {
        let kind = NodeKind::Param;
        let parts: Vec<Element<'f>> = node.children().collect();
        let span = required(node.span(), kind, "its tokens")?;
        if parts.len() == 2 && is_leaf(&parts[1], &Tok::RParen) {
            return Ok(Param::Unit(span));
        }
        let implicit = is_leaf(&parts[0], &Tok::LBracket);
        let Some(colon) = parts.iter().position(|part| is_leaf(part, &Tok::Colon)) else {
            // `[auto Ord a]`: no name, so nothing can refer to it.
            let auto = parts.get(1).and_then(as_leaf);
            let auto = required(auto, kind, "`auto`")?;
            let ty = required(parts.get(2).copied(), kind, "its type")?;
            return Ok(Param::Named {
                names: vec![Name {
                    text: crate::ast::NAMELESS.to_string(),
                    span: auto.span(),
                }],
                ty: self.expr(ty)?,
                implicit,
                auto: true,
                default: None,
                span,
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
        let default = match node.child(NodeKind::Default) {
            Some(default) => {
                let value = default.after(&Tok::ColonEq);
                let value = required(value, NodeKind::Default, "its value")?;
                Some(Box::new(self.expr(value)?))
            }
            None => None,
        };
        Ok(Param::Named {
            names,
            ty: self.expr(ty)?,
            implicit,
            auto,
            default,
            span,
        })
    }

    /// `| p, q if c => body`, or with an absurd pattern and no body,
    /// `| p, ()`: an equation whose patterns are the header's, then the
    /// arm's.
    fn arm(&self, arm: Node<'f>, name: &Name, header: &[Pattern]) -> Lowering<Decl> {
        let kind = NodeKind::Arm;
        let mut patterns = header.to_vec();
        let (mut guard, mut rhs) = (None, None);
        let mut parts = arm.children().skip(1);
        while let Some(part) = parts.next() {
            match part {
                Element::Leaf(leaf) if *leaf.tok() == Tok::Comma => {}
                Element::Leaf(leaf) if *leaf.tok() == Tok::FatArrow => {
                    let body = required(parts.next(), kind, "its body")?;
                    rhs = Some(self.expr(body)?);
                    break;
                }
                Element::Node(node) if node.kind() == NodeKind::Guard => {
                    guard = Some(self.guard(node)?);
                }
                pattern => patterns.push(self.pattern(pattern)?),
            }
        }
        Ok(Decl::Equation {
            name: name.clone(),
            patterns,
            guard,
            rhs,
            arm: Some(header.len()),
            span: required(arm.span(), kind, "its tokens")?,
        })
    }

    /// `if c` or `if h: c` after an arm's patterns.
    pub(super) fn guard(&self, node: Node<'f>) -> Lowering<Guard> {
        let kind = NodeKind::Guard;
        let start = required(node.first_leaf_is(&Tok::KwIf), kind, "`if`")?;
        let (binder, cond) = match node.leaf(&Tok::Colon) {
            Some(_) => {
                let binder = as_leaf_opt(node.after(&Tok::KwIf)).and_then(name);
                let binder = required(binder, kind, "its name")?;
                (Some(binder), node.after(&Tok::Colon))
            }
            None => (None, node.after(&Tok::KwIf)),
        };
        let cond = self.expr(required(cond, kind, "its condition")?)?;
        Ok(Guard {
            binder,
            span: start.span().to(cond.span()),
            cond,
        })
    }

    /// The attributes written as groups `@[a, b "x"] @[c]` among `node`'s
    /// children, in order.
    pub(super) fn attributes(&self, node: Node<'f>) -> Lowering<Vec<Attribute>> {
        let groups = node
            .child_nodes()
            .filter(|n| n.kind() == NodeKind::Attributes);
        attributes_in(groups)
    }

    /// The attributes before a declaration: those before its first token,
    /// since a declaration that didn't parse may have more inside it.
    pub(super) fn leading_attributes(&self, root: Node<'f>) -> Lowering<Vec<Attribute>> {
        let groups = root.children().map_while(|child| match child {
            Element::Node(node) if node.kind() == NodeKind::Attributes => Some(node),
            _ => None,
        });
        attributes_in(groups)
    }
}

/// The attributes of the groups `@[a, b "x"]`, in order.
fn attributes_in<'f>(groups: impl Iterator<Item = Node<'f>>) -> Lowering<Vec<Attribute>> {
    let mut attrs = Vec::new();
    for group in groups {
        for attribute in group.child_nodes() {
            attrs.push(attribute_of(attribute)?);
        }
    }
    Ok(attrs)
}

/// One attribute, `js.name "x"`.
fn attribute_of(node: Node<'_>) -> Lowering<Attribute> {
    let kind = NodeKind::Attribute;
    let name = match node.children().next() {
        Some(Element::Leaf(leaf)) => name(leaf),
        Some(Element::Node(parts)) if parts.kind() == NodeKind::AttributeName => {
            let mut words = parts.own_leaves().filter_map(name);
            words.next().map(|first| {
                words.fold(first, |mut name, part| {
                    name.text.push('.');
                    name.text.push_str(&part.text);
                    name.span = name.span.to(part.span);
                    name
                })
            })
        }
        _ => None,
    };
    let name = required(name, kind, "its name")?;
    let arg = node.own_leaves().find_map(|leaf| match leaf.tok() {
        Tok::Str(text) => Some((text.clone(), leaf.span())),
        _ => None,
    });
    let span = arg.as_ref().map_or(name.span, |(_, s)| name.span.to(*s));
    Ok(Attribute { name, arg, span })
}

/// The token an element is, if it is one.
pub(super) fn as_leaf<'f>(element: &Element<'f>) -> Option<Leaf<'f>> {
    match element {
        Element::Leaf(leaf) => Some(*leaf),
        Element::Node(_) => None,
    }
}

fn as_leaf_opt(element: Option<Element<'_>>) -> Option<Leaf<'_>> {
    as_leaf(&element?)
}

#[cfg(test)]
mod tests {
    use crate::SourceMap;
    use crate::lower::oracle::{Report, compare};
    use crate::tree::NodeKind;

    fn report(text: &str) -> Report {
        compare(SourceMap::new().next_id(), text, crate::DEFAULT_STACK, true)
    }

    fn differences(report: &Report) -> Vec<String> {
        let at =
            |d: &crate::lower::oracle::Difference| format!("{} at {}:\n{}", d.what, d.at, d.detail);
        report.differences.iter().map(at).collect()
    }

    /// Every kind of declaration and header part comes out of the lowering
    /// as the parser builds it, spans included: attributes, `export` and
    /// `opaque`, each kind of parameter and its default, a theorem's `∀`,
    /// `decreasing` and `unfolding`, arms with guards and an absurd one,
    /// data types with indices, constructors in brackets and braces,
    /// records, synonyms, interfaces, abilities, function types and rows.
    #[test]
    fn declarations_and_headers_lower_as_parsed() {
        let text = "\
@[inline] @[a.b \"c\", d] export def f (x y: Nat) [a: Type] (z: Nat := 3) (): Nat := x
opaque def o: Nat := 1
export opaque def o2: Nat := 1
theorem t ∀ (x: Nat) [auto h: P] [auto Q]: P decreasing x unfolding g, H := h
def g (x: Nat): Nat
  | Zero => x
  | n if n => n
  | 'c' if h: m => h
  | 3, _ => h
  | ()
def prim: Type
@[js.tag \"t\"] type T (a: Type) [auto o: O] : Nat -> (n: Nat) -> Type =
  | A
  | @[x \"y\"] B (x: Nat := 1) [y: a] : T
  | C { f: Nat, g: Nat := 2 }
  | D [k: Nat] { f: Nat }
type E
type R = { x: Nat := 1, @[q.r \"s\"] y: Nat }
type S (a: Type) [auto o: O] : Type = a
@[inline] type S2 = Nat
interface I (a: Type) = { op: a, op2: a := op }
ability St (s: Type) where
  get: (u: Nat) -> {St} s
  put: (x: s) -> {St, r} Nat
instance i: I := x
def e: {IO | r} Nat := x
def e2: {} Nat := x
def ft: (x: Nat) -> [y: Type] -> [auto Q] -> Nat := ft
";
        let report = report(text);
        assert_eq!(differences(&report), Vec::<String>::new());
        assert!(report.unsupported.is_empty(), "{:?}", report.unsupported);
        use NodeKind::*;
        assert_eq!(
            report.lowered,
            [
                Def,
                Def,
                Def,
                Theorem,
                Def,
                Def,
                DataType,
                DataType,
                RecordType,
                TypeSynonym,
                TypeSynonym,
                Interface,
                Ability,
                Instance,
                Def,
                Def,
                Def
            ]
        );
    }

    /// A definition that doesn't parse keeps its signature when its header
    /// parsed, with where its first error is, and its attributes (not those
    /// in its body); when its header didn't parse, it gives its name as
    /// failed.
    #[test]
    fn a_failed_definition_keeps_its_signature_if_its_header_parsed() {
        let text = "\
def bad (x: Nat): Nat := (
@[a] def bad2 (x: Nat): Nat decreasing x
  | Zero => (
theorem bad3 (x: Nat): x := h
  | Zero => x
def bad4 (x x: Nat): Nat := x
def bad5 (x: Nat): Nat := x where
def bad6 (x: Nat): Nat :=
  @[tailrec]
  x
def bad7 (x: Nat) Nat := x
";
        let report = report(text);
        assert_eq!(differences(&report), Vec::<String>::new());
        assert!(report.unsupported.is_empty(), "{:?}", report.unsupported);
        let file = SourceMap::new().next_id();
        let (module, _) = crate::parse_module_recovering(file, text, crate::DEFAULT_STACK);
        let kept: Vec<&str> = module
            .decls
            .iter()
            .map(|d| match d {
                crate::ast::Decl::Signature {
                    name,
                    body_error: Some(_),
                    ..
                } => name.text.as_str(),
                other => panic!("{other:?}"),
            })
            .collect();
        assert_eq!(kept, ["bad", "bad2", "bad3", "bad5", "bad6"]);
        let failed: Vec<&str> = module.failed.iter().map(|f| f.name.text.as_str()).collect();
        assert_eq!(failed, ["bad4", "bad7"]);
    }
}
