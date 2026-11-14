//! Binding: a block's lines (`let`, local definitions, sequences), the
//! expression `let`, lambdas and their pattern parameters, `forall` and
//! `exists`, `if`, and clause lambdas (`match | …`, `match some | …`,
//! `matches | …`). The parser still builds the compiler's tree itself and
//! shares the expansions here ([`bind_let`], [`lines`], [`lambda_of`],
//! [`forall_of`], [`exists_chain`], [`clause_lambda_of`]), so both routes
//! expand the same way.

use crate::Span;
use crate::ast::{Alt, Expr, LocalDef, MatchKind, Mode, Name, Pattern, Scrutinee};
use crate::lexer::Tok;
use crate::tree::{Element, Leaf, Node, NodeKind};

use super::access::required;
use super::decls::name;
use super::definitions::last_token;
use super::header::Param;
use super::{Lower, Lowering, Unsupported};

/// One line of a block.
pub(crate) enum Stmt {
    Let(Name, Option<Expr>, Expr, Span),
    /// `let (a, b) = e`: a pattern binding, desugared to a `match` in `block`.
    LetPattern(Pattern, Option<Expr>, Expr, Span),
    /// A local `def` or `theorem`; the span is where it starts.
    Def(LocalDef, Span),
    Expr(Expr),
}

/// `let p := e` followed by `rest`: the `Let` (or, for a pattern, the
/// one-alternative `match`) that a block's `let` line and an expression
/// `let` both make.
pub(crate) fn bind_let(stmt: Stmt, rest: Expr) -> Expr {
    match stmt {
        Stmt::LetPattern(pattern, ty, value, span) => {
            let expr = match ty {
                Some(ty) => {
                    let ann_span = value.span().to(ty.span());
                    Expr::Ann(Box::new(value), Box::new(ty), ann_span)
                }
                None => value,
            };
            let alt_span = pattern.span().to(rest.span());
            let span = span.to(rest.span());
            Expr::Match {
                scrutinees: vec![Scrutinee { name: None, expr }],
                alts: vec![Alt {
                    guard: None,
                    patterns: vec![pattern],
                    body: Some(rest),
                    span: alt_span,
                }],
                span,
                kind: MatchKind::Let,
            }
        }
        Stmt::Let(name, ty, value, span) => Expr::Let {
            span: span.to(rest.span()),
            name,
            ty: ty.map(Box::new),
            value: Box::new(value),
            body: Box::new(rest),
        },
        _ => unreachable!("bind_let takes a `let`"),
    }
}

/// A block's lines before its last, `stmts`, in front of the last, `rest`:
/// nested `Let`s (or one-alternative `match`es), `Seq`s and `LocalDefs`,
/// each spanning to the block's end. Consecutive local definitions are one
/// `LocalDefs`, so they can call each other.
pub(crate) fn lines(stmts: Vec<Stmt>, mut rest: Expr) -> Expr {
    // Whether `rest` is a `LocalDefs` made from the line after this one,
    // which another local definition joins.
    let mut grouping = false;
    for stmt in stmts.into_iter().rev() {
        let was_grouping = std::mem::replace(&mut grouping, false);
        rest = match stmt {
            Stmt::Def(def, span) => {
                grouping = true;
                if was_grouping
                    && let Expr::LocalDefs {
                        defs, span: end, ..
                    } = &mut rest
                {
                    defs.insert(0, def);
                    *end = span.to(*end);
                    rest
                } else {
                    Expr::LocalDefs {
                        defs: vec![def],
                        span: span.to(rest.span()),
                        body: Box::new(rest),
                    }
                }
            }
            stmt @ (Stmt::LetPattern(..) | Stmt::Let(..)) => bind_let(stmt, rest),
            Stmt::Expr(e) => Expr::Seq(Box::new(e), Box::new(rest)),
        };
    }
    rest
}

/// A lambda parameter: a name (with the pattern it stands for, if it was
/// written as one), or a name with a written type and its mode.
pub(crate) enum LamParam {
    Plain(Name, Option<Pattern>),
    Typed(Name, Mode, Expr),
    /// `(pattern: A)`: a pattern with a written type, an explicit parameter
    /// of that type taken apart by the pattern.
    TypedPattern(Name, Pattern, Expr),
}

/// The lambda with parameters `params` and body `body`, written from
/// `start` (its first parameter) to `end` (its last token). Parameters
/// written as patterns are named `%arg<i>` and taken apart by a
/// one-alternative `match` around the body.
pub(crate) fn lambda_of(params: Vec<LamParam>, body: Expr, start: Span, end: Span) -> Expr {
    let span = start.to(body.span());
    let mut scrutinees = Vec::new();
    let mut patterns = Vec::new();
    for param in &params {
        if let LamParam::Plain(name, Some(pattern)) | LamParam::TypedPattern(name, pattern, _) =
            param
        {
            scrutinees.push(Scrutinee {
                name: None,
                expr: Expr::Var(name.clone()),
            });
            patterns.push(pattern.clone());
        }
    }
    let mut result = if patterns.is_empty() {
        body
    } else {
        let alt_span = patterns[0].span().to(end);
        Expr::Match {
            scrutinees,
            alts: vec![Alt {
                guard: None,
                patterns,
                body: Some(body),
                span: alt_span,
            }],
            span,
            kind: MatchKind::Lambda,
        }
    };
    // Build from the last parameter outwards: a run of untyped ones is
    // one `Lam`, and each typed one is a `TypedLam`.
    let mut run: Vec<Name> = Vec::new();
    for param in params.into_iter().rev() {
        match param {
            LamParam::Plain(name, _) => run.push(name),
            LamParam::Typed(name, mode, ty) => {
                if !run.is_empty() {
                    run.reverse();
                    result = Expr::Lam(std::mem::take(&mut run), Box::new(result), span);
                }
                result = Expr::TypedLam(name, mode, Box::new(ty), Box::new(result), span);
            }
            LamParam::TypedPattern(name, _, ty) => {
                if !run.is_empty() {
                    run.reverse();
                    result = Expr::Lam(std::mem::take(&mut run), Box::new(result), span);
                }
                let ty = Box::new(ty);
                result = Expr::TypedLam(name, Mode::Explicit, ty, Box::new(result), span);
            }
        }
    }
    if !run.is_empty() {
        run.reverse();
        result = Expr::Lam(run, Box::new(result), span);
    }
    result
}

/// One group of a `forall`'s parameters: its names, whether it's implicit,
/// whether it's `auto`, and its type.
pub(crate) type ForallGroup = (Vec<Name>, bool, bool, Expr);

/// `forall` at `keyword` with parameter groups `groups`: a function type
/// for each group, every one spanning the whole `forall`.
pub(crate) fn forall_of(groups: Vec<ForallGroup>, mut body: Expr, keyword: Span) -> Expr {
    let span = keyword.to(body.span());
    for (names, implicit, auto, dom) in groups.into_iter().rev() {
        body = Expr::Pi {
            names,
            implicit,
            auto,
            dom: Box::new(dom),
            cod: Box::new(body),
            span,
        };
    }
    body
}

/// A clause lambda's alternatives `alts` as the lambda over a `match` on
/// its parameters, `%arg0` and on, named at its keyword `keyword`; written
/// from `start` to `end`. `match some` and `matches` end with an
/// alternative for every other value, `None` or `False`, which has no place
/// in the source: its span is empty, at the end of the construct.
pub(crate) fn clause_lambda_of(
    kind: MatchKind,
    mut alts: Vec<Alt>,
    keyword: Span,
    start: Span,
    end: Span,
) -> Expr {
    let arity = alts[0].patterns.len();
    if kind != MatchKind::Clause {
        let rest = if kind == MatchKind::ClauseSome {
            "Std.Option.None"
        } else {
            "Std.Bool.False"
        };
        alts.push(Alt {
            patterns: vec![Pattern::Wildcard(keyword); arity],
            guard: None,
            body: Some(library_var(rest, Span::point(keyword.file, keyword.start))),
            span: Span::point(end.file, end.end),
        });
    }
    let span = start.to(end);
    let names: Vec<Name> = (0..arity)
        .map(|i| Name {
            text: format!("%arg{i}"),
            span: keyword,
        })
        .collect();
    let scrutinees = names
        .iter()
        .map(|name| Scrutinee {
            name: None,
            expr: Expr::Var(name.clone()),
        })
        .collect();
    let matched = Expr::Match {
        scrutinees,
        alts,
        span,
        kind,
    };
    Expr::Lam(names, Box::new(matched), span)
}

/// The body of a `match some` alternative, `body`, which the alternative
/// at `bar` gives as `Some body`.
pub(crate) fn clause_some(body: Expr, bar: Span) -> Expr {
    let some = library_var("Std.Option.Some", Span::point(bar.file, body.span().start));
    Expr::App(Box::new(some), Box::new(body))
}

/// The body of a `matches` alternative written without one, at `bar`:
/// `True`.
pub(crate) fn clause_true(bar: Span) -> Expr {
    library_var("Std.Bool.True", Span::point(bar.file, bar.start))
}

/// `Exists _ (x => body)` for each parameter of `lambda`, the lambda after
/// `exists` at `keyword`: its layers are those whose span is `outer` (a
/// lambda in the body has a span of its own).
pub(crate) fn exists_chain(keyword: Span, lambda: Expr, outer: Span) -> Expr {
    let wrap = |param: Expr| {
        let exists = Expr::Var(Name {
            text: "Std.Exists".into(),
            span: keyword,
        });
        let applied = Expr::App(Box::new(exists), Box::new(Expr::Hole(keyword)));
        Expr::App(Box::new(applied), Box::new(param))
    };
    let mut lambda = lambda;
    let take = |b: &mut Box<Expr>| std::mem::replace(&mut **b, Expr::Prop(Span::NOWHERE));
    match &mut lambda {
        Expr::TypedLam(_, _, _, body, span) if *span == outer => {
            let inner = exists_chain(keyword, take(body), outer);
            **body = inner;
            wrap(lambda)
        }
        Expr::Lam(names, body, span) if *span == outer => {
            let span = *span;
            let mut inner = exists_chain(keyword, take(body), outer);
            let mut names = std::mem::take(names);
            while names.len() > 1 {
                let last = names.pop().expect("more than one");
                inner = wrap(Expr::Lam(vec![last], Box::new(inner), span));
            }
            wrap(Expr::Lam(names, Box::new(inner), span))
        }
        _ => lambda,
    }
}

/// A reference to a library name the compiler writes into a desugaring. Its
/// span is empty, which is how the elaborator tells it from one written.
pub(crate) fn library_var(path: &str, span: Span) -> Expr {
    Expr::Var(Name {
        text: path.into(),
        span,
    })
}

impl<'f> Lower<'f> {
    /// A block of more than one line: its lines before the last in front of
    /// the last ([`lines`]).
    #[inline(never)]
    pub(super) fn block(&self, node: Node<'f>) -> Lowering<Expr> {
        let mut stmts = node
            .children()
            .map(|line| self.statement(line))
            .collect::<Lowering<Vec<_>>>()?;
        let rest = match stmts.pop() {
            Some(Stmt::Expr(rest)) => rest,
            _ => return Err(Unsupported::Missing(NodeKind::Block, "an expression last")),
        };
        Ok(lines(stmts, rest))
    }

    /// One line of a block.
    fn statement(&self, line: Element<'f>) -> Lowering<Stmt> {
        match line {
            Element::Node(node) if node.kind() == NodeKind::Let => self.let_line(node),
            Element::Node(node) if matches!(node.kind(), NodeKind::Def | NodeKind::Theorem) => {
                self.local_def(node)
            }
            line => Ok(Stmt::Expr(self.expr(line)?)),
        }
    }

    /// A local `def` or `theorem`: a definition as at top level, which
    /// starts at its keyword, after any attributes.
    fn local_def(&self, node: Node<'f>) -> Lowering<Stmt> {
        let keyword = node
            .own_leaves()
            .find(|leaf| matches!(leaf.tok(), Tok::KwDef | Tok::KwTheorem));
        let keyword = required(keyword, node.kind(), "`def` or `theorem`")?;
        let mut decls = self.definition(node)?.into_iter();
        let signature = required(decls.next(), node.kind(), "its signature")?;
        let def = LocalDef {
            signature,
            equations: decls.collect(),
        };
        Ok(Stmt::Def(def, keyword.span()))
    }

    /// `let p := e` or `let p : T := e`.
    fn let_line(&self, node: Node<'f>) -> Lowering<Stmt> {
        let kind = NodeKind::Let;
        let keyword = required(node.first_leaf_is(&Tok::KwLet), kind, "`let`")?;
        let pattern = required(node.after(&Tok::KwLet), kind, "its pattern")?;
        let pattern = self.pattern(pattern)?;
        let ty = match node.leaf(&Tok::Colon) {
            Some(_) => {
                let ty = required(node.after(&Tok::Colon), kind, "its type")?;
                Some(self.expr(ty)?)
            }
            None => None,
        };
        let value = required(node.after(&Tok::ColonEq), kind, "its value")?;
        let value = self.expr(value)?;
        Ok(match pattern {
            Pattern::Var(name) => Stmt::Let(name, ty, value, keyword.span()),
            pattern => Stmt::LetPattern(pattern, ty, value, keyword.span()),
        })
    }

    /// `let x := e; body`: the same tree as a block's `let` line and the
    /// lines after it.
    #[inline(never)]
    pub(super) fn let_expr(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::LetExpr;
        let line = required(node.child(NodeKind::Let), kind, "its `let`")?;
        let stmt = self.let_line(line)?;
        let body = required(node.after(&Tok::Semi), kind, "its body")?;
        Ok(bind_let(stmt, self.expr(body)?))
    }

    /// `a; b`
    #[inline(never)]
    pub(super) fn seq(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::Seq;
        let first = required(node.children().next(), kind, "its first expression")?;
        let rest = required(node.after(&Tok::Semi), kind, "its rest")?;
        Ok(Expr::Seq(
            Box::new(self.expr(first)?),
            Box::new(self.expr(rest)?),
        ))
    }

    /// `x (a, b) [t: Type] => e` ([`lambda_of`]).
    #[inline(never)]
    pub(super) fn lambda(&self, node: Node<'f>) -> Lowering<Expr> {
        self.lambda_parts(node, node.children())
    }

    /// The lambda whose parameters, `=>` and body are `parts`, the rest of
    /// `node`'s children: all of a `Lambda`'s, or an `Exists`'s after its
    /// keyword.
    fn lambda_parts(
        &self,
        node: Node<'f>,
        mut parts: impl Iterator<Item = Element<'f>>,
    ) -> Lowering<Expr> {
        let kind = node.kind();
        let mut params: Vec<LamParam> = Vec::new();
        let mut start = None;
        let body = loop {
            let part = required(parts.next(), kind, "`=>` and its body")?;
            start.get_or_insert(first_token(part)?);
            match part {
                Element::Leaf(leaf) => match leaf.tok() {
                    Tok::FatArrow => break required(parts.next(), kind, "its body")?,
                    Tok::Underscore => {
                        let name = Name {
                            text: "_".to_string(),
                            span: leaf.span(),
                        };
                        params.push(LamParam::Plain(name, None));
                    }
                    _ => {
                        let name = required(name(leaf), kind, "a parameter")?;
                        params.push(LamParam::Plain(name, None));
                    }
                },
                Element::Node(param) if param.kind() == NodeKind::LambdaParam => {
                    let Param::Named {
                        names,
                        ty,
                        implicit,
                        auto,
                        ..
                    } = self.param(param)?
                    else {
                        return Err(Unsupported::Missing(kind, "a named parameter"));
                    };
                    let mode = match (implicit, auto) {
                        (false, _) => Mode::Explicit,
                        (true, false) => Mode::Implicit,
                        (true, true) => Mode::Auto,
                    };
                    for name in names {
                        params.push(LamParam::Typed(name, mode, ty.clone()));
                    }
                }
                // `((a, b): A)`: a pattern with a written type.
                Element::Node(typed) if typed.kind() == NodeKind::PatternTyped => {
                    let (pattern, ty) = self.pattern_typed(typed)?;
                    let name = Name {
                        text: format!("%arg{}", params.len()),
                        span: pattern.span(),
                    };
                    params.push(LamParam::TypedPattern(name, pattern, ty));
                }
                Element::Node(_) => match self.pattern(part)? {
                    Pattern::Var(name) => params.push(LamParam::Plain(name, None)),
                    pattern => {
                        let name = Name {
                            text: format!("%arg{}", params.len()),
                            span: pattern.span(),
                        };
                        params.push(LamParam::Plain(name, Some(pattern)));
                    }
                },
            }
        };
        if params.is_empty() {
            return Err(Unsupported::Missing(kind, "a parameter"));
        }
        let start = required(start, kind, "a parameter")?;
        let end = required(last_token(node), kind, "tokens")?;
        Ok(lambda_of(params, self.expr(body)?, start, end))
    }

    /// `exists (x: T) => P`: `Exists T ((x: T) => P)`, a layer for each
    /// parameter ([`exists_chain`]).
    #[inline(never)]
    pub(super) fn exists(&self, node: Node<'f>) -> Lowering<Expr> {
        let mut parts = node.children();
        let keyword = match parts.next() {
            Some(Element::Leaf(leaf)) if *leaf.tok() == Tok::KwExists => leaf.span(),
            _ => return Err(Unsupported::Missing(NodeKind::Exists, "`exists`")),
        };
        let lambda = self.lambda_parts(node, parts)?;
        let outer = lambda.span();
        Ok(exists_chain(keyword, lambda, outer))
    }

    /// `forall (x: T) => P`: the function type `(x: T) -> P` ([`forall_of`]).
    #[inline(never)]
    pub(super) fn forall(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::Forall;
        let mut parts = node.children();
        let keyword = match parts.next() {
            Some(Element::Leaf(leaf)) if *leaf.tok() == Tok::KwForall => leaf.span(),
            _ => return Err(Unsupported::Missing(kind, "`forall`")),
        };
        let mut groups: Vec<ForallGroup> = Vec::new();
        let body = loop {
            match required(parts.next(), kind, "`=>` and its body")? {
                Element::Leaf(leaf) => match leaf.tok() {
                    Tok::FatArrow => break required(parts.next(), kind, "its body")?,
                    Tok::Underscore => {
                        let name = Name {
                            text: "_".to_string(),
                            span: leaf.span(),
                        };
                        groups.push((vec![name], false, false, Expr::Hole(leaf.span())));
                    }
                    _ => {
                        let name = required(name(leaf), kind, "a parameter")?;
                        let hole = Expr::Hole(name.span);
                        groups.push((vec![name], false, false, hole));
                    }
                },
                Element::Node(param) if param.kind() == NodeKind::LambdaParam => {
                    let Param::Named {
                        names,
                        ty,
                        implicit,
                        auto,
                        ..
                    } = self.param(param)?
                    else {
                        return Err(Unsupported::Missing(kind, "a named parameter"));
                    };
                    groups.push((names, implicit, implicit && auto, ty));
                }
                Element::Node(_) => return Err(Unsupported::Missing(kind, "a parameter")),
            }
        };
        if groups.is_empty() {
            return Err(Unsupported::Missing(kind, "a parameter"));
        }
        Ok(forall_of(groups, self.expr(body)?, keyword))
    }

    /// `if c then a else b`, or `if h: c then …`, which binds a proof.
    #[inline(never)]
    pub(super) fn if_expr(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::If;
        let start = required(node.first_leaf_is(&Tok::KwIf), kind, "`if`")?.span();
        let (binder, cond) = match node.leaf(&Tok::Colon) {
            Some(_) => {
                let binder = match node.after(&Tok::KwIf) {
                    Some(Element::Leaf(leaf)) => name(leaf),
                    _ => None,
                };
                let binder = required(binder, kind, "its name")?;
                (Some(binder), node.after(&Tok::Colon))
            }
            None => (None, node.after(&Tok::KwIf)),
        };
        let cond = self.expr(required(cond, kind, "its condition")?)?;
        let then = self.expr(required(node.after(&Tok::KwThen), kind, "`then`")?)?;
        let otherwise = self.expr(required(node.after(&Tok::KwElse), kind, "`else`")?)?;
        let span = start.to(otherwise.span());
        Ok(Expr::If {
            binder,
            cond: Box::new(cond),
            then: Box::new(then),
            otherwise: Box::new(otherwise),
            span,
        })
    }

    /// `match | p, q => e | …`, `match some | …` or `matches | …`: a lambda
    /// over a `match` on its parameters ([`clause_lambda_of`]).
    #[inline(never)]
    pub(super) fn clause_lambda(&self, node: Node<'f>) -> Lowering<Expr> {
        let ckind = NodeKind::ClauseLambda;
        let keywords: Vec<Leaf<'f>> = node.own_leaves().collect();
        let first = required(keywords.first(), ckind, "`match` or `matches`")?;
        let last = keywords.last().expect("a first");
        let kind = match (first.tok(), keywords.len()) {
            (Tok::KwMatch, 1) => MatchKind::Clause,
            (Tok::KwMatch, _) => MatchKind::ClauseSome,
            _ => MatchKind::ClauseMatches,
        };
        let start = first.span();
        let keyword = start.to(last.span());
        let alts = node
            .child_nodes()
            .map(|arm| self.clause_arm(arm, kind))
            .collect::<Lowering<Vec<_>>>()?;
        if alts.is_empty() {
            return Err(Unsupported::Missing(ckind, "an alternative"));
        }
        let end = required(last_token(node), ckind, "tokens")?;
        Ok(clause_lambda_of(kind, alts, keyword, start, end))
    }

    /// `| p, q if c => e`, an alternative of a clause lambda of kind `kind`:
    /// its body wrapped in `Some` for `match some`, `True` if a `matches`
    /// alternative leaves it out, none for an absurd one.
    fn clause_arm(&self, arm: Node<'f>, kind: MatchKind) -> Lowering<Alt> {
        let akind = NodeKind::Arm;
        if arm.kind() != akind {
            return Err(Unsupported::Missing(
                NodeKind::ClauseLambda,
                "an alternative",
            ));
        }
        let bar = match arm.children().next() {
            Some(Element::Leaf(leaf)) if *leaf.tok() == Tok::Pipe => leaf.span(),
            _ => return Err(Unsupported::Missing(akind, "`|`")),
        };
        let (patterns, guard, body) = self.arm_parts(arm)?;
        let body = match (kind, body) {
            (MatchKind::ClauseMatches, None) => Some(clause_true(bar)),
            (MatchKind::ClauseSome, Some(body)) => Some(clause_some(body, bar)),
            (_, body) => body,
        };
        let end = required(last_token(arm), akind, "tokens")?;
        Ok(Alt {
            span: bar.to(end),
            patterns,
            guard,
            body,
        })
    }
}

/// An element's first token's span: where the parser starts a span it
/// builds with `start.to(…)`.
fn first_token(element: Element<'_>) -> Lowering<Span> {
    match element {
        Element::Leaf(leaf) => Ok(leaf.span()),
        Element::Node(node) => {
            let first = node.file().tokens().get(node.token_range().start);
            Ok(required(first, node.kind(), "tokens")?.span)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::oracle::{Report, compare};
    use crate::SourceMap;
    use crate::tree::NodeKind;

    fn report(text: &str) -> Report {
        let file = SourceMap::new().next_id();
        compare(file, text, crate::DEFAULT_STACK, true)
    }

    fn differences(report: &Report) -> Vec<String> {
        report
            .differences
            .iter()
            .map(|d| format!("{} at {}:\n{}", d.what, d.at, d.detail))
            .collect()
    }

    /// Each kind of lane L3, in the forms whose lowering depends on what
    /// surrounds it, comes out as the parser builds it, spans and hidden
    /// names included.
    #[test]
    fn binding_and_sections_lower_as_parsed() {
        let bodies = [
            "x => x",
            "_ => 0",
            "x y => f x y",
            "(x: Nat) => x",
            "(x y: Nat) z => x",
            "x (y: A) z => y",
            "[a: Type] (x: a) => x",
            "[auto h: P] [auto Ord a] => h",
            "f (x => x) y",
            "xs.map .f",
            "xs.map .f.g",
            "xs.map (.f a b)",
            ".f a",
            ".f().g",
            ".f () x",
            ".f -1 C { x = 1 } y",
            "(.id == id)",
            "(.f a == b && c)",
            "(.f |> g)",
            "xs |> .drop 1",
            "xs |> .f.g()",
            "(+ 1) (k +) (&&) (-)",
            "(== 'S') (> 1) (x >=)",
            "(in xs) (∉ xs) (x ∈)",
            "(<-> p) (|| a && b && c) (a ||) (a < b &&)",
            "∀ n => n = n",
            "∀ (x y: Nat) [a: Type] [auto h: P] _ => x = y",
            "forall n => exists m => n < m",
            "∃ (a b: Nat) c => a = b",
            "∃ x => ∃ y => x = y",
            "if c then a else b",
            "if h: c then a else if d then b else e",
            "match | A, b => b | _, _ => c",
            "match | x if x > 0 => 1 | _ => 0",
            "match | () ",
            "match some | A => 1 | B => 2",
            "(let x := 1; x + 1)",
            "(let _ := 1; 2)",
            "(let C := c; 2)",
            "(let x : Nat := 1; x)",
            "(a; b; c)",
            "(a; let x := 1; x)",
            "(a, b) x {c, d} => a",
            "((a, b): P) (y: A) => a",
            "(let (a, b) := p; a)",
            "(let (a, b) : P := p; a)",
            "(let MkPair a b := p; a)",
            "match | (a, b), [c, ..d] => a",
        ];
        let mut text: String = bodies
            .iter()
            .enumerate()
            .map(|(i, body)| format!("test \"{i}\" := {body}\n"))
            .collect();
        text.push_str(
            "def f (x: Nat): Nat :=\n  let y: Nat :=\n    let z := x\n    z\n  @[tailrec] def g (n: \
             Nat): Nat := n\n  theorem t: g 0 = 0 := rfl\n  def k: Nat := 1\n  g y; k\n  let w := \
             k\n  print w\n  def m: Nat := w\n  m\n\
             def p: Nat -> Bool := matches\n  | 0\n  | 1 => False\n\
             def q: Nat -> Nat := match\n  | 0 => 1\n  | n => n\n",
        );
        let report = report(&text);
        assert_eq!(differences(&report), Vec::<String>::new());
        assert_eq!(report.unsupported, []);
        let mut kinds = vec![NodeKind::Test; bodies.len()];
        kinds.extend([NodeKind::Def; 3]);
        assert_eq!(report.lowered, kinds);
        assert_eq!(report.expressions.unsupported, []);
    }
}
