//! The span-containment check: every span the compiler's tree
//! ([`crate::ast`]) carries is the token range of a node of the lossless
//! tree, or a single token. It is how stage 1 shows the lossless tree has a
//! node for everything the compiler's tree talks about, which the lowering
//! (docs/proposals/syntax-tree-architecture.md, step 3) will need; and it
//! guards the parser's `operand_start`, which assumes every operand of more
//! than one token is marked.
//!
//! Two things about the compiler's tree make room for leeway. It has no
//! node for brackets, so a span it works out from its parts can stop inside
//! them (`f (g x)` from `f` to `x`): a span is found if adding back the
//! brackets at its ends makes it a node. And some of its spans are not
//! anything written: the parser expands shorthand, and the pieces it makes
//! up get spans of their own. The walk below knows each place that can
//! happen and gives the span its reason ([`Synthetic`]); such a span is
//! still looked for, and only if it isn't found is it counted under its
//! reason instead of as a miss. Every other span must be found.

use super::{NodeKind, SyntaxFile};
use crate::Span;
use crate::ast::{
    Alt, Attribute, BinOp, Binder, CHAIN, Clause, Decl, Expr, Guard, MatchKind, Module, Name,
    Pattern, SECTION,
};
use crate::lexer::Tok;
use std::collections::{BTreeMap, BTreeSet};

/// What [`SyntaxFile::check_spans`] found in one file.
#[derive(Clone, Debug, Default)]
pub struct SpanCheck {
    /// Spans found, or missed with no reason.
    pub checked: usize,
    /// Spans of the parser's own making that are no node, by kind.
    pub synthetic: BTreeMap<Synthetic, usize>,
    /// Spans in declarations that didn't parse, which the compiler's tree
    /// keeps part of (a signature whose body failed) and whose lossless
    /// tree is one `Error` node.
    pub unparsed: usize,
    /// Spans that are no node's range and not a single token.
    pub misses: Vec<SpanMiss>,
}

/// A span of the compiler's tree that matches no node of the lossless tree.
#[derive(Clone, Debug)]
pub struct SpanMiss {
    /// Where in the compiler's tree it is, as `Expr::Let` or `Alt`.
    pub what: &'static str,
    pub span: Span,
}

/// Why a span may be no node: the construct it belongs to was made up by
/// the parser when it expanded something written, or its span was worked
/// out from such a part.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Synthetic {
    /// An empty span: a name or alternative the parser adds (the
    /// `_ => None` of `match some`, a clause lambda's parameters).
    Empty,
    /// `f a b` is `App(App(f, a), b)`: the inner applications are parts of
    /// the one `App` node.
    PartialApp,
    /// `(a, b, c)` is `(a, (b, c))` and `[a, b, ..r]` is `a :: (b :: r)`:
    /// the inner ones are parts of the one `Tuple` or `PatternList` node.
    Nested,
    /// A line of a block is the compiler's `Let`, `Seq` or local
    /// definitions with the rest of the block inside it: its span runs from
    /// the line to the end of the block.
    BlockRest,
    /// An application of a function the parser writes at an operator
    /// ([`OPERATOR_HEADS`]): `p ↔ q` is `Std.Iff p q`, so the
    /// application's span starts at the `↔`.
    OperatorHead,
    /// A name the parser makes up (`%arg0`, `%section`, `%chain…`), at the
    /// place it stands for, which may be no one construct: a clause
    /// lambda's parameters are at its keywords, `match some`.
    Generated,
    /// The last alternative of `match some | …` or `matches | …`, `_ =>
    /// None` or `_ => False`, which the parser adds; its wildcards are at
    /// the keywords.
    Added,
    /// A data type's span starts at `type`, after its attributes, which the
    /// declaration's node includes.
    Attributes,
    /// `a > b` is `b < a`: the span worked out from its first and last
    /// parts runs from inside `b` to the end of `a` when `b` is compound.
    Flipped,
    /// `∃ (x: A) => P` is `Std.Exists _ ((x: A) => P)`: the lambda starts
    /// at its parameter, after the `∃`.
    Exists,
    /// A chain `a ≤ b < c` binds its middle operands with a `let` and joins
    /// the comparisons with `∧`.
    Chain,
    /// A method section `.f a` is the lambda `%section => %section.f a`.
    Section,
    /// `"a${x}b"` is `"a" ++ x ++ "b"`: the joins span from one piece to the
    /// end of the text, which is no node.
    Interpolation,
    /// `let p := e` with a pattern, and a lambda's pattern parameters, are
    /// a one-arm `match` on the value.
    PatternMatch,
    /// A definition is a `Decl::Signature`, from its keyword to the end of
    /// its type, whose type is a `Pi` for each of the header's parameters,
    /// from that parameter to the end; and a `Decl::Equation` for its `:=`
    /// body, from its name to the body's end (an arm's is the arm).
    Header,
}

/// A part of the compiler's tree waiting to be walked. An expression or
/// pattern comes with the reason its own span may be made up, if the
/// construct around it makes it one.
enum Item<'a> {
    Expr(&'a Expr, Option<Synthetic>),
    Pattern(&'a Pattern, Option<Synthetic>),
    Decl(&'a Decl),
}

/// A span to look for: where it is, and why it may be made up, if it may.
type Found = (&'static str, Span, Option<Synthetic>);

struct Walk<'a> {
    todo: Vec<Item<'a>>,
    spans: Vec<Found>,
}

impl<'a> Walk<'a> {
    fn span(&mut self, what: &'static str, span: Span) {
        self.spans.push((what, span, None));
    }

    fn made(&mut self, what: &'static str, span: Span, why: Synthetic) {
        self.spans.push((what, span, Some(why)));
    }

    fn tagged(&mut self, what: &'static str, span: Span, why: Option<Synthetic>) {
        self.spans.push((what, span, why));
    }

    fn name(&mut self, what: &'static str, name: &Name) {
        let made = name.text.starts_with('%').then_some(Synthetic::Generated);
        self.tagged(what, name.span, made);
    }

    /// A span worked out from `part` as its last part, which may make it
    /// wrong ([`made_from`]).
    fn ending(&mut self, what: &'static str, span: Span, part: &Expr) {
        self.tagged(what, span, made_from(part));
    }

    fn expr(&mut self, expr: &'a Expr) {
        self.todo.push(Item::Expr(expr, None));
    }

    fn inner(&mut self, expr: &'a Expr, why: Synthetic) {
        self.todo.push(Item::Expr(expr, Some(why)));
    }

    fn pattern(&mut self, pattern: &'a Pattern) {
        self.todo.push(Item::Pattern(pattern, None));
    }

    fn attrs(&mut self, attrs: &'a [Attribute]) {
        for attr in attrs {
            self.span("Attribute", attr.span);
            self.name("Attribute name", &attr.name);
            if let Some((_, span)) = &attr.arg {
                self.span("Attribute argument", *span);
            }
        }
    }

    fn binders(&mut self, binders: &'a [Binder]) {
        for binder in binders {
            for name in &binder.names {
                self.name("Binder name", name);
            }
            self.expr(&binder.ty);
            self.attrs(&binder.attrs);
        }
    }

    fn guard(&mut self, guard: &'a Guard) {
        self.ending("Guard", guard.span, &guard.cond);
        if let Some(binder) = &guard.binder {
            self.name("Guard binder", binder);
        }
        self.expr(&guard.cond);
    }

    /// An alternative of a `match`; `added` if it is the last of a `match
    /// some` or `matches`, which the parser adds.
    fn alt(&mut self, alt: &'a Alt, why: Option<Synthetic>, added: bool) {
        let why = why.or_else(|| alt.body.as_ref().and_then(made_from));
        self.tagged("Alt", alt.span, why);
        for pattern in &alt.patterns {
            if added {
                self.todo
                    .push(Item::Pattern(pattern, Some(Synthetic::Added)));
            } else {
                self.pattern(pattern);
            }
        }
        if let Some(guard) = &alt.guard {
            self.guard(guard);
        }
        if let Some(body) = &alt.body {
            self.expr(body);
        }
    }

    fn clauses(&mut self, clauses: &'a [Clause]) {
        for clause in clauses {
            match clause {
                Clause::Return { var, body } => {
                    self.name("Clause variable", var);
                    self.expr(body);
                }
                Clause::Op { op, arg, k, body } => {
                    self.name("Clause operation", op);
                    self.pattern(arg);
                    self.name("Clause continuation", k);
                    self.expr(body);
                }
            }
        }
    }

    fn walk_expr(&mut self, expr: &'a Expr, why: Option<Synthetic>) {
        let what = expr_kind(expr);
        let why = why.or_else(|| made_from(expr));
        match expr {
            Expr::Var(name) => {
                let made = name.text.starts_with('%').then_some(Synthetic::Generated);
                self.tagged(what, name.span, why.or(made));
            }
            Expr::Num(_, span)
            | Expr::Float(_, span)
            | Expr::Str(_, span)
            | Expr::Include(_, span)
            | Expr::Char(_, span)
            | Expr::Type(_, span)
            | Expr::Prop(span)
            | Expr::Hole(span)
            | Expr::Goal(span)
            | Expr::Unit(span) => self.tagged(what, *span, why),
            Expr::App(a, b) => {
                let operator = matches!(head(expr), Expr::Var(name)
                    if OPERATOR_HEADS.contains(&name.text.as_str()));
                let exists = matches!(head(expr), Expr::Var(name) if name.text == "Std.Exists");
                let made = operator.then_some(Synthetic::OperatorHead);
                self.tagged(what, expr.span(), why.or(made));
                if exists && matches!(**b, Expr::Lam(..) | Expr::TypedLam(..)) {
                    self.inner(b, Synthetic::Exists);
                } else {
                    self.expr(b);
                }
                match &**a {
                    Expr::App(..) if operator => self.inner(a, Synthetic::OperatorHead),
                    Expr::App(..) => self.inner(a, Synthetic::PartialApp),
                    _ => self.expr(a),
                }
            }
            Expr::Arrow(a, b) | Expr::Pipe(a, b) => {
                self.tagged(what, expr.span(), why);
                self.expr(a);
                self.expr(b);
            }
            Expr::Seq(a, b) => {
                self.tagged(what, expr.span(), why.or(Some(Synthetic::BlockRest)));
                self.expr(a);
                self.expr(b);
            }
            Expr::Binary(op, a, b) => {
                let flipped = a.span().start > b.span().start;
                self.tagged(
                    what,
                    expr.span(),
                    why.or(flipped.then_some(Synthetic::Flipped)),
                );
                if let BinOp::In(span) = op {
                    self.span("BinOp::In", *span);
                }
                // The pieces of an interpolated text, joined.
                if why == Some(Synthetic::Interpolation) {
                    self.inner(a, Synthetic::Interpolation);
                    self.inner(b, Synthetic::Interpolation);
                } else if *op == BinOp::And && is_chain(a, b) {
                    self.inner(a, Synthetic::Chain);
                    self.inner(b, Synthetic::Chain);
                } else {
                    self.expr(a);
                    self.expr(b);
                }
            }
            Expr::Effect(row, b) => {
                self.tagged(what, expr.span(), why);
                self.span("Row", row.span);
                for ability in &row.abilities {
                    self.expr(ability);
                }
                if let Some(tail) = &row.tail {
                    self.name("Row tail", tail);
                }
                self.expr(b);
            }
            Expr::Interpolated(e, span) => {
                self.tagged(what, *span, why);
                self.inner(e, Synthetic::Interpolation);
            }
            Expr::Bracketed(e, span) | Expr::Neg(e, span, _) | Expr::Spread(e, span) => {
                self.tagged(what, *span, why);
                self.expr(e);
            }
            Expr::Lam(names, body, span) => {
                let section = matches!(names.as_slice(), [name] if name.text == SECTION);
                self.tagged(what, *span, why.or(section.then_some(Synthetic::Section)));
                for name in names {
                    self.name("Lam parameter", name);
                }
                self.expr(body);
            }
            Expr::TypedLam(name, _, ty, body, span) => {
                self.tagged(what, *span, why);
                self.name("TypedLam parameter", name);
                self.expr(ty);
                self.expr(body);
            }
            Expr::Pi {
                names,
                dom,
                cod,
                span,
                ..
            } => {
                self.tagged(what, *span, why);
                for name in names {
                    self.name("Pi parameter", name);
                }
                self.expr(dom);
                self.expr(cod);
            }
            Expr::NamedArg(name, e, span, _) => {
                self.tagged(what, *span, why);
                self.name("NamedArg name", name);
                self.expr(e);
            }
            Expr::If {
                binder,
                cond,
                then,
                otherwise,
                span,
            } => {
                self.tagged(what, *span, why);
                if let Some(binder) = binder {
                    self.name("If binder", binder);
                }
                self.expr(cond);
                self.expr(then);
                self.expr(otherwise);
            }
            Expr::Ann(a, b, span) => {
                self.tagged(what, *span, why);
                self.expr(a);
                self.expr(b);
            }
            Expr::Tuple(a, b, span) => {
                self.tagged(what, *span, why);
                self.expr(a);
                if matches!(**b, Expr::Tuple(..)) {
                    self.inner(b, Synthetic::Nested);
                } else {
                    self.expr(b);
                }
            }
            Expr::List(items, span) => {
                self.tagged(what, *span, why);
                for item in items {
                    self.expr(item);
                }
            }
            Expr::Let {
                name,
                ty,
                value,
                body,
                span,
            } => {
                let chain = name.text.starts_with(CHAIN);
                let made = if chain {
                    Synthetic::Chain
                } else {
                    Synthetic::BlockRest
                };
                self.tagged(what, *span, why.or(Some(made)));
                self.name("Let name", name);
                if let Some(ty) = ty {
                    self.expr(ty);
                }
                self.expr(value);
                self.expr(body);
            }
            Expr::LocalDefs { defs, body, span } => {
                self.tagged(what, *span, why.or(Some(Synthetic::BlockRest)));
                for def in defs {
                    self.todo.push(Item::Decl(&def.signature));
                    for equation in &def.equations {
                        self.todo.push(Item::Decl(equation));
                    }
                }
                self.expr(body);
            }
            Expr::Handle {
                body,
                clauses,
                span,
            } => {
                self.tagged(what, *span, why);
                self.expr(body);
                self.clauses(clauses);
            }
            Expr::Reify {
                thunk,
                clauses,
                span,
            } => {
                self.tagged(what, *span, why);
                self.expr(thunk);
                self.clauses(clauses);
            }
            Expr::Induct { call, alts, span } => {
                self.tagged(what, *span, why);
                self.expr(call);
                for alt in alts {
                    self.ending("InductAlt", alt.span, &alt.body);
                    self.name("InductAlt case", &alt.case);
                    for binder in &alt.binders {
                        self.name("InductAlt binder", binder);
                    }
                    self.expr(&alt.body);
                }
            }
            Expr::Match {
                scrutinees,
                alts,
                span,
                kind,
            } => {
                let made = matches!(kind, MatchKind::Let | MatchKind::Lambda)
                    .then_some(Synthetic::PatternMatch);
                self.tagged(what, *span, why.or(made));
                for scrutinee in scrutinees {
                    if let Some(name) = &scrutinee.name {
                        self.name("Scrutinee name", name);
                    }
                    match &scrutinee.expr {
                        // `let (a, b): T := e` matches `(e : T)`, from `T` to `e`.
                        e @ Expr::Ann(..) if made.is_some() => {
                            self.inner(e, Synthetic::PatternMatch)
                        }
                        e => self.expr(e),
                    }
                }
                let added = matches!(kind, MatchKind::ClauseSome | MatchKind::ClauseMatches);
                for (i, alt) in alts.iter().enumerate() {
                    self.alt(alt, made, added && i + 1 == alts.len());
                }
            }
            Expr::Record { base, fields, span } => {
                self.tagged(what, *span, why);
                if let Some(base) = base {
                    self.expr(base);
                }
                for (name, value) in fields {
                    self.name("Record field", name);
                    self.expr(value);
                }
            }
            Expr::CtorFields {
                ctor, fields, span, ..
            } => {
                self.tagged(what, *span, why);
                self.name("CtorFields constructor", ctor);
                for (name, value) in fields {
                    self.name("CtorFields field", name);
                    self.expr(value);
                }
            }
            Expr::Calc { first, steps, span } => {
                self.tagged(what, *span, why);
                self.expr(first);
                for step in steps {
                    self.ending(
                        "CalcStep",
                        step.span,
                        step.proof.as_ref().unwrap_or(&step.rhs),
                    );
                    self.span("CalcStep relation", step.rel_span);
                    self.expr(&step.rhs);
                    if let Some(proof) = &step.proof {
                        self.expr(proof);
                    }
                }
            }
            Expr::Rewrite {
                rules,
                target,
                body,
                keyword,
                at,
                in_,
                span,
            } => {
                self.tagged(what, *span, why);
                self.span("Rewrite keyword", *keyword);
                for rule in rules {
                    self.ending("RewriteRule", rule.span, &rule.proof);
                    self.expr(&rule.proof);
                }
                if let Some(target) = target {
                    self.expr(target);
                }
                if let Some(at) = at {
                    self.span("Rewrite at", *at);
                }
                if let Some(in_) = in_ {
                    self.span("Rewrite in", *in_);
                }
                if let Some(body) = body {
                    self.expr(body);
                }
            }
            Expr::Omega { facts, span } | Expr::Ring { facts, span } => {
                self.tagged(what, *span, why);
                for fact in facts {
                    self.expr(fact);
                }
            }
            Expr::Cases { body, span } => {
                self.tagged(what, *span, why);
                if let Some(body) = body {
                    self.expr(body);
                }
            }
            Expr::Field(e, name) => {
                // `xs |> .f` is `xs.f`, from `xs` to `f`, with the `|> .`
                // between: the receiver doesn't end at the `.` before `f`.
                // (Brackets around the receiver also put a gap there.)
                let piped = e.span().end + 1 != name.span.start;
                self.tagged(
                    what,
                    expr.span(),
                    why.or(piped.then_some(Synthetic::Section)),
                );
                self.name("Field name", name);
                self.expr(e);
            }
        }
    }

    fn walk_pattern(&mut self, pattern: &'a Pattern, why: Option<Synthetic>) {
        let what = pattern_kind(pattern);
        let sub = |walk: &mut Self, p: &'a Pattern| walk.pattern(p);
        match pattern {
            Pattern::Var(name) => self.tagged(what, name.span, why),
            Pattern::Wildcard(span)
            | Pattern::Absurd(span)
            | Pattern::Num(_, span)
            | Pattern::NegNum(_, span)
            | Pattern::Char(_, span)
            | Pattern::Nil(span) => self.tagged(what, *span, why),
            Pattern::Ctor(name, args, span) => {
                self.tagged(what, *span, why);
                self.name("Pattern::Ctor name", name);
                for arg in args {
                    sub(self, arg);
                }
            }
            Pattern::Tuple(a, b, span) | Pattern::Cons(a, b, span) => {
                self.tagged(what, *span, why);
                sub(self, a);
                if matches!(
                    (pattern, &**b),
                    (Pattern::Tuple(..), Pattern::Tuple(..))
                        | (Pattern::Cons(..), Pattern::Cons(..))
                ) {
                    self.todo.push(Item::Pattern(b, Some(Synthetic::Nested)));
                } else {
                    sub(self, b);
                }
            }
            Pattern::Named(name, p, span) => {
                self.tagged(what, *span, why);
                self.name("Pattern::Named name", name);
                sub(self, p);
            }
            Pattern::Record { fields, span, .. } => {
                self.tagged(what, *span, why);
                for (name, p) in fields {
                    self.name("Pattern::Record field", name);
                    sub(self, p);
                }
            }
            Pattern::CtorFields {
                ctor, fields, span, ..
            } => {
                self.tagged(what, *span, why);
                self.name("Pattern::CtorFields constructor", ctor);
                for (name, p) in fields {
                    self.name("Pattern::CtorFields field", name);
                    sub(self, p);
                }
            }
            Pattern::Or(ps, span) => {
                self.tagged(what, *span, why);
                for p in ps {
                    sub(self, p);
                }
            }
        }
    }

    fn walk_decl(&mut self, decl: &'a Decl) {
        match decl {
            Decl::Data {
                name,
                params,
                indices,
                sort,
                ctors,
                attrs,
                span,
                ..
            } => {
                let made = (!attrs.is_empty()).then_some(Synthetic::Attributes);
                self.tagged("Decl::Data", *span, made);
                self.name("Decl::Data name", name);
                self.binders(params);
                for (name, ty) in indices {
                    if let Some(name) = name {
                        self.name("Data index name", name);
                    }
                    self.expr(ty);
                }
                if let Some(sort) = sort {
                    self.expr(sort);
                }
                for ctor in ctors {
                    self.attrs(&ctor.attrs);
                    self.name("CtorDecl name", &ctor.name);
                    self.binders(&ctor.fields);
                    for default in ctor.defaults.iter().flatten() {
                        self.expr(default);
                    }
                    if let Some(result) = &ctor.result {
                        self.expr(result);
                    }
                }
                self.attrs(attrs);
            }
            Decl::Signature {
                name,
                ty,
                decreasing,
                unfolding,
                defaults,
                attrs,
                span,
                ..
            } => {
                self.made("Decl::Signature", *span, Synthetic::Header);
                self.name("Decl::Signature name", name);
                // The header's parameters, in front of the result type.
                let mut ty = ty;
                loop {
                    match ty {
                        Expr::Pi {
                            names,
                            dom,
                            cod,
                            span,
                            ..
                        } => {
                            self.made("Expr::Pi", *span, Synthetic::Header);
                            for name in names {
                                self.name("Pi parameter", name);
                            }
                            self.expr(dom);
                            ty = cod;
                        }
                        Expr::Arrow(unit, cod) if matches!(**unit, Expr::Unit(_)) => {
                            self.made("Expr::Arrow", ty.span(), Synthetic::Header);
                            self.expr(unit);
                            ty = cod;
                        }
                        _ => break,
                    }
                }
                self.expr(ty);
                if let Some(decreasing) = decreasing {
                    self.expr(decreasing);
                }
                for name in unfolding {
                    self.name("Unfolding name", name);
                }
                for default in defaults.iter().flatten() {
                    self.expr(default);
                }
                self.attrs(attrs);
            }
            Decl::Test { expr, span, .. } => {
                self.ending("Decl::Test", *span, expr);
                self.expr(expr);
            }
            Decl::Ability {
                name,
                params,
                ops,
                span,
            } => {
                self.span("Decl::Ability", *span);
                self.name("Decl::Ability name", name);
                self.binders(params);
                for (name, ty) in ops {
                    self.name("Ability operation", name);
                    self.expr(ty);
                }
            }
            Decl::Equation {
                name,
                patterns,
                guard,
                rhs,
                arm,
                span,
            } => {
                // A `:=` body's equation runs from the name to the body's end.
                let made = arm.is_none().then_some(Synthetic::Header);
                let made = made.or_else(|| rhs.as_ref().and_then(made_from));
                self.tagged("Decl::Equation", *span, made);
                self.name("Decl::Equation name", name);
                // The alternative `match some` adds is an equation too, in
                // `def f: A -> Option B := match some | …`: empty, as it is.
                let added = (span.start == span.end).then_some(Synthetic::Added);
                for pattern in patterns {
                    self.todo.push(Item::Pattern(pattern, added));
                }
                if let Some(guard) = guard {
                    self.guard(guard);
                }
                if let Some(rhs) = rhs {
                    self.expr(rhs);
                }
            }
        }
    }
}

/// The library functions the parser writes at an operator: `p ↔ q` is
/// `Std.Iff p q`, `x ∉ xs` is `Std.Bool.not (x ∈ xs)`, and a step `_ = x :=
/// p` of a `calc` written with `>` is turned round with `Std.Eq.sym p`, the
/// function at the `=`.
const OPERATOR_HEADS: &[&str] = &["Std.Iff", "Std.Bool.not", "Std.Eq.sym"];

/// Why `expr`'s span, worked out from its first and last parts, may not
/// be what was written: one of those parts is made up. A chain's `let`
/// spans only the operand it binds (`x => a ≤ f x ≤ b` ends at `f x`); a
/// flipped comparison's parts are the other way round; an operator's
/// function is at the operator (`x ∉ xs` starts at the `∉`).
fn made_from(expr: &Expr) -> Option<Synthetic> {
    let flipped = |a: &Expr, b: &Expr| a.span().start > b.span().start;
    let mut first = expr;
    loop {
        first = match first {
            Expr::Binary(_, a, b) if flipped(a, b) => return Some(Synthetic::Flipped),
            Expr::App(a, _)
            | Expr::Arrow(a, _)
            | Expr::Binary(_, a, _)
            | Expr::Pipe(a, _)
            | Expr::Seq(a, _) => a,
            Expr::Var(name) if OPERATOR_HEADS.contains(&name.text.as_str()) => {
                return Some(Synthetic::OperatorHead);
            }
            Expr::Let { name, .. } if name.text.starts_with(CHAIN) => {
                return Some(Synthetic::Chain);
            }
            _ => break,
        };
    }
    let mut last = expr;
    loop {
        last = match last {
            Expr::Binary(_, a, b) if flipped(a, b) => return Some(Synthetic::Flipped),
            Expr::App(_, b)
            | Expr::Arrow(_, b)
            | Expr::Binary(_, _, b)
            | Expr::Pipe(_, b)
            | Expr::Seq(_, b)
            | Expr::Effect(_, b)
            | Expr::Lam(_, b, _)
            | Expr::TypedLam(_, _, _, b, _) => b,
            Expr::Pi { cod, .. } => cod,
            Expr::If { otherwise, .. } => otherwise,
            Expr::Let { name, .. } if name.text.starts_with(CHAIN) => {
                return Some(Synthetic::Chain);
            }
            Expr::Let { body, .. } | Expr::LocalDefs { body, .. } => body,
            _ => return None,
        };
    }
}

/// The function at the head of an application `f a b`.
fn head(mut expr: &Expr) -> &Expr {
    while let Expr::App(f, _) = expr {
        expr = f;
    }
    expr
}

/// Whether `a && b` is two links of a chain `a ≤ b < c`, as the parser
/// expands it: the two comparisons share their middle operand, the same
/// expression (or the `%chain` name it is bound to) with the same span. A
/// written `a ≤ b && b < c` has two `b`s, at different places.
fn is_chain(a: &Expr, b: &Expr) -> bool {
    fn operands(e: &Expr) -> Option<(Span, Span)> {
        match e {
            Expr::Binary(BinOp::Eq | BinOp::Ne | BinOp::EqEq | BinOp::Lt | BinOp::Le, l, r) => {
                Some((l.span(), r.span()))
            }
            _ => None,
        }
    }
    // The first link on the right: past the `let %chain` that binds its
    // middle operand, and down the left of a longer chain.
    let mut first = b;
    loop {
        match first {
            Expr::Let { name, body, .. } if name.text.starts_with(CHAIN) => first = body,
            Expr::Binary(BinOp::And, l, _) => first = l,
            _ => break,
        }
    }
    match (operands(a), operands(first)) {
        (Some((al, ar)), Some((bl, br))) => [al, ar].iter().any(|s| *s == bl || *s == br),
        _ => false,
    }
}

fn expr_kind(expr: &Expr) -> &'static str {
    match expr {
        Expr::Var(_) => "Expr::Var",
        Expr::Num(..) => "Expr::Num",
        Expr::Float(..) => "Expr::Float",
        Expr::Str(..) => "Expr::Str",
        Expr::Include(..) => "Expr::Include",
        Expr::Char(..) => "Expr::Char",
        Expr::Type(..) => "Expr::Type",
        Expr::Prop(_) => "Expr::Prop",
        Expr::App(..) => "Expr::App",
        Expr::Bracketed(..) => "Expr::Bracketed",
        Expr::Lam(..) => "Expr::Lam",
        Expr::TypedLam(..) => "Expr::TypedLam",
        Expr::Pi { .. } => "Expr::Pi",
        Expr::NamedArg(..) => "Expr::NamedArg",
        Expr::Hole(_) => "Expr::Hole",
        Expr::Goal(_) => "Expr::Goal",
        Expr::Arrow(..) => "Expr::Arrow",
        Expr::Binary(..) => "Expr::Binary",
        Expr::Pipe(..) => "Expr::Pipe",
        Expr::Neg(..) => "Expr::Neg",
        Expr::Interpolated(..) => "Expr::Interpolated",
        Expr::If { .. } => "Expr::If",
        Expr::Ann(..) => "Expr::Ann",
        Expr::List(..) => "Expr::List",
        Expr::Spread(..) => "Expr::Spread",
        Expr::Unit(_) => "Expr::Unit",
        Expr::Tuple(..) => "Expr::Tuple",
        Expr::Effect(..) => "Expr::Effect",
        Expr::Let { .. } => "Expr::Let",
        Expr::Seq(..) => "Expr::Seq",
        Expr::LocalDefs { .. } => "Expr::LocalDefs",
        Expr::Handle { .. } => "Expr::Handle",
        Expr::Reify { .. } => "Expr::Reify",
        Expr::Induct { .. } => "Expr::Induct",
        Expr::Match { .. } => "Expr::Match",
        Expr::Record { .. } => "Expr::Record",
        Expr::CtorFields { .. } => "Expr::CtorFields",
        Expr::Calc { .. } => "Expr::Calc",
        Expr::Rewrite { .. } => "Expr::Rewrite",
        Expr::Omega { .. } => "Expr::Omega",
        Expr::Cases { .. } => "Expr::Cases",
        Expr::Ring { .. } => "Expr::Ring",
        Expr::Field(..) => "Expr::Field",
    }
}

fn pattern_kind(pattern: &Pattern) -> &'static str {
    match pattern {
        Pattern::Var(_) => "Pattern::Var",
        Pattern::Wildcard(_) => "Pattern::Wildcard",
        Pattern::Absurd(_) => "Pattern::Absurd",
        Pattern::Num(..) => "Pattern::Num",
        Pattern::NegNum(..) => "Pattern::NegNum",
        Pattern::Char(..) => "Pattern::Char",
        Pattern::Ctor(..) => "Pattern::Ctor",
        Pattern::Tuple(..) => "Pattern::Tuple",
        Pattern::Nil(_) => "Pattern::Nil",
        Pattern::Cons(..) => "Pattern::Cons",
        Pattern::Named(..) => "Pattern::Named",
        Pattern::Record { .. } => "Pattern::Record",
        Pattern::CtorFields { .. } => "Pattern::CtorFields",
        Pattern::Or(..) => "Pattern::Or",
    }
}

/// Every span `module` carries, with where it is.
fn module_spans(module: &Module) -> Vec<Found> {
    let mut walk = Walk {
        todo: module.decls.iter().rev().map(Item::Decl).collect(),
        spans: Vec::new(),
    };
    if let Some(namespace) = &module.namespace {
        walk.span("Namespace", namespace.span);
        walk.name("Namespace path", &namespace.path);
    }
    for import in &module.imports {
        walk.span("Import", import.span);
        walk.name("Import path", &import.path);
        if let Some(everything) = import.everything {
            walk.span("Import everything", everything);
        }
        for item in &import.items {
            walk.name("Import item", &item.name);
            if let Some(alias) = &item.alias {
                walk.name("Import alias", alias);
            }
        }
    }
    while let Some(item) = walk.todo.pop() {
        match item {
            Item::Expr(e, why) => walk.walk_expr(e, why),
            Item::Pattern(p, why) => walk.walk_pattern(p, why),
            Item::Decl(d) => walk.walk_decl(d),
        }
    }
    walk.spans
}

impl SyntaxFile {
    /// Checks that every span in `module`, the compiler's tree from the
    /// same parse, is the token range of one of this tree's nodes or a
    /// single token, except the spans of constructs
    /// the parser made up ([`Synthetic`]).
    pub fn check_spans(&self, module: &Module) -> SpanCheck {
        // Token indices by the byte they start or end at.
        let mut starts = BTreeMap::new();
        let mut ends = BTreeMap::new();
        for (i, token) in self.tokens.iter().enumerate() {
            starts.insert(token.span.start, i);
            ends.insert(token.span.end, i + 1);
        }
        let ranges: BTreeSet<(usize, usize)> = self
            .decls
            .iter()
            .flat_map(|decl| &decl.nodes)
            .map(|node| (node.start as usize, node.end as usize))
            .collect();
        // Token `i` is a bracket, opening or closing.
        let bracket = |i: usize, open: bool| {
            self.tokens.get(i).is_some_and(|t| {
                if open {
                    matches!(t.tok, Tok::LParen | Tok::LBracket)
                } else {
                    matches!(t.tok, Tok::RParen | Tok::RBracket)
                }
            })
        };
        let is_node = |start: usize, end: usize| end == start + 1 || ranges.contains(&(start, end));
        // The compiler's tree has no node for brackets, so a span it works
        // out from its parts can start or end inside them: `f (g x)` is
        // found as `f (g x` from `f` and `g x`. Such a span is found once
        // the brackets around its ends are added back.
        let found = |start: usize, end: usize| {
            let mut s = start;
            loop {
                let mut e = end;
                loop {
                    if is_node(s, e) {
                        return true;
                    }
                    if !bracket(e, false) {
                        break;
                    }
                    e += 1;
                }
                if s == 0 || !bracket(s - 1, true) {
                    return false;
                }
                s -= 1;
            }
        };
        let unparsed: Vec<(u32, u32)> = self
            .decls
            .iter()
            .filter(|decl| decl.nodes[0].kind == NodeKind::Error)
            .filter_map(|decl| {
                let (start, end) = (decl.nodes[0].start as usize, decl.nodes[0].end as usize);
                let first = self.tokens.get(start)?;
                let last = self.tokens.get(end.checked_sub(1)?)?;
                Some((first.span.start, last.span.end))
            })
            .collect();
        let mut check = SpanCheck::default();
        for (what, span, why) in module_spans(module) {
            if unparsed
                .iter()
                .any(|&(start, end)| start <= span.start && span.start < end)
            {
                check.unparsed += 1;
                continue;
            }
            if span.start == span.end {
                *check.synthetic.entry(Synthetic::Empty).or_default() += 1;
                continue;
            }
            let hit = match (starts.get(&span.start), ends.get(&span.end)) {
                (Some(&start), Some(&end)) => found(start, end),
                _ => false,
            };
            match why {
                _ if hit => check.checked += 1,
                Some(why) => *check.synthetic.entry(why).or_default() += 1,
                None => {
                    check.checked += 1;
                    check.misses.push(SpanMiss { what, span });
                }
            }
        }
        check
    }
}
