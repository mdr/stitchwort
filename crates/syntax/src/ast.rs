//! The surface syntax tree, as written by the user.

use num_bigint::BigUint;

use crate::Span;

#[derive(Clone, Debug)]
pub struct Name {
    pub text: String,
    pub span: Span,
}

/// The parameter of a method section's lambda: `.f a` is parsed as
/// `%section => %section.f a` (docs/syntax.md, Method sections). Users
/// can't write the name, so it never captures one of theirs.
pub const SECTION: &str = "%section";

/// The name of an `auto` parameter written without one, `[auto Ord a]`
/// (docs/proposals/interfaces.md §5.3): it can't be referred to, or given by
/// name.
pub const NAMELESS: &str = "_";

/// The brackets a named argument is written in, which say what kind of
/// parameter it names (D1093).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Bracket {
    /// `(x := e)`: an explicit parameter.
    Round,
    /// `[x := e]`: an implicit or `auto` parameter.
    Square,
}

/// How a lambda's parameter is passed: one mode for each kind of function
/// type, `(x: A) -> B`, `[x: A] -> B` and `[auto x: P] -> B`
/// (docs/proposals/lambda-syntax.md §4.3, D91).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// `(x: A) => body`, or `x => body`.
    Explicit,
    /// `[a: Type] => body`.
    Implicit,
    /// `[auto h: P] => body`, or without a name, `[auto P] => body`.
    Auto,
}

#[derive(Clone, Debug)]
pub enum Expr {
    /// A variable, function, data type or constructor name.
    Var(Name),
    Num(BigUint, Span),
    /// A decimal or exponent literal, as written: `1.5`, `1e3`.
    Float(String, Span),
    /// A text literal: `"héllo"`.
    Str(String, Span),
    /// `include "path"`: the text of a file, read when the program is checked.
    Include(String, Span),
    /// A character literal: `'a'`.
    Char(char, Span),
    /// `Type` or `Type n`.
    Type(u32, Span),
    Prop(Span),
    App(Box<Expr>, Box<Expr>),
    /// `(f a) b`: a call in brackets, applied to more arguments. The
    /// brackets finish the call, so a function with parameter defaults has
    /// them filled before `b` (docs/proposals/signature-defaults.md §6.3).
    /// Only the head of an application is one.
    Bracketed(Box<Expr>, Span),
    /// `x y => body`
    Lam(Vec<Name>, Box<Expr>, Span),
    /// `(x: A) => body`, `[a: Type] => body` or `[auto h: P] => body`: a
    /// lambda whose parameter has a written type (one parameter; several
    /// are nested), with the mode saying which kind of function it is.
    TypedLam(Name, Mode, Box<Expr>, Box<Expr>, Span),
    /// `(x y : A) -> B`, `[x y : A] -> B` with `implicit`, or
    /// `[auto x : P] -> B` with `implicit` and `auto`.
    Pi {
        names: Vec<Name>,
        implicit: bool,
        auto: bool,
        dom: Box<Expr>,
        cod: Box<Expr>,
        span: Span,
    },
    /// `[x := e]`, supplying an implicit or `auto` argument by name, or
    /// `(x := e)`, an explicit one (docs/proposals/named-arguments.md §4).
    /// Only valid as an argument in an application.
    NamedArg(Name, Box<Expr>, Span, Bracket),
    /// `_`: a hole the compiler fills in.
    Hole(Span),
    /// `?`: an open goal. The checker reports what must go here (its type
    /// and the names in scope) and carries on; the declaration is
    /// unfinished, not wrong (docs/proposals/lsp-goal-holes.md).
    Goal(Span),
    /// `A -> B`
    Arrow(Box<Expr>, Box<Expr>),
    /// `a = b`, `a + b`, …
    Binary(BinOp, Box<Expr>, Box<Expr>),
    /// `x |> f a b`: `f a b x`, with `x` elaborated (and run) first.
    Pipe(Box<Expr>, Box<Expr>),
    /// A prefix minus: `-e`, or a negative argument `f -e`.
    Neg(Box<Expr>, Span, NegForm),
    /// `"a${x}b"`: a text with interpolations, its pieces joined with `++`,
    /// spanning the whole literal, quotes included.
    Interpolated(Box<Expr>, Span),
    /// `if c then a else b`, or with a binder, `if h : P then a else b`, where
    /// `h` is a proof of `P` in `a` and of `Not P` in `b`.
    If {
        binder: Option<Name>,
        cond: Box<Expr>,
        then: Box<Expr>,
        otherwise: Box<Expr>,
        span: Span,
    },
    /// `(e : T)`
    Ann(Box<Expr>, Box<Expr>, Span),
    /// `[a, b, c]`
    List(Vec<Expr>, Span),
    /// `()`: the unit value, or the unit type.
    Unit(Span),
    /// `(a, b)`: a pair value or a pair type, decided by elaboration; three
    /// or more components nest to the right, `(a, (b, c))`.
    Tuple(Box<Expr>, Box<Expr>, Span),
    /// `{E} B`, the result of a function type that may perform the
    /// abilities in `E`: `Nat -> {State Nat} Nat`.
    Effect(Row, Box<Expr>),
    /// `let x = e` (or `let x : T = e`) on one line of a block, with the rest
    /// of the block as `body`.
    Let {
        name: Name,
        ty: Option<Box<Expr>>,
        value: Box<Expr>,
        body: Box<Expr>,
        span: Span,
    },
    /// One line of a block followed by the rest: `a` is run for its effects.
    Seq(Box<Expr>, Box<Expr>),
    /// Local definitions: `def`s and `theorem`s on consecutive lines of a
    /// block, with the rest of the block as `body`. They may refer to each
    /// other (docs/proposals/syntax-conveniences.md §3).
    LocalDefs {
        defs: Vec<LocalDef>,
        body: Box<Expr>,
        span: Span,
    },
    /// `handle e with | return x -> … | op p => k -> …`
    Handle {
        body: Box<Expr>,
        clauses: Vec<Clause>,
        span: Span,
    },
    /// `match reify t with | return x => … | Fail.stop msg, k => …`: in a
    /// proof, a split on what the computation `t ()` does first, with
    /// clauses written as a handler's (docs/proposals/proof-reification.md).
    Reify {
        thunk: Box<Expr>,
        clauses: Vec<Clause>,
        span: Span,
    },
    /// `match e with | p -> body | …`; several scrutinees `match a, b with | p, q -> …`;
    /// naming the equation `match h : e with …` (docs/proposals/syntax-conveniences.md §4).
    Match {
        scrutinees: Vec<Scrutinee>,
        alts: Vec<Alt>,
        span: Span,
        kind: MatchKind,
    },
    /// A record literal `{ name = e, age = e }`, or with a base, an update
    /// `{ p | age = e }`. Fields are in the order written; a punned field
    /// `{ name }` is `{ name = name }`.
    Record {
        base: Option<Box<Expr>>,
        fields: Vec<(Name, Expr)>,
        span: Span,
    },
    /// `C { f = e, g }`: constructor `C` applied to its explicit fields,
    /// named, in any order (a punned field `{ g }` is `{ g = g }`). Braces
    /// right after a constructor always name its fields; a record literal as
    /// its positional argument is written in brackets, `C ({ … })`, which is
    /// `App(C, Record { … })` (docs/proposals/variant-fields.md §4.5).
    CtorFields {
        ctor: Name,
        fields: Vec<(Name, Expr)>,
        span: Span,
    },
    /// `calc e0` followed by steps `_ = e1 := proof`, one per line
    /// (docs/syntax.md, calc): a chain of relations from `e0` to the last
    /// step's expression.
    Calc {
        first: Box<Expr>,
        steps: Vec<CalcStep>,
        span: Span,
    },
    /// `rewrite p, <- q in t` (docs/syntax.md, rewrite): `t` proves the
    /// expected proposition with each rule's left side replaced by its right
    /// side, the rules applied left to right. Without `in t`, `t` is `rfl`.
    ///
    /// With `at h` (docs/proposals/rewrite-hypothesis.md) the rules rewrite
    /// the type of `h` instead: `rewrite p at h in t` checks `t` with `h`
    /// rebound to the rewritten fact, and `rewrite p at h` is that fact.
    Rewrite {
        rules: Vec<RewriteRule>,
        target: Option<Box<Expr>>,
        body: Option<Box<Expr>>,
        span: Span,
    },
    /// `omega`, or `omega [e1, e2]` with extra facts (docs/syntax.md,
    /// omega): a proof of a linear arithmetic goal from the facts in scope
    /// and the ones listed, found by the compiler and checked by the kernel
    /// (docs/proposals/omega.md).
    Omega {
        facts: Vec<Expr>,
        span: Span,
    },
    /// `cases`, or `cases in t` (docs/syntax.md, cases): a proof found by
    /// splitting on what the goal and the hypotheses are stuck on, each case
    /// closed by computation, a contradiction, `omega`, or `t`
    /// (docs/proposals/simp.md §5). The proof is the `match`es it writes.
    Cases {
        body: Option<Box<Expr>>,
        span: Span,
    },
    /// `ring`, or `ring [h1, h2]` with hypotheses (docs/syntax.md, ring): a
    /// proof of an equation between polynomials over `Nat` or `Int`, checked
    /// by the kernel normalising both sides
    /// (docs/proposals/proof-automation.md §6.2).
    Ring {
        facts: Vec<Expr>,
        span: Span,
    },
    /// Field access `e.name`.
    Field(Box<Expr>, Name),
}

/// One rule of a `rewrite`: a proof of an equation, used left to right or,
/// with `<-`, right to left.
#[derive(Clone, Debug)]
pub struct RewriteRule {
    pub reverse: bool,
    pub proof: Expr,
    /// From the `<-` (if any) to the end of the proof.
    pub span: Span,
}

/// One line of a `calc`: `_ R rhs := proof`. `R` is `=`, `<=` or `<` (as a
/// [`BinOp`]); without a proof the step is closed by computation.
#[derive(Clone, Debug)]
pub struct CalcStep {
    pub rel: BinOp,
    pub rel_span: Span,
    pub rhs: Expr,
    pub proof: Option<Expr>,
    /// From the `_` to the end of the line's proof or expression.
    pub span: Span,
}

/// A local `def` or `theorem`, lowered as at top level: a
/// [`Decl::Signature`] and its [`Decl::Equation`]s.
#[derive(Clone, Debug)]
pub struct LocalDef {
    pub signature: Decl,
    pub equations: Vec<Decl>,
}

/// An ability row, `{State s, Abort | e}`. A row ending in a lowercase name
/// without `|` (`{e}`) has only a tail.
#[derive(Clone, Debug)]
pub struct Row {
    pub abilities: Vec<Expr>,
    pub tail: Option<Name>,
    pub span: Span,
}

/// A handler clause.
#[derive(Clone, Debug)]
pub enum Clause {
    /// `return x -> body`
    Return { var: Name, body: Expr },
    /// `op arg => k -> body`, where `arg` is a variable, `_` or `()`.
    Op {
        op: Name,
        arg: Pattern,
        k: Name,
        body: Expr,
    },
}

/// What a `match` was written as. A pattern in `let` or in a lambda is a
/// one-alternative `match` (docs/proposals/syntax-conveniences.md §5), whose
/// failure to cover every case is `E-LET-REFUTABLE` rather than
/// `E-NONEXHAUSTIVE`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MatchKind {
    /// `match … with`.
    Match,
    /// `let p = e`, followed by the rest of the block.
    Let,
    /// `p => body`: the lambda's parameters are generated variables
    /// matched against its patterns.
    Lambda,
}

/// One scrutinee of a `match`: the expression, and the name of its equation if written (`h : e`).
#[derive(Clone, Debug)]
pub struct Scrutinee {
    pub name: Option<Name>,
    pub expr: Expr,
}

/// One alternative of a `match`: `| p₁, p₂ -> body`, one pattern per scrutinee.
#[derive(Clone, Debug)]
pub struct Alt {
    pub patterns: Vec<Pattern>,
    pub body: Expr,
    /// From the `|` to the end of the body.
    pub span: Span,
}

impl Expr {
    /// If this is a method section `.f ….g args`, the first name after the
    /// `.` (`f`), for messages.
    pub fn section_name(&self) -> Option<&Name> {
        let Expr::Lam(names, body, _) = self else {
            return None;
        };
        if names.len() != 1 || names[0].text != SECTION {
            return None;
        }
        let mut e: &Expr = body;
        loop {
            match e {
                Expr::App(f, _) => e = f,
                Expr::Field(r, name) => match &**r {
                    Expr::Var(v) if v.text == SECTION => return Some(name),
                    _ => e = r,
                },
                _ => return None,
            }
        }
    }

    /// Chains like `f a b c …` and `1 + 2 + 3 + …` are parsed in a loop and
    /// nest as deeply as they're long, so this walks down each side of them
    /// in a loop: the first part's start to the last part's end.
    pub fn span(&self) -> Span {
        let mut first = self;
        let start = loop {
            match first {
                Expr::App(a, _)
                | Expr::Arrow(a, _)
                | Expr::Binary(_, a, _)
                | Expr::Pipe(a, _)
                | Expr::Seq(a, _) => {
                    first = a;
                }
                Expr::Effect(row, _) => break row.span,
                _ => break first.own_span(),
            }
        };
        let mut last = self;
        let end = loop {
            match last {
                Expr::App(_, b)
                | Expr::Arrow(_, b)
                | Expr::Binary(_, _, b)
                | Expr::Pipe(_, b)
                | Expr::Seq(_, b)
                | Expr::Effect(_, b) => last = b,
                _ => break last.own_span(),
            }
        };
        start.to(end)
    }

    /// The span of anything but a chain.
    fn own_span(&self) -> Span {
        match self {
            Expr::Var(name) => name.span,
            Expr::Num(_, span)
            | Expr::Float(_, span)
            | Expr::Char(_, span)
            | Expr::Str(_, span)
            | Expr::Include(_, span)
            | Expr::Type(_, span)
            | Expr::Prop(span)
            | Expr::Lam(_, _, span)
            | Expr::TypedLam(_, _, _, _, span)
            | Expr::Pi { span, .. }
            | Expr::NamedArg(_, _, span, _)
            | Expr::If { span, .. }
            | Expr::Hole(span)
            | Expr::Goal(span)
            | Expr::Ann(_, _, span)
            | Expr::Bracketed(_, span)
            | Expr::Neg(_, span, _)
            | Expr::Interpolated(_, span)
            | Expr::List(_, span)
            | Expr::Unit(span)
            | Expr::Tuple(_, _, span)
            | Expr::Let { span, .. }
            | Expr::LocalDefs { span, .. }
            | Expr::Record { span, .. }
            | Expr::CtorFields { span, .. }
            | Expr::Handle { span, .. }
            | Expr::Reify { span, .. }
            | Expr::Calc { span, .. }
            | Expr::Rewrite { span, .. }
            | Expr::Omega { span, .. }
            | Expr::Cases { span, .. }
            | Expr::Ring { span, .. }
            | Expr::Match { span, .. } => *span,
            // Down a chain of fields in a loop: `e.span()` here would reach
            // this arm for `e` too, twice per level (the start and the end),
            // so `x.f.g.h …` would take time exponential in its length.
            Expr::Field(e, name) => {
                let mut inner: &Expr = e;
                while let Expr::Field(i, _) = inner {
                    inner = i;
                }
                inner.span().to(name.span)
            }
            Expr::Effect(..)
            | Expr::App(..)
            | Expr::Arrow(..)
            | Expr::Binary(..)
            | Expr::Pipe(..)
            | Expr::Seq(..) => self.span(),
        }
    }
}

/// Freeing an expression frees its sub-expressions without recursing: the
/// parser builds chains like `f a b c …` in a loop, so they can nest more
/// deeply than recursion could follow. Rust frees nested data recursively by
/// default, which would overflow the stack.
impl Drop for Expr {
    fn drop(&mut self) {
        if !has_nested(self) {
            return;
        }
        let mut pending = Vec::new();
        take_children(self, &mut pending);
        while let Some(mut child) = pending.pop() {
            take_children(&mut child, &mut pending);
            // `child` is freed here, with nothing left to free under it.
        }
    }
}

/// Whether freeing `expr` would free another expression with parts.
fn has_nested(expr: &Expr) -> bool {
    let nested = |e: &Expr| !is_leaf(e);
    match expr {
        Expr::App(a, b)
        | Expr::Arrow(a, b)
        | Expr::Binary(_, a, b)
        | Expr::Pipe(a, b)
        | Expr::Seq(a, b) => nested(a) || nested(b),
        Expr::Lam(_, b, _)
        | Expr::NamedArg(_, b, _, _)
        | Expr::Neg(b, _, _)
        | Expr::Interpolated(b, _)
        | Expr::Effect(_, b) => nested(b),
        Expr::Pi { dom, cod, .. } => nested(dom) || nested(cod),
        Expr::Ann(e, t, _) | Expr::Tuple(e, t, _) => nested(e) || nested(t),
        Expr::TypedLam(_, _, t, b, _) => nested(t) || nested(b),
        Expr::If {
            cond,
            then,
            otherwise,
            ..
        } => nested(cond) || nested(then) || nested(otherwise),
        Expr::Let {
            ty, value, body, ..
        } => ty.as_deref().is_some_and(nested) || nested(value) || nested(body),
        Expr::Handle { body, .. } => nested(body),
        Expr::Reify { thunk, .. } => nested(thunk),
        Expr::Calc { first, steps, .. } => {
            nested(first)
                || steps
                    .iter()
                    .any(|s| nested(&s.rhs) || s.proof.as_ref().is_some_and(nested))
        }
        Expr::Rewrite {
            rules,
            target,
            body,
            ..
        } => {
            rules.iter().any(|r| nested(&r.proof))
                || target.as_deref().is_some_and(nested)
                || body.as_deref().is_some_and(nested)
        }
        Expr::LocalDefs { body, .. } => nested(body),
        Expr::Omega { facts, .. } | Expr::Ring { facts, .. } => facts.iter().any(nested),
        Expr::Cases { body, .. } => body.as_deref().is_some_and(nested),
        Expr::Match {
            scrutinees, alts, ..
        } => scrutinees.iter().any(|s| nested(&s.expr)) || alts.iter().any(|a| nested(&a.body)),
        Expr::List(items, _) => !items.is_empty(),
        Expr::Record { base, fields, .. } => base.is_some() || !fields.is_empty(),
        Expr::CtorFields { fields, .. } => !fields.is_empty(),
        Expr::Field(e, _) => nested(e),
        _ => false,
    }
}

fn is_leaf(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Var(_)
            | Expr::Num(..)
            | Expr::Float(..)
            | Expr::Str(..)
            | Expr::Include(..)
            | Expr::Char(..)
            | Expr::Type(..)
            | Expr::Prop(_)
            | Expr::Hole(_)
            | Expr::Goal(_)
            | Expr::Unit(_)
    )
}

/// Moves `expr`'s boxed sub-expressions and list items onto `pending`,
/// leaving placeholders. (Handler clauses and rows hold expressions too, but
/// only ones the parser reached by recursing, which it limits.)
fn take_children(expr: &mut Expr, pending: &mut Vec<Expr>) {
    let mut take = |e: &mut Box<Expr>| {
        if !is_leaf(e) {
            pending.push(std::mem::replace(&mut **e, Expr::Prop(Span::NOWHERE)));
        }
    };
    match expr {
        Expr::App(a, b)
        | Expr::Arrow(a, b)
        | Expr::Binary(_, a, b)
        | Expr::Pipe(a, b)
        | Expr::Seq(a, b) => {
            take(a);
            take(b);
        }
        Expr::Lam(_, b, _)
        | Expr::NamedArg(_, b, _, _)
        | Expr::Neg(b, _, _)
        | Expr::Interpolated(b, _)
        | Expr::Effect(_, b) => take(b),
        Expr::Pi { dom, cod, .. } => {
            take(dom);
            take(cod);
        }
        Expr::Ann(e, t, _) | Expr::Tuple(e, t, _) => {
            take(e);
            take(t);
        }
        Expr::TypedLam(_, _, t, b, _) => {
            take(t);
            take(b);
        }
        Expr::If {
            cond,
            then,
            otherwise,
            ..
        } => {
            take(cond);
            take(then);
            take(otherwise);
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            if let Some(ty) = ty {
                take(ty);
            }
            take(value);
            take(body);
        }
        Expr::Handle { body, .. } => take(body),
        Expr::Reify { thunk, .. } => take(thunk),
        Expr::Calc { first, steps, .. } => {
            take(first);
            for step in steps {
                pending.push(std::mem::replace(&mut step.rhs, Expr::Prop(Span::NOWHERE)));
                if let Some(proof) = &mut step.proof {
                    pending.push(std::mem::replace(proof, Expr::Prop(Span::NOWHERE)));
                }
            }
        }
        Expr::Rewrite {
            rules,
            target,
            body,
            ..
        } => {
            if let Some(body) = body {
                take(body);
            }
            if let Some(target) = target {
                take(target);
            }
            for rule in rules {
                pending.push(std::mem::replace(
                    &mut rule.proof,
                    Expr::Prop(Span::NOWHERE),
                ));
            }
        }
        // A long block of local definitions nests its rest here.
        Expr::LocalDefs { body, .. } => take(body),
        Expr::Omega { facts, .. } | Expr::Ring { facts, .. } => {
            for fact in facts {
                pending.push(std::mem::replace(fact, Expr::Prop(Span::NOWHERE)));
            }
        }
        Expr::Cases {
            body: Some(body), ..
        } => take(body),
        Expr::Cases { body: None, .. } => {}
        // A pattern `let` nests the rest of its block in its alternative,
        // so a long block nests deeply there.
        Expr::Match {
            scrutinees, alts, ..
        } => {
            for e in scrutinees
                .iter_mut()
                .map(|s| &mut s.expr)
                .chain(alts.iter_mut().map(|a| &mut a.body))
            {
                if !is_leaf(e) {
                    pending.push(std::mem::replace(e, Expr::Prop(Span::NOWHERE)));
                }
            }
        }
        Expr::List(items, _) => pending.append(items),
        Expr::Record { base, fields, .. } => {
            if let Some(base) = base {
                take(base);
            }
            for (_, value) in fields {
                pending.push(std::mem::replace(value, Expr::Prop(Span::NOWHERE)));
            }
        }
        Expr::CtorFields { fields, .. } => {
            for (_, value) in fields {
                pending.push(std::mem::replace(value, Expr::Prop(Span::NOWHERE)));
            }
        }
        Expr::Field(e, _) => take(e),
        _ => {}
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    /// `=`: equality, a proposition.
    Eq,
    /// `!=`: `Not (a = b)`.
    Ne,
    /// `a == b`: whether `a = b`, as a `Bool`.
    EqEq,
    /// `&&`, `||`: on `Bool`s (short-circuiting), or on propositions
    /// (`And`, `Or`).
    And,
    Or,
    /// `<`, `<=`: propositions about `Nat`.
    Lt,
    Le,
    /// `++`: joins texts, or lists.
    Append,
    Add,
    Sub,
    Mul,
    /// `/`, `%`: need a proof that the divisor isn't zero.
    Div,
    Mod,
    /// `x in c` (or `x ∈ c`): membership in a list, a set or a map's keys
    /// (D1201), with the operator's span. `x !in c` is parsed as
    /// `!(x in c)`.
    In(Span),
}

impl BinOp {
    pub fn symbol(self) -> &'static str {
        match self {
            BinOp::Eq => "=",
            BinOp::Ne => "!=",
            BinOp::EqEq => "==",
            BinOp::And => "&&",
            BinOp::Or => "||",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Append => "++",
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::In(_) => "in",
        }
    }
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Var(Name),
    Wildcard(Span),
    /// `()`: this argument's type has no values, so the equation needs no
    /// right-hand side.
    Absurd(Span),
    /// A number: that many `Succ`s around `Zero`.
    Num(BigUint, Span),
    /// A negative number `(-k)`, written in brackets.
    NegNum(BigUint, Span),
    /// A character `'L'`: `MkChar 76 _`, the code as a number pattern.
    Char(char, Span),
    Ctor(Name, Vec<Pattern>, Span),
    /// `(p, q)`: the library's pair constructor; three or more nest to the
    /// right.
    Tuple(Box<Pattern>, Box<Pattern>, Span),
    /// `[]`: the library's `Nil`.
    Nil(Span),
    /// `[p, q]` is `Cons p (Cons q Nil)`: the library's `Cons`, by identity.
    /// A list pattern is parsed to these, nested to the right.
    Cons(Box<Pattern>, Box<Pattern>, Span),
    /// `[n := p]` among a constructor pattern's arguments: implicit field
    /// `n` matched by `p` (docs/proposals/indexed-families.md §7.3).
    Named(Name, Box<Pattern>, Span),
    /// A record pattern `{ name = p, age }` (a punned field is a variable of
    /// its name), with `rest` for a trailing `..` that ignores the other
    /// fields.
    Record {
        fields: Vec<(Name, Pattern)>,
        rest: bool,
        span: Span,
    },
    /// `C { f = p, g, .. }`: constructor `C` with its explicit fields named,
    /// as in a record pattern; the fields left out are `_` (with `rest`).
    /// Braces right after a constructor always name its fields; a record
    /// pattern as its positional argument is written in brackets,
    /// `C ({ … })`, which is `Ctor(C, [Record { … }])`
    /// (docs/proposals/variant-fields.md §4).
    CtorFields {
        ctor: Name,
        fields: Vec<(Name, Pattern)>,
        rest: bool,
        span: Span,
    },
    /// `p | q | …`: matches if any alternative does. The alternatives bind
    /// no variables; an arm with one is checked as one arm per alternative.
    Or(Vec<Pattern>, Span),
}

impl Decl {
    pub fn span(&self) -> Span {
        match self {
            Decl::Data { span, .. }
            | Decl::Signature { span, .. }
            | Decl::Test { span, .. }
            | Decl::Ability { span, .. }
            | Decl::Equation { span, .. } => *span,
        }
    }
}

impl Pattern {
    pub fn span(&self) -> Span {
        match self {
            Pattern::Var(name) => name.span,
            Pattern::Wildcard(span)
            | Pattern::Absurd(span)
            | Pattern::Num(_, span)
            | Pattern::NegNum(_, span)
            | Pattern::Char(_, span)
            | Pattern::Ctor(_, _, span)
            | Pattern::Tuple(_, _, span)
            | Pattern::Nil(span)
            | Pattern::Cons(_, _, span)
            | Pattern::Named(_, _, span)
            | Pattern::Record { span, .. }
            | Pattern::CtorFields { span, .. }
            | Pattern::Or(_, span) => *span,
        }
    }
}

/// An attribute, `js.name "CIRCLE"`, one of those written in `@[…]`
/// before a declaration, a constructor or a field (docs/syntax.md,
/// Attributes). The parser checks only its shape; the elaborator's registry
/// knows the names.
#[derive(Clone, Debug)]
pub struct Attribute {
    /// The name, as written: `js.name`.
    pub name: Name,
    /// The argument, a plain string, and where it's written.
    pub arg: Option<(String, Span)>,
    /// From the name to the end of the argument.
    pub span: Span,
}

/// `(x y : A)`
#[derive(Clone, Debug)]
pub struct Binder {
    pub names: Vec<Name>,
    pub ty: Expr,
    /// The attributes written inside the brackets, before the names:
    /// `(@[js.name "center_x"] centerX: Nat)`. Only a constructor's or a
    /// record's field may have any; the parser refuses them elsewhere.
    pub attrs: Vec<Attribute>,
}

#[derive(Clone, Debug)]
pub struct CtorDecl {
    /// The attributes written after the constructor's `|`.
    pub attrs: Vec<Attribute>,
    pub name: Name,
    pub fields: Vec<Binder>,
    /// For each binder of `fields`, whether it's implicit, `[n: T]`.
    pub implicit: Vec<bool>,
    /// For each binder of `fields`, its default value, `(id: Text :=
    /// "anonymous")`, or in a record `step: Nat := 1`
    /// (docs/proposals/named-arguments.md §5.1). Empty when no field has
    /// one; only explicit fields can.
    pub defaults: Vec<Option<Expr>>,
    /// The result type, `: Vec a (Succ n)`, if written
    /// (docs/proposals/indexed-families.md §7.1).
    pub result: Option<Expr>,
}

#[derive(Clone, Debug)]
pub enum Decl {
    /// `type List (a : Type) : Type = | Nil | Cons (head : a) (tail : List a)`,
    /// or with `record`, `type Person = { name : Text, age : Nat }`: one
    /// constructor, named `%mk` (which source can't write), with a
    /// field for each of the record's, in order.
    Data {
        name: Name,
        params: Vec<Binder>,
        /// For each binder of `params`, whether it's an `auto` parameter,
        /// `[auto ord: Ord k]`, filled in by instance search wherever the
        /// type is written (docs/proposals/interfaces.md §7.5).
        auto_params: Vec<bool>,
        /// The index telescope after the header's colon: `Nat -> Type`, or
        /// with names, `(len: Nat) -> Type` (docs/proposals/indexed-families.md).
        indices: Vec<(Option<Name>, Expr)>,
        sort: Option<Expr>,
        ctors: Vec<CtorDecl>,
        record: bool,
        /// `interface I (a: Type) = { … }`: a record whose values the
        /// compiler finds by type (docs/proposals/interfaces.md §5.1).
        interface: bool,
        /// The attributes written before the declaration.
        attrs: Vec<Attribute>,
        span: Span,
    },
    /// `name : Type`, optionally preceded by `theorem` or `export`.
    Signature {
        name: Name,
        ty: Expr,
        theorem: bool,
        export: bool,
        /// `type Name = …`: a transparent name for a type, checked as a
        /// definition but never recursive, so a cycle among synonyms is its
        /// own error (`E-SYNONYM-CYCLE`).
        synonym: bool,
        /// `instance N: I T := …`: a definition that `auto` finds by its
        /// type (docs/proposals/interfaces.md §5.2).
        instance: bool,
        /// `decreasing e` after the result type: the measure of a
        /// well-founded recursive definition or theorem
        /// (docs/proposals/well-founded-recursion.md §6.1).
        decreasing: Option<Box<Expr>>,
        /// `opaque def`: opaque to the checker, so other declarations see
        /// its type and not its body (docs/proposals/opaque-definitions.md
        /// §6.2).
        opaque: bool,
        /// `unfolding f, g` after the result type (and after `decreasing e`):
        /// the opaque definitions whose bodies this one's body may use
        /// (docs/proposals/opaque-definitions.md §6.3). Empty if not written.
        unfolding: Vec<Name>,
        /// The default values of the header's parameters, `(step: Nat := 1)`:
        /// empty when none has one, otherwise one entry per binder the
        /// header's parameters make, in order (each name of `(a b: T)` its
        /// own, `()` one), so its length is how many there are.
        defaults: Vec<Option<Expr>>,
        /// The attributes written before the declaration (before `export`,
        /// if it's there).
        attrs: Vec<Attribute>,
        span: Span,
    },
    /// `test "name" = expr`: a `Bool` that `stitchwort test` checks is `True`.
    Test {
        name: String,
        expr: Expr,
        span: Span,
    },
    /// `ability State (s : Type) where` followed by its operations, one per
    /// line: `get : () -> {State s} s`.
    Ability {
        name: Name,
        params: Vec<Binder>,
        ops: Vec<(Name, Expr)>,
        span: Span,
    },
    /// `name pattern* = expr`, or without `= expr` when a pattern is `()`.
    /// In the new declaration syntax, a `def` lowers to a signature and
    /// equations (docs/proposals/declaration-syntax.md §2.3).
    Equation {
        name: Name,
        patterns: Vec<Pattern>,
        rhs: Option<Expr>,
        /// For an arm under a `def` or `theorem` header: how many of
        /// `patterns` are the header's named parameters (the rest are the
        /// arm's own). Arms have exact arity (§2.4). `None` for an old-style
        /// equation, or a `:=` body.
        arm: Option<usize>,
        span: Span,
    },
}

/// `import List (map, filter)`: makes `map` and `filter` from the namespace
/// `List` usable without `List.` in this file (docs/proposals/namespaces.md
/// §4.5). `import List (..)` makes every name declared directly in `List`
/// usable, below the names imported one by one
/// (docs/proposals/multi-file.md §4.5).
#[derive(Clone, Debug)]
pub struct Import {
    /// The namespace, as written: `List`, or `Std.List`.
    pub path: Name,
    /// The names listed: at least one, or none for `(..)`.
    pub items: Vec<Name>,
    /// `(..)`: the span of the `..`.
    pub everything: Option<Span>,
    pub span: Span,
}

/// `namespace Day05`: the first line of a file, saying which namespace its
/// declarations go in (docs/proposals/multi-file.md §4.2).
#[derive(Clone, Debug)]
pub struct NamespaceDecl {
    /// The namespace, as written: `Day05` or `Aoc.Day05`.
    pub path: Name,
    pub span: Span,
}

#[derive(Clone, Debug, Default)]
pub struct Module {
    /// The file's namespace line, if it has one.
    pub namespace: Option<NamespaceDecl>,
    /// At the top of the file, before any declaration.
    pub imports: Vec<Import>,
    pub decls: Vec<Decl>,
    /// Names declared by declarations that failed to parse, so aren't in
    /// `decls` (only `parse_module_recovering` fills it).
    pub failed: Vec<Name>,
}

/// How a [`Expr::Neg`] was written. Only the elaborator's messages read it;
/// the kernel never sees it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NegForm {
    /// `-e` at the start of an operand, or a negative numeral.
    Operand,
    /// An unbracketed argument, `f -e`: a space before the `-`, none after
    /// (docs/proposals/negative-arguments.md §4.2).
    Argument,
}
