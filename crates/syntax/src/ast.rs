//! The surface syntax tree, as written by the user.

use num_bigint::BigUint;

use crate::Span;

#[derive(Clone, Debug)]
pub struct Name {
    pub text: String,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Expr {
    /// A variable, function, data type or constructor name.
    Var(Name),
    Num(BigUint, Span),
    /// A text literal: `"héllo"`.
    Str(String, Span),
    /// A character literal: `'a'`.
    Char(char, Span),
    /// `Type` or `Type n`.
    Type(u32, Span),
    Prop(Span),
    App(Box<Expr>, Box<Expr>),
    /// `\x y -> body`
    Lam(Vec<Name>, Box<Expr>, Span),
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
    /// `[x := e]`, supplying an implicit argument by name. Only valid as an
    /// argument in an application.
    NamedArg(Name, Box<Expr>, Span),
    /// `_`: a hole the compiler fills in.
    Hole(Span),
    /// `A -> B`
    Arrow(Box<Expr>, Box<Expr>),
    /// `a = b`, `a + b`, …
    Binary(BinOp, Box<Expr>, Box<Expr>),
    /// A prefix minus: `-e`.
    Neg(Box<Expr>, Span),
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
    /// Field access `e.name`.
    Field(Box<Expr>, Name),
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
    /// `\p -> body`: the lambda's parameters are generated variables
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
    /// Chains like `f a b c …` and `1 + 2 + 3 + …` are parsed in a loop and
    /// nest as deeply as they're long, so this walks down each side of them
    /// in a loop: the first part's start to the last part's end.
    pub fn span(&self) -> Span {
        let mut first = self;
        let start = loop {
            match first {
                Expr::App(a, _) | Expr::Arrow(a, _) | Expr::Binary(_, a, _) | Expr::Seq(a, _) => {
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
            | Expr::Char(_, span)
            | Expr::Str(_, span)
            | Expr::Type(_, span)
            | Expr::Prop(span)
            | Expr::Lam(_, _, span)
            | Expr::Pi { span, .. }
            | Expr::NamedArg(_, _, span)
            | Expr::If { span, .. }
            | Expr::Hole(span)
            | Expr::Ann(_, _, span)
            | Expr::Neg(_, span)
            | Expr::List(_, span)
            | Expr::Unit(span)
            | Expr::Tuple(_, _, span)
            | Expr::Let { span, .. }
            | Expr::LocalDefs { span, .. }
            | Expr::Record { span, .. }
            | Expr::Handle { span, .. }
            | Expr::Match { span, .. } => *span,
            Expr::Field(e, name) => e.span().to(name.span),
            Expr::Effect(..)
            | Expr::App(..)
            | Expr::Arrow(..)
            | Expr::Binary(..)
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
        Expr::App(a, b) | Expr::Arrow(a, b) | Expr::Binary(_, a, b) | Expr::Seq(a, b) => {
            nested(a) || nested(b)
        }
        Expr::Lam(_, b, _) | Expr::NamedArg(_, b, _) | Expr::Neg(b, _) | Expr::Effect(_, b) => {
            nested(b)
        }
        Expr::Pi { dom, cod, .. } => nested(dom) || nested(cod),
        Expr::Ann(e, t, _) | Expr::Tuple(e, t, _) => nested(e) || nested(t),
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
        Expr::LocalDefs { body, .. } => nested(body),
        Expr::Match {
            scrutinees, alts, ..
        } => scrutinees.iter().any(|s| nested(&s.expr)) || alts.iter().any(|a| nested(&a.body)),
        Expr::List(items, _) => !items.is_empty(),
        Expr::Record { base, fields, .. } => base.is_some() || !fields.is_empty(),
        Expr::Field(e, _) => nested(e),
        _ => false,
    }
}

fn is_leaf(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Var(_)
            | Expr::Num(..)
            | Expr::Str(..)
            | Expr::Char(..)
            | Expr::Type(..)
            | Expr::Prop(_)
            | Expr::Hole(_)
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
        Expr::App(a, b) | Expr::Arrow(a, b) | Expr::Binary(_, a, b) | Expr::Seq(a, b) => {
            take(a);
            take(b);
        }
        Expr::Lam(_, b, _) | Expr::NamedArg(_, b, _) | Expr::Neg(b, _) | Expr::Effect(_, b) => {
            take(b)
        }
        Expr::Pi { dom, cod, .. } => {
            take(dom);
            take(cod);
        }
        Expr::Ann(e, t, _) | Expr::Tuple(e, t, _) => {
            take(e);
            take(t);
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
        // A long block of local definitions nests its rest here.
        Expr::LocalDefs { body, .. } => take(body),
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
}

impl BinOp {
    pub fn symbol(self) -> &'static str {
        match self {
            BinOp::Eq => "=",
            BinOp::Ne => "!=",
            BinOp::EqEq => "==",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Append => "++",
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
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
    Ctor(Name, Vec<Pattern>, Span),
    /// `(p, q)`: the library's pair constructor; three or more nest to the
    /// right.
    Tuple(Box<Pattern>, Box<Pattern>, Span),
    /// `[]`: the library's `Nil`.
    Nil(Span),
    /// `[p, q]` is `Cons p (Cons q Nil)`: the library's `Cons`, by identity.
    /// A list pattern is parsed to these, nested to the right.
    Cons(Box<Pattern>, Box<Pattern>, Span),
    /// A record pattern `{ name = p, age }` (a punned field is a variable of
    /// its name), with `rest` for a trailing `..` that ignores the other
    /// fields.
    Record {
        fields: Vec<(Name, Pattern)>,
        rest: bool,
        span: Span,
    },
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
            | Pattern::Ctor(_, _, span)
            | Pattern::Tuple(_, _, span)
            | Pattern::Nil(span)
            | Pattern::Cons(_, _, span)
            | Pattern::Record { span, .. } => *span,
        }
    }
}

/// `(x y : A)`
#[derive(Clone, Debug)]
pub struct Binder {
    pub names: Vec<Name>,
    pub ty: Expr,
}

#[derive(Clone, Debug)]
pub struct CtorDecl {
    pub name: Name,
    pub fields: Vec<Binder>,
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
        sort: Option<Expr>,
        ctors: Vec<CtorDecl>,
        record: bool,
        span: Span,
    },
    /// `name : Type`, optionally preceded by `theorem` or `export`.
    Signature {
        name: Name,
        ty: Expr,
        theorem: bool,
        export: bool,
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
/// §4.5).
#[derive(Clone, Debug)]
pub struct Import {
    /// The namespace, as written: `List`, or `Std.List`.
    pub path: Name,
    /// At least one.
    pub items: Vec<Name>,
    pub span: Span,
}

#[derive(Clone, Debug, Default)]
pub struct Module {
    /// At the top of the file, before any declaration.
    pub imports: Vec<Import>,
    pub decls: Vec<Decl>,
}
