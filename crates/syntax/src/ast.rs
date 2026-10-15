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
    /// `handle e with | return x -> … | op p => k -> …`
    Handle {
        body: Box<Expr>,
        clauses: Vec<Clause>,
        span: Span,
    },
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

impl Expr {
    pub fn span(&self) -> Span {
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
            | Expr::List(_, span)
            | Expr::Unit(span)
            | Expr::Let { span, .. }
            | Expr::Handle { span, .. } => *span,
            Expr::Effect(row, b) => row.span.to(b.span()),
            Expr::App(a, b) | Expr::Arrow(a, b) | Expr::Binary(_, a, b) | Expr::Seq(a, b) => {
                a.span().to(b.span())
            }
        }
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
    Ctor(Name, Vec<Pattern>, Span),
}

impl Pattern {
    pub fn span(&self) -> Span {
        match self {
            Pattern::Var(name) => name.span,
            Pattern::Wildcard(span)
            | Pattern::Absurd(span)
            | Pattern::Num(_, span)
            | Pattern::Ctor(_, _, span) => *span,
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
    /// `type List (a : Type) : Type = | Nil | Cons (head : a) (tail : List a)`
    Data {
        name: Name,
        params: Vec<Binder>,
        sort: Option<Expr>,
        ctors: Vec<CtorDecl>,
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
    Equation {
        name: Name,
        patterns: Vec<Pattern>,
        rhs: Option<Expr>,
        span: Span,
    },
}

#[derive(Clone, Debug, Default)]
pub struct Module {
    pub decls: Vec<Decl>,
}
