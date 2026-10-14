//! The surface syntax tree, as written by the user.

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
    Num(u64, Span),
    /// `Type` or `Type n`.
    Type(u32, Span),
    Prop(Span),
    App(Box<Expr>, Box<Expr>),
    /// `\x y -> body`
    Lam(Vec<Name>, Box<Expr>, Span),
    /// `(x y : A) -> B`, or `[x y : A] -> B` with `implicit`.
    Pi {
        names: Vec<Name>,
        implicit: bool,
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
    /// `a = b`
    Eq(Box<Expr>, Box<Expr>),
    /// `a + b`
    Add(Box<Expr>, Box<Expr>),
    /// `(e : T)`
    Ann(Box<Expr>, Box<Expr>, Span),
    /// `[a, b, c]`
    List(Vec<Expr>, Span),
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Expr::Var(name) => name.span,
            Expr::Num(_, span)
            | Expr::Type(_, span)
            | Expr::Prop(span)
            | Expr::Lam(_, _, span)
            | Expr::Pi { span, .. }
            | Expr::NamedArg(_, _, span)
            | Expr::Hole(span)
            | Expr::Ann(_, _, span)
            | Expr::List(_, span) => *span,
            Expr::App(a, b) | Expr::Arrow(a, b) | Expr::Eq(a, b) | Expr::Add(a, b) => {
                a.span().to(b.span())
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Var(Name),
    Wildcard(Span),
    /// Only `0` is supported for now.
    Num(u64, Span),
    Ctor(Name, Vec<Pattern>, Span),
}

impl Pattern {
    pub fn span(&self) -> Span {
        match self {
            Pattern::Var(name) => name.span,
            Pattern::Wildcard(span) | Pattern::Num(_, span) | Pattern::Ctor(_, _, span) => *span,
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
    /// `name pattern* = expr`
    Equation {
        name: Name,
        patterns: Vec<Pattern>,
        rhs: Expr,
        span: Span,
    },
}

#[derive(Clone, Debug, Default)]
pub struct Module {
    pub decls: Vec<Decl>,
}
