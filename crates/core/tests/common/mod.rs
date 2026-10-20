//! Builders for hand-written core terms, so kernel tests can feed it terms the
//! elaborator would never produce.
#![allow(dead_code)]

use std::rc::Rc;

use stitchwort_core::check::{self, CtorDecl};
use stitchwort_core::registry;
use stitchwort_core::term::Branch;
use stitchwort_core::{DataId, DefId, Globals, Icit, Sort, Term};
use stitchwort_syntax::{SourceMap, Span};

pub fn span() -> Span {
    let mut sources = SourceMap::new();
    let file = sources.add("test", "");
    Span::point(file, 0)
}

/// De Bruijn index: `v(0)` is the nearest binder.
pub fn v(ix: usize) -> Term {
    Term::Var(ix)
}

pub fn ty() -> Term {
    Term::Sort(Sort::Type(0))
}

pub fn ty_n(n: u32) -> Term {
    Term::Sort(Sort::Type(n))
}

pub fn prop() -> Term {
    Term::Sort(Sort::Prop)
}

/// `(x : a) -> b`, where `b` is already written under the binder.
pub fn pi(x: &str, a: Term, b: Term) -> Term {
    Term::Pi(x.into(), Icit::Explicit, Rc::new(a), Rc::new(b))
}

pub fn ipi(x: &str, a: Term, b: Term) -> Term {
    Term::Pi(x.into(), Icit::Implicit, Rc::new(a), Rc::new(b))
}

/// `a -> b`, where `b` is written outside the binder (it's shifted under it).
pub fn arrow(a: Term, b: Term) -> Term {
    pi("_", a, b.shift(&Globals::default(), 1, 0).unwrap())
}

pub fn lam(x: &str, body: Term) -> Term {
    Term::Lam(x.into(), Icit::Explicit, Rc::new(body))
}

pub fn ilam(x: &str, body: Term) -> Term {
    Term::Lam(x.into(), Icit::Implicit, Rc::new(body))
}

pub fn app(f: Term, args: impl IntoIterator<Item = Term>) -> Term {
    args.into_iter().fold(f, Term::app)
}

pub fn eq(ty: Option<Term>, a: Term, b: Term) -> Term {
    Term::Eq(ty.map(Rc::new), Rc::new(a), Rc::new(b))
}

pub fn case(ix: usize, d: DataId, branches: Vec<(Vec<&str>, Term)>) -> Term {
    Term::Case(
        ix,
        d,
        branches
            .into_iter()
            .map(|(names, body)| Branch {
                names: names.into_iter().map(Into::into).collect(),
                body: Some(Rc::new(body)),
            })
            .collect(),
    )
}

/// A prelude built directly in the core: `Nat`, `add` and `List`.
pub struct Prelude {
    pub g: Globals,
    pub nat: DataId,
    pub add: DefId,
    pub list: DataId,
}

impl Prelude {
    pub fn new() -> Self {
        let mut g = Globals::default();
        let nat = data(&mut g, "Nat", vec![], Sort::Type(0));
        let nat_ty = Term::Data(nat, vec![]);
        check::define_ctors(
            &mut g,
            nat,
            vec![
                ctor("Zero", vec![]),
                ctor("Succ", vec![("n", nat_ty.clone())]),
            ],
        )
        .expect("Nat");

        // add m n = case m of Zero -> n; Succ m' -> Succ (add m' n)
        let add = declare(
            &mut g,
            "Nat.add",
            arrow(nat_ty.clone(), arrow(nat_ty.clone(), nat_ty.clone())),
        );
        let body = lam(
            "m",
            lam(
                "n",
                case(
                    1,
                    nat,
                    vec![
                        (vec![], v(0)),
                        (
                            vec!["m'"],
                            Term::ctor(nat, 1, vec![app(Term::Def(add), [v(0), v(1)])]),
                        ),
                    ],
                ),
            ),
        );
        check::define_def(&mut g, add, &body).expect("add");

        let list = data(&mut g, "List", vec![("a", ty())], Sort::Type(0));
        check::define_ctors(
            &mut g,
            list,
            vec![
                ctor("Nil", vec![]),
                ctor(
                    "Cons",
                    vec![("head", v(0)), ("tail", Term::data(list, vec![v(1)]))],
                ),
            ],
        )
        .expect("List");
        // They're the prelude's, as far as the printer and the evaluator
        // know.
        registry::bind_data(&mut g, nat);
        registry::bind_def(&mut g, add);
        registry::bind_data(&mut g, list);
        Prelude { g, nat, add, list }
    }

    pub fn nat_ty(&self) -> Term {
        Term::Data(self.nat, vec![])
    }

    pub fn num(&self, n: usize) -> Term {
        (0..n).fold(Term::Ctor(self.nat, 0, vec![]), |t, _| {
            Term::ctor(self.nat, 1, vec![t])
        })
    }

    pub fn plus(&self, a: Term, b: Term) -> Term {
        app(Term::Def(self.add), [a, b])
    }
}

pub fn data(g: &mut Globals, name: &str, params: Vec<(&str, Term)>, sort: Sort) -> DataId {
    check::declare_data(
        g,
        name.into(),
        params.into_iter().map(|(x, t)| (x.into(), t)).collect(),
        sort,
        span(),
    )
    .expect("data type parameters check")
}

pub fn ctor(name: &str, fields: Vec<(&str, Term)>) -> CtorDecl {
    CtorDecl {
        name: name.into(),
        fields: fields
            .into_iter()
            .map(|(x, t)| (x.into(), t, span()))
            .collect(),
        result: Vec::new(),
    }
}

pub fn declare(g: &mut Globals, name: &str, ty: Term) -> DefId {
    check::declare_def(g, &name.into(), &ty, false, false, span()).expect("type checks")
}

/// Declares and defines `name : ty = body`, returning the error code if the
/// kernel rejects it.
pub fn define(g: &mut Globals, name: &str, ty: Term, body: Term) -> Result<DefId, &'static str> {
    let id = check::declare_def(g, &name.into(), &ty, false, false, span()).map_err(|d| d.code)?;
    check::define_def(g, id, &body).map_err(|d| d.code)?;
    Ok(id)
}

// Indexed families (docs/proposals/indexed-families.md)

/// Declares a data type with parameters and an index telescope.
pub fn try_family(
    g: &mut Globals,
    name: &str,
    params: Vec<(&str, Term)>,
    indices: Vec<(&str, Term)>,
    sort: Sort,
) -> Result<DataId, stitchwort_syntax::Diagnostic> {
    let ids = check::declare_indexed_data_group(
        g,
        params.into_iter().map(|(x, t)| (x.into(), t)).collect(),
        sort,
        vec![check::DataDecl {
            name: name.into(),
            span: span(),
            record: false,
            indices: indices.into_iter().map(|(x, t)| (x.into(), t)).collect(),
        }],
    )?;
    Ok(ids[0])
}

pub fn family(
    g: &mut Globals,
    name: &str,
    params: Vec<(&str, Term)>,
    indices: Vec<(&str, Term)>,
    sort: Sort,
) -> DataId {
    try_family(g, name, params, indices, sort).expect("the family's telescopes check")
}

/// A constructor with result indices, in the context of the parameters and
/// the fields.
pub fn ictor(name: &str, fields: Vec<(&str, Term)>, result: Vec<Term>) -> CtorDecl {
    CtorDecl {
        result,
        ..ctor(name, fields)
    }
}

/// A case whose branches may be impossible (no body).
pub fn icase(ix: usize, d: DataId, branches: Vec<(Vec<&str>, Option<Term>)>) -> Term {
    Term::Case(
        ix,
        d,
        branches
            .into_iter()
            .map(|(names, body)| Branch {
                names: names.into_iter().map(Into::into).collect(),
                body: body.map(Rc::new),
            })
            .collect(),
    )
}

impl Prelude {
    pub fn succ(&self, t: Term) -> Term {
        Term::ctor(self.nat, 1, vec![t])
    }
}
