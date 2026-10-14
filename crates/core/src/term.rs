//! Core terms: the small, explicit language the kernel checks. See `docs/core.md`.

use std::rc::Rc;

use stitchwort_syntax::Span;

pub type Name = Rc<str>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DefId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DataId(pub usize);

/// A universe: `Prop`, or `Type i`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sort {
    Prop,
    Type(u32),
}

impl Sort {
    /// The universe this universe lives in.
    pub fn succ(self) -> Sort {
        match self {
            Sort::Prop => Sort::Type(0),
            Sort::Type(i) => Sort::Type(i + 1),
        }
    }

    fn level(self) -> u32 {
        match self {
            Sort::Prop => 0,
            Sort::Type(i) => i,
        }
    }

    /// The universe of a pure `(x : A) -> B` with `A : dom` and `B : cod`.
    /// `Prop` is impredicative: if `B` is a proposition, so is the function type.
    pub fn pi(dom: Sort, cod: Sort) -> Sort {
        match cod {
            Sort::Prop => Sort::Prop,
            Sort::Type(_) => Sort::Type(dom.level().max(cod.level())),
        }
    }

    /// Whether a constructor field whose type is in `self` may appear in a data
    /// type declared in `data`.
    pub fn fits_in(self, data: Sort) -> bool {
        match (self, data) {
            (_, Sort::Prop) | (Sort::Prop, _) => true,
            (Sort::Type(i), Sort::Type(j)) => i <= j,
        }
    }
}

/// Whether a function parameter is explicit `(x : A)` or implicit `[x : A]`.
/// Implicit arguments are filled in by the elaborator. The kernel only checks
/// that functions and applications agree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Icit {
    Explicit,
    Implicit,
}

/// Variables are de Bruijn indices: `Var(0)` is the nearest enclosing binder.
#[derive(Clone, Debug)]
pub enum Term {
    Var(usize),
    Def(DefId),
    /// A data type applied to all of its parameters.
    Data(DataId, Vec<Term>),
    /// A constructor applied to all of its fields. The data type's parameters
    /// come from the expected type, so constructors can only be checked.
    Ctor(DataId, usize, Vec<Term>),
    Sort(Sort),
    Pi(Name, Icit, Rc<Term>, Rc<Term>),
    Lam(Name, Icit, Rc<Term>),
    App(Rc<Term>, Rc<Term>, Icit),
    Ann(Rc<Term>, Rc<Term>),
    /// Pattern match on a variable of data type `DataId`, with one branch per
    /// constructor, in declaration order. Only appears at the top of a
    /// definition's body (after its parameters), forming a case tree.
    Case(usize, DataId, Rc<[Branch]>),
    /// `a = b`. The type of `a` and `b` is filled in by the checker.
    Eq(Option<Rc<Term>>, Rc<Term>, Rc<Term>),
    Refl,
    /// `J motive base proof`: transport along an equality.
    J(Rc<Term>, Rc<Term>, Rc<Term>),
    /// A source location, for error messages. Ignored by evaluation.
    Loc(Span, Rc<Term>),
    /// A metavariable: an unknown the elaborator solves by unification. Never
    /// reaches the kernel, which only checks complete terms.
    Meta(usize),
}

#[derive(Clone, Debug)]
pub struct Branch {
    /// Names of the constructor's fields, bound in `body`.
    pub names: Vec<Name>,
    pub body: Term,
}

impl Term {
    pub fn strip_loc(&self) -> &Term {
        let mut term = self;
        while let Term::Loc(_, inner) = term {
            term = inner;
        }
        term
    }

    pub fn app(f: Term, a: Term) -> Term {
        Term::App(Rc::new(f), Rc::new(a), Icit::Explicit)
    }

    pub fn app_icit(f: Term, a: Term, icit: Icit) -> Term {
        Term::App(Rc::new(f), Rc::new(a), icit)
    }

    /// Splits `f a b c` into `f` and `[a, b, c]`, looking through locations.
    pub fn spine(&self) -> (&Term, Vec<&Term>) {
        let mut args = Vec::new();
        let mut head = self.strip_loc();
        while let Term::App(f, a, _) = head {
            args.push(a.as_ref());
            head = f.strip_loc();
        }
        args.reverse();
        (head, args)
    }

    /// The body under the first `n` lambdas.
    pub fn peel_lams(&self, n: usize) -> &Term {
        let mut term = self.strip_loc();
        for _ in 0..n {
            match term {
                Term::Lam(_, _, body) => term = body.strip_loc(),
                _ => panic!("internal error: expected {n} lambdas"),
            }
        }
        term
    }

    pub fn count_lams(&self) -> usize {
        let mut term = self.strip_loc();
        let mut n = 0;
        while let Term::Lam(_, _, body) = term {
            n += 1;
            term = body.strip_loc();
        }
        n
    }

    /// Adds `by` to every variable at or above `cutoff`, for moving a term
    /// under `by` new binders.
    pub fn shift(&self, by: usize, cutoff: usize) -> Term {
        let go = |t: &Rc<Term>, cutoff| Rc::new(t.shift(by, cutoff));
        match self {
            Term::Var(ix) if *ix >= cutoff => Term::Var(ix + by),
            Term::Var(_) | Term::Def(_) | Term::Sort(_) | Term::Refl | Term::Meta(_) => {
                self.clone()
            }
            Term::Data(d, args) => {
                Term::Data(*d, args.iter().map(|a| a.shift(by, cutoff)).collect())
            }
            Term::Ctor(d, c, args) => {
                Term::Ctor(*d, *c, args.iter().map(|a| a.shift(by, cutoff)).collect())
            }
            Term::Pi(x, i, a, b) => Term::Pi(x.clone(), *i, go(a, cutoff), go(b, cutoff + 1)),
            Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, go(b, cutoff + 1)),
            Term::App(f, a, i) => Term::App(go(f, cutoff), go(a, cutoff), *i),
            Term::Ann(e, t) => Term::Ann(go(e, cutoff), go(t, cutoff)),
            Term::Case(ix, d, branches) => Term::Case(
                if *ix >= cutoff { ix + by } else { *ix },
                *d,
                branches
                    .iter()
                    .map(|b| Branch {
                        names: b.names.clone(),
                        body: b.body.shift(by, cutoff + b.names.len()),
                    })
                    .collect(),
            ),
            Term::Eq(ty, a, b) => Term::Eq(
                ty.as_ref().map(|t| go(t, cutoff)),
                go(a, cutoff),
                go(b, cutoff),
            ),
            Term::J(m, b, p) => Term::J(go(m, cutoff), go(b, cutoff), go(p, cutoff)),
            Term::Loc(span, t) => Term::Loc(*span, go(t, cutoff)),
        }
    }

    /// Whether variable `ix` occurs free.
    pub fn mentions(&self, ix: usize) -> bool {
        match self {
            Term::Var(i) => *i == ix,
            Term::Def(_) | Term::Sort(_) | Term::Refl | Term::Meta(_) => false,
            Term::Data(_, args) | Term::Ctor(_, _, args) => args.iter().any(|a| a.mentions(ix)),
            Term::Pi(_, _, a, b) => a.mentions(ix) || b.mentions(ix + 1),
            Term::Lam(_, _, b) => b.mentions(ix + 1),
            Term::App(f, a, _) => f.mentions(ix) || a.mentions(ix),
            Term::Ann(e, t) => e.mentions(ix) || t.mentions(ix),
            Term::Case(i, _, branches) => {
                *i == ix || branches.iter().any(|b| b.body.mentions(ix + b.names.len()))
            }
            Term::Eq(ty, a, b) => {
                ty.as_ref().is_some_and(|t| t.mentions(ix)) || a.mentions(ix) || b.mentions(ix)
            }
            Term::J(m, b, p) => m.mentions(ix) || b.mentions(ix) || p.mentions(ix),
            Term::Loc(_, t) => t.mentions(ix),
        }
    }
}
