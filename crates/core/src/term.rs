//! Core terms: the small, explicit language the kernel checks. See `docs/core.md`.

use std::rc::Rc;

use num_bigint::BigUint;
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

/// Whether a function parameter is explicit `(x : A)`, implicit `[x : A]`, or
/// an implicit proof found automatically, `[auto x : P]`. Implicit and auto
/// arguments are filled in by the elaborator. The kernel only checks that
/// functions and applications agree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Icit {
    Explicit,
    Implicit,
    Auto,
}

impl Icit {
    /// Implicit or auto: filled in by the compiler.
    pub fn is_implicit(self) -> bool {
        self != Icit::Explicit
    }
}

/// Variables are de Bruijn indices: `Var(0)` is the nearest enclosing binder.
#[derive(Clone, Debug)]
pub enum Term {
    Var(usize),
    Def(DefId),
    /// A data type applied to all of its parameters.
    Data(DataId, Vec<Rc<Term>>),
    /// A constructor applied to all of its fields. The data type's parameters
    /// come from the expected type, so constructors can only be checked.
    Ctor(DataId, usize, Vec<Rc<Term>>),
    /// A number: the same as that many `Succ`s around `Zero`, stored compactly.
    Nat(Rc<BigUint>),
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

/// Freeing a term frees its sub-terms without recursing, however deeply they
/// nest (a long list literal is a long chain of `Ctor`s): the sub-terms this
/// is the last owner of are taken out onto a work list and freed one at a
/// time. Rust frees nested data recursively by default, which would overflow
/// the stack.
impl Drop for Term {
    fn drop(&mut self) {
        if !has_unique_child(self) {
            return; // freeing it only decrements its children's counts
        }
        let Ok(leaf) = LEAF.try_with(Rc::clone) else {
            return; // the thread is ending
        };
        let mut free = |pending: &mut Vec<Rc<Term>>| {
            take_children(self, &leaf, pending);
            while let Some(child) = pending.pop() {
                if let Ok(mut term) = Rc::try_unwrap(child) {
                    take_children(&mut term, &leaf, pending);
                }
            }
        };
        // Freeing never starts another free that needs the shared work list
        // (everything it frees has had its children taken), but if it ever
        // did, a local one would do.
        let shared = FREEING.try_with(|p| match p.try_borrow_mut() {
            Ok(mut p) => {
                free(&mut p);
                true
            }
            Err(_) => false,
        });
        if shared != Ok(true) {
            free(&mut Vec::new());
        }
    }
}

thread_local! {
    /// What a taken-apart term's children are replaced with.
    static LEAF: Rc<Term> = Rc::new(Term::Refl);
    /// The work list for freeing, kept between uses.
    static FREEING: std::cell::RefCell<Vec<Rc<Term>>> = const { std::cell::RefCell::new(Vec::new()) };
}

fn has_unique_child(term: &Term) -> bool {
    let unique = |t: &Rc<Term>| Rc::strong_count(t) == 1;
    match term {
        Term::Pi(_, _, a, b) | Term::App(a, b, _) | Term::Ann(a, b) => unique(a) || unique(b),
        Term::Lam(_, _, b) | Term::Loc(_, b) => unique(b),
        Term::Data(_, args) | Term::Ctor(_, _, args) => args.iter().any(unique),
        Term::Eq(ty, a, b) => ty.as_ref().is_some_and(unique) || unique(a) || unique(b),
        Term::J(m, b, p) => unique(m) || unique(b) || unique(p),
        Term::Case(_, _, branches) => {
            Rc::strong_count(branches) == 1 && branches.iter().any(|b| unique(&b.body))
        }
        Term::Var(_) | Term::Def(_) | Term::Nat(_) | Term::Sort(_) | Term::Refl | Term::Meta(_) => {
            false
        }
    }
}

/// Moves `term`'s sub-terms onto `pending`, leaving `leaf` in their place.
fn take_children(term: &mut Term, leaf: &Rc<Term>, pending: &mut Vec<Rc<Term>>) {
    let mut take = |t: &mut Rc<Term>| pending.push(std::mem::replace(t, leaf.clone()));
    match term {
        Term::Pi(_, _, a, b) | Term::App(a, b, _) | Term::Ann(a, b) => {
            take(a);
            take(b);
        }
        Term::Lam(_, _, b) | Term::Loc(_, b) => take(b),
        Term::Data(_, args) | Term::Ctor(_, _, args) => pending.append(args),
        Term::Eq(ty, a, b) => {
            if let Some(ty) = ty {
                take(ty);
            }
            take(a);
            take(b);
        }
        Term::J(m, b, p) => {
            take(m);
            take(b);
            take(p);
        }
        Term::Case(_, _, branches) => {
            if let Some(branches) = Rc::get_mut(branches) {
                for branch in branches {
                    take(&mut branch.body);
                }
            }
        }
        Term::Var(_) | Term::Def(_) | Term::Nat(_) | Term::Sort(_) | Term::Refl | Term::Meta(_) => {
        }
    }
}

#[derive(Clone, Debug)]
pub struct Branch {
    /// Names of the constructor's fields, bound in `body`.
    pub names: Vec<Name>,
    pub body: Rc<Term>,
}

impl Term {
    pub fn strip_loc(&self) -> &Term {
        let mut term = self;
        while let Term::Loc(_, inner) = term {
            term = inner;
        }
        term
    }

    /// Every sub-term the evaluator may evaluate is behind its own `Rc`, so it
    /// can hold on to it while evaluating (see `value.rs`).
    pub fn data(d: DataId, args: Vec<Term>) -> Term {
        Term::Data(d, args.into_iter().map(Rc::new).collect())
    }

    pub fn ctor(d: DataId, c: usize, fields: Vec<Term>) -> Term {
        Term::Ctor(d, c, fields.into_iter().map(Rc::new).collect())
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

    /// `strip_loc`, keeping the `Rc`.
    pub fn strip_loc_rc(term: &Rc<Term>) -> Rc<Term> {
        let mut term = term;
        while let Term::Loc(_, inner) = &**term {
            term = inner;
        }
        term.clone()
    }

    /// `peel_lams`, keeping the `Rc`.
    pub fn peel_lams_rc(term: &Rc<Term>, n: usize) -> Rc<Term> {
        let mut term = Term::strip_loc_rc(term);
        for _ in 0..n {
            term = match &*term {
                Term::Lam(_, _, body) => Term::strip_loc_rc(body),
                _ => panic!("internal error: expected {n} lambdas"),
            };
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
            Term::Var(_)
            | Term::Def(_)
            | Term::Nat(_)
            | Term::Sort(_)
            | Term::Refl
            | Term::Meta(_) => self.clone(),
            Term::Data(d, args) => {
                Term::data(*d, args.iter().map(|a| a.shift(by, cutoff)).collect())
            }
            Term::Ctor(d, c, args) => {
                Term::ctor(*d, *c, args.iter().map(|a| a.shift(by, cutoff)).collect())
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
                        body: Rc::new(b.body.shift(by, cutoff + b.names.len())),
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
            Term::Def(_) | Term::Nat(_) | Term::Sort(_) | Term::Refl | Term::Meta(_) => false,
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

#[cfg(test)]
mod tests {
    use super::*;

    fn v(ix: usize) -> Term {
        Term::Var(ix)
    }

    fn rc(t: Term) -> Rc<Term> {
        Rc::new(t)
    }

    fn lam(body: Term) -> Term {
        Term::Lam("x".into(), Icit::Explicit, rc(body))
    }

    fn pi(dom: Term, cod: Term) -> Term {
        Term::Pi("x".into(), Icit::Explicit, rc(dom), rc(cod))
    }

    fn data(args: Vec<Term>) -> Term {
        Term::data(DataId(0), args)
    }

    fn case(ix: usize, names: usize, body: Term) -> Term {
        Term::Case(
            ix,
            DataId(0),
            vec![Branch {
                names: (0..names).map(|_| "y".into()).collect(),
                body: Rc::new(body),
            }]
            .into(),
        )
    }

    /// Compares terms by their debug output (binder names are all the same here).
    fn assert_same(actual: Term, expected: Term) {
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    #[test]
    fn shift_moves_only_free_variables() {
        // \x -> x y, with y free: y moves, x doesn't.
        assert_same(
            lam(Term::app(v(0), v(1))).shift(2, 0),
            lam(Term::app(v(0), v(3))),
        );
        // Below the cutoff, nothing moves.
        assert_same(Term::app(v(0), v(1)).shift(5, 1), Term::app(v(0), v(6)));
    }

    #[test]
    fn shift_goes_under_every_binder_and_into_every_child() {
        // In (x : v0) -> v0 v1, the domain's v0 is free, the codomain's v0 is x.
        assert_same(
            pi(v(0), Term::app(v(0), v(1))).shift(1, 0),
            pi(v(1), Term::app(v(0), v(2))),
        );
        // A case binds its fields in its branches, and its scrutinee can move.
        assert_same(
            case(1, 2, Term::app(v(1), v(2))).shift(1, 0),
            case(2, 2, Term::app(v(1), v(3))),
        );
        assert_same(case(0, 1, v(0)).shift(1, 1), case(0, 1, v(0)));
        assert_same(
            Term::Eq(Some(rc(v(0))), rc(v(1)), rc(v(2))).shift(1, 0),
            Term::Eq(Some(rc(v(1))), rc(v(2)), rc(v(3))),
        );
        assert_same(
            Term::J(rc(v(0)), rc(v(1)), rc(v(2))).shift(1, 1),
            Term::J(rc(v(0)), rc(v(2)), rc(v(3))),
        );
        assert_same(
            Term::Ann(
                rc(data(vec![v(0)])),
                rc(Term::ctor(DataId(0), 0, vec![v(1)])),
            )
            .shift(3, 0),
            Term::Ann(
                rc(data(vec![v(3)])),
                rc(Term::ctor(DataId(0), 0, vec![v(4)])),
            ),
        );
    }

    #[test]
    fn mentions_finds_free_occurrences_only() {
        assert!(v(0).mentions(0));
        assert!(!v(1).mentions(0));
        assert!(lam(v(1)).mentions(0));
        assert!(!lam(v(0)).mentions(0), "bound by the lambda");
        assert!(
            pi(v(0), Term::Sort(Sort::Prop)).mentions(0),
            "free in the domain"
        );
        assert!(
            !pi(Term::Sort(Sort::Prop), v(0)).mentions(0),
            "bound in the codomain"
        );
        assert!(pi(Term::Sort(Sort::Prop), v(1)).mentions(0));
        assert!(Term::app(Term::Refl, v(0)).mentions(0));
        assert!(Term::app(v(0), Term::Refl).mentions(0));
        assert!(data(vec![Term::Refl, v(0)]).mentions(0));
        assert!(case(0, 1, Term::Refl).mentions(0), "the scrutinee");
        assert!(case(1, 2, v(2)).mentions(0), "under the branch's fields");
        assert!(!case(1, 2, v(1)).mentions(0), "a field, not the variable");
        assert!(Term::Eq(Some(rc(v(0))), rc(Term::Refl), rc(Term::Refl)).mentions(0));
        assert!(Term::Eq(None, rc(Term::Refl), rc(v(0))).mentions(0));
        assert!(Term::J(rc(Term::Refl), rc(Term::Refl), rc(v(0))).mentions(0));
        assert!(Term::J(rc(Term::Refl), rc(v(0)), rc(Term::Refl)).mentions(0));
        assert!(Term::Ann(rc(Term::Refl), rc(v(0))).mentions(0));
        assert!(!Term::Meta(0).mentions(0));
    }
}
