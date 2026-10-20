//! The index unifier (`unify_index.rs`, docs/proposals/indexed-families.md
//! §6.3), checked two ways (D149, §10 stage 2):
//!
//! - against a **reference unifier**, small enough to read in one sitting:
//!   named variables, naive substitution, no levels, over a toy signature
//!   that tells apart data constructors in `Type` and in `Prop`, opaque
//!   applications and type formers. Generated bounded problems go through
//!   both; the outcomes (solved, conflict, stuck) must agree, and for solved
//!   ones the *effects* of the two substitutions on the context's variables
//!   (each an instance of the other: equivalent most general unifiers can
//!   differ as maps);
//! - directly, for what the reference can't see, having no levels: every
//!   solution makes the original equations convertible, the refined context
//!   is well formed, the occurs check sees through types transitively, and
//!   refined types quoted at the branch's depth are well scoped.
//!
//! Unit tests of the unifier at both universes (test 24 of the note's §9)
//! are the fixed problems below.

mod common;

use std::collections::BTreeSet;

use common::*;
use stitchwort_core::check;
use stitchwort_core::term::Term;
use stitchwort_core::unify_index::{Outcome, Scope, unify};
use stitchwort_core::value::{Head, Value, conv, eval, quote};
use stitchwort_core::{DataId, DefId, Name, Sort};

// The toy signature

/// A term of the toy signature. Variables are the context's, by level.
#[derive(Clone, Debug, PartialEq, Eq)]
enum T {
    V(usize),
    // Nat: `Z | S n`, in `Type`.
    Z,
    S(Box<T>),
    /// The opaque `g : Nat -> Nat`: `g Z = Z`, `g (S n) = n`, stuck
    /// otherwise.
    G(Box<T>),
    // Fin: `FZ [n] : Fin (S n) | FS [n] (i : Fin n) : Fin (S n)`, in `Type`.
    Fz(Box<T>),
    Fs(Box<T>, Box<T>),
    // W: `Mk (n : Nat) (i : Fin (S n))`, in `Type`: a dependent field.
    Mk(Box<T>, Box<T>),
    // P: `A | B`, in `Prop`.
    A,
    B,
    // Hidden: `Hide (n : Nat)`, in `Prop`.
    Hide(Box<T>),
    // Tt: `MkT (h : P) (n : Nat)`, in `Type`: a proof field before data.
    Mkt(Box<T>, Box<T>),
    // Type formers, at type `Type`.
    TyNat,
    TyFin(Box<T>),
    TyW,
}

/// The type of a constraint.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Ty {
    Nat,
    Fin(T),
    W,
    P,
    Hidden,
    Tt,
    Type,
}

fn b(t: T) -> Box<T> {
    Box::new(t)
}

/// The context: names and types, outermost first.
fn context() -> Vec<(&'static str, Ty)> {
    vec![
        ("a", Ty::Nat),
        ("b", Ty::Nat),
        ("c", Ty::Nat),
        ("i", Ty::Fin(T::V(0))), // i : Fin a
        ("p", Ty::P),
        ("q", Ty::P),
        ("h", Ty::Hidden),
        ("w", Ty::W),
        ("t", Ty::Type),
        ("j", Ty::Fin(T::S(b(T::V(1))))), // j : Fin (S b)
    ]
}

impl T {
    /// Substitutes `by` for variable `x`, and computes `g`.
    fn subst(&self, x: usize, by: &T) -> T {
        self.map(&|v| if v == x { by.clone() } else { T::V(v) })
    }

    fn map(&self, f: &dyn Fn(usize) -> T) -> T {
        let m = |t: &T| b(t.map(f));
        match self {
            T::V(v) => f(*v),
            T::Z | T::A | T::B | T::TyNat | T::TyW => self.clone(),
            T::S(x) => T::S(m(x)),
            T::G(x) => match x.map(f) {
                T::Z => T::Z,
                T::S(n) => *n,
                other => T::G(b(other)),
            },
            T::Fz(n) => T::Fz(m(n)),
            T::Fs(n, i) => T::Fs(m(n), m(i)),
            T::Mk(n, i) => T::Mk(m(n), m(i)),
            T::Hide(n) => T::Hide(m(n)),
            T::Mkt(h, n) => T::Mkt(m(h), m(n)),
            T::TyFin(n) => T::TyFin(m(n)),
        }
    }

    fn vars(&self, out: &mut BTreeSet<usize>) {
        match self {
            T::V(v) => {
                out.insert(*v);
            }
            T::Z | T::A | T::B | T::TyNat | T::TyW => {}
            T::S(x) | T::G(x) | T::Fz(x) | T::Hide(x) | T::TyFin(x) => x.vars(out),
            T::Fs(x, y) | T::Mk(x, y) | T::Mkt(x, y) => {
                x.vars(out);
                y.vars(out);
            }
        }
    }

    /// The constructor and its fields, with their types (each given the
    /// left and the right fields before it), if it's a constructor.
    fn constructor(&self) -> Option<(&'static str, Vec<T>)> {
        Some(match self {
            T::Z => ("Z", vec![]),
            T::S(n) => ("S", vec![(**n).clone()]),
            T::Fz(n) => ("FZ", vec![(**n).clone()]),
            T::Fs(n, i) => ("FS", vec![(**n).clone(), (**i).clone()]),
            T::Mk(n, i) => ("Mk", vec![(**n).clone(), (**i).clone()]),
            T::Mkt(h, n) => ("MkT", vec![(**h).clone(), (**n).clone()]),
            _ => return None,
        })
    }
}

impl Ty {
    fn subst(&self, x: usize, by: &T) -> Ty {
        match self {
            Ty::Fin(n) => Ty::Fin(n.subst(x, by)),
            other => other.clone(),
        }
    }

    fn vars(&self, out: &mut BTreeSet<usize>) {
        if let Ty::Fin(n) = self {
            n.vars(out);
        }
    }

    /// The types of constructor `c`'s fields, from the earlier fields.
    fn field_types(c: &str, fields: &[T]) -> Vec<Ty> {
        match c {
            "Z" => vec![],
            "S" | "FZ" => vec![Ty::Nat],
            "FS" => vec![Ty::Nat, Ty::Fin(fields[0].clone())],
            "Mk" => vec![Ty::Nat, Ty::Fin(T::S(b(fields[0].clone())))],
            "MkT" => vec![Ty::P, Ty::Nat],
            _ => unreachable!(),
        }
    }
}

// The reference unifier

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Kind {
    Solved,
    Conflict,
    Stuck,
}

/// A constraint still to solve: its type given the left values and given
/// the right ones, which must agree when it's reached.
struct Item {
    ty_left: Ty,
    ty_right: Ty,
    lhs: T,
    rhs: T,
}

/// The reference unifier: the rules of §6.3.2, in order, on named
/// variables. Returns the outcome and, if solved, what each context
/// variable became.
fn reference(problem: &[(Ty, T, T)]) -> (Kind, Vec<T>) {
    let mut types: Vec<Ty> = context().into_iter().map(|(_, ty)| ty).collect();
    let mut value: Vec<T> = (0..types.len()).map(T::V).collect();
    let mut solved = vec![false; types.len()];
    let mut queue: Vec<Item> = problem
        .iter()
        .map(|(ty, l, r)| Item {
            ty_left: ty.clone(),
            ty_right: ty.clone(),
            // In normal form (`g Z` is `Z`): terms are compared syntactically.
            lhs: l.map(&T::V),
            rhs: r.map(&T::V),
        })
        .collect();
    while !queue.is_empty() {
        let Item {
            ty_left,
            ty_right,
            lhs,
            rhs,
        } = queue.remove(0);
        if ty_left != ty_right {
            return (Kind::Stuck, value);
        }
        let ty = ty_left;
        if lhs == rhs {
            continue;
        }
        let flexible = |t: &T| match t {
            T::V(v) if !solved[*v] => Some(*v),
            _ => None,
        };
        // Whether `y` occurs in `t` or, transitively, in its variables' types.
        let occurs = |y: usize, t: &T| {
            let mut todo = BTreeSet::new();
            t.vars(&mut todo);
            let mut seen = BTreeSet::new();
            while let Some(v) = todo.pop_first() {
                if v == y {
                    return true;
                }
                if seen.insert(v) {
                    types[v].vars(&mut todo);
                }
            }
            false
        };
        let solution = match (flexible(&lhs), flexible(&rhs)) {
            (Some(x), Some(y)) => {
                let (later, earlier) = (x.max(y), x.min(y));
                if !occurs(later, &T::V(earlier)) {
                    Some((later, T::V(earlier)))
                } else if !occurs(earlier, &T::V(later)) {
                    Some((earlier, T::V(later)))
                } else {
                    return (Kind::Stuck, value);
                }
            }
            (Some(x), None) if !occurs(x, &rhs) => Some((x, rhs.clone())),
            (None, Some(y)) if !occurs(y, &lhs) => Some((y, lhs.clone())),
            (Some(_), None) | (None, Some(_)) => return (Kind::Stuck, value),
            (None, None) => None,
        };
        if let Some((x, by)) = solution {
            solved[x] = true;
            for v in value.iter_mut() {
                *v = v.subst(x, &by);
            }
            for ty in types.iter_mut() {
                *ty = ty.subst(x, &by);
            }
            for item in queue.iter_mut() {
                item.ty_left = item.ty_left.subst(x, &by);
                item.ty_right = item.ty_right.subst(x, &by);
                item.lhs = item.lhs.subst(x, &by);
                item.rhs = item.rhs.subst(x, &by);
            }
            continue;
        }
        // Injectivity and conflict, only for data in `Type`.
        if matches!(ty, Ty::P | Ty::Hidden | Ty::Type) {
            return (Kind::Stuck, value);
        }
        let (Some((cl, fl)), Some((cr, fr))) = (lhs.constructor(), rhs.constructor()) else {
            return (Kind::Stuck, value);
        };
        if cl != cr {
            return (Kind::Conflict, value);
        }
        let (tl, tr) = (Ty::field_types(cl, &fl), Ty::field_types(cr, &fr));
        let fields = tl.into_iter().zip(tr).zip(fl.into_iter().zip(fr));
        let fields: Vec<Item> = fields
            .map(|((ty_left, ty_right), (lhs, rhs))| Item {
                ty_left,
                ty_right,
                lhs,
                rhs,
            })
            .collect();
        queue.splice(0..0, fields);
    }
    (Kind::Solved, value)
}

// The production unifier, on the same problems

/// The toy signature in the kernel.
struct Sig {
    p: Prelude,
    fin: DataId,
    w: DataId,
    prop_p: DataId,
    hidden: DataId,
    tt: DataId,
    g: DefId,
}

impl Sig {
    fn new() -> Sig {
        let mut p = Prelude::new();
        stitchwort_core::native::register_nat(&mut p.g, p.nat).expect("Nat");
        let nat = p.nat_ty();
        let fin = family(
            &mut p.g,
            "Fin",
            vec![],
            vec![("n", nat.clone())],
            Sort::Type(0),
        );
        let ctors = vec![
            ictor("FZ", vec![("n", nat.clone())], vec![p.succ(v(0))]),
            ictor(
                "FS",
                vec![("n", nat.clone()), ("i", Term::data(fin, vec![v(0)]))],
                vec![p.succ(v(1))],
            ),
        ];
        check::define_ctors(&mut p.g, fin, ctors).expect("Fin");
        let w = data(&mut p.g, "W", vec![], Sort::Type(0));
        let fields = vec![
            ("n", nat.clone()),
            ("i", Term::data(fin, vec![p.succ(v(0))])),
        ];
        check::define_ctors(&mut p.g, w, vec![ctor("Mk", fields)]).expect("W");
        let prop_p = data(&mut p.g, "P", vec![], Sort::Prop);
        check::define_ctors(&mut p.g, prop_p, vec![ctor("A", vec![]), ctor("B", vec![])])
            .expect("P");
        let hidden = data(&mut p.g, "Hidden", vec![], Sort::Prop);
        check::define_ctors(
            &mut p.g,
            hidden,
            vec![ctor("Hide", vec![("n", nat.clone())])],
        )
        .expect("Hidden");
        let tt = data(&mut p.g, "Tt", vec![], Sort::Type(0));
        let fields = vec![("h", Term::data(prop_p, vec![])), ("n", nat.clone())];
        check::define_ctors(&mut p.g, tt, vec![ctor("MkT", fields)]).expect("Tt");
        let body = lam(
            "x",
            case(0, p.nat, vec![(vec![], p.num(0)), (vec!["k"], v(0))]),
        );
        let g = define(&mut p.g, "g", arrow(nat.clone(), nat), body).expect("g");
        Sig {
            p,
            fin,
            w,
            prop_p,
            hidden,
            tt,
            g,
        }
    }

    /// `t` as a core term, with `depth` variables in scope (the context's
    /// first).
    fn term(&self, t: &T, depth: usize) -> Term {
        let go = |t: &T| self.term(t, depth);
        match t {
            T::V(l) => v(depth - 1 - l),
            T::Z => self.p.num(0),
            T::S(n) => self.p.succ(go(n)),
            T::G(n) => app(Term::Def(self.g), [go(n)]),
            T::Fz(n) => Term::ctor(self.fin, 0, vec![go(n)]),
            T::Fs(n, i) => Term::ctor(self.fin, 1, vec![go(n), go(i)]),
            T::Mk(n, i) => Term::ctor(self.w, 0, vec![go(n), go(i)]),
            T::A => Term::ctor(self.prop_p, 0, vec![]),
            T::B => Term::ctor(self.prop_p, 1, vec![]),
            T::Hide(n) => Term::ctor(self.hidden, 0, vec![go(n)]),
            T::Mkt(h, n) => Term::ctor(self.tt, 0, vec![go(h), go(n)]),
            T::TyNat => self.p.nat_ty(),
            T::TyFin(n) => Term::data(self.fin, vec![go(n)]),
            T::TyW => Term::data(self.w, vec![]),
        }
    }

    fn ty(&self, t: &Ty, depth: usize) -> Term {
        match t {
            Ty::Nat => self.p.nat_ty(),
            Ty::Fin(n) => Term::data(self.fin, vec![self.term(n, depth)]),
            Ty::W => Term::data(self.w, vec![]),
            Ty::P => Term::data(self.prop_p, vec![]),
            Ty::Hidden => Term::data(self.hidden, vec![]),
            Ty::Tt => Term::data(self.tt, vec![]),
            Ty::Type => ty(),
        }
    }

    /// A closed-over core term back in the toy signature.
    fn toy(&self, term: &Term, depth: usize) -> T {
        let go = |t: &Term| b(self.toy(t, depth));
        match term.strip_loc() {
            Term::Var(ix) => T::V(depth - 1 - ix),
            Term::Nat(n) => {
                let n: usize = n.to_string().parse().unwrap();
                (0..n).fold(T::Z, |t, _| T::S(b(t)))
            }
            Term::Ctor(d, c, args) if *d == self.p.nat => match c {
                0 => T::Z,
                _ => T::S(go(&args[0])),
            },
            Term::Ctor(d, c, args) if *d == self.fin => match c {
                0 => T::Fz(go(&args[0])),
                _ => T::Fs(go(&args[0]), go(&args[1])),
            },
            Term::Ctor(d, _, args) if *d == self.w => T::Mk(go(&args[0]), go(&args[1])),
            Term::Ctor(d, c, _) if *d == self.prop_p => [T::A, T::B][*c].clone(),
            Term::Ctor(d, _, args) if *d == self.hidden => T::Hide(go(&args[0])),
            Term::Ctor(d, _, args) if *d == self.tt => T::Mkt(go(&args[0]), go(&args[1])),
            Term::Data(d, _) if *d == self.p.nat => T::TyNat,
            Term::Data(d, args) if *d == self.fin => T::TyFin(go(&args[0])),
            Term::Data(d, _) if *d == self.w => T::TyW,
            Term::App(f, x, _) if matches!(f.strip_loc(), Term::Def(id) if *id == self.g) => {
                T::G(go(x))
            }
            other => panic!("unexpected {other:?}"),
        }
    }

    /// The context as a scope for the production unifier.
    fn scope(&self) -> Scope {
        let g = &self.p.g;
        let mut env = Vec::new();
        let mut types = Vec::new();
        for (l, (_, ty)) in context().iter().enumerate() {
            types.push(eval(g, &env, &self.ty(ty, l)).unwrap());
            env.push(Value::var(l));
        }
        Scope {
            env,
            types,
            extra: Vec::new(),
            rigid: Vec::new(),
        }
    }

    /// Runs the production unifier on `problem`: a telescope of independent
    /// binders, whose types may mention the context. Returns the outcome,
    /// what each context variable became, and the scope it left.
    fn production(&self, problem: &[(Ty, T, T)]) -> (Kind, Vec<T>, Scope) {
        let g = &self.p.g;
        let n = context().len();
        let mut scope = self.scope();
        let vars: Vec<Value> = (0..n).map(Value::var).collect();
        // Binder `k`'s type is in the context of the variables and the
        // binders before it, which it doesn't mention.
        let binders: Vec<(Name, Term)> = problem
            .iter()
            .enumerate()
            .map(|(k, (ty, _, _))| {
                let ty = self.ty(ty, n).shift(g, k, 0).unwrap();
                ("x".into(), ty)
            })
            .collect();
        let values = |side: fn(&(Ty, T, T)) -> &T| {
            problem
                .iter()
                .map(|c| eval(g, &vars, &self.term(side(c), n)).unwrap())
                .collect::<Vec<_>>()
        };
        let (lhs, rhs) = (values(|c| &c.1), values(|c| &c.2));
        let outcome = unify(g, &mut scope, &binders, vars, lhs, rhs).unwrap();
        let kind = match outcome {
            Outcome::Solved(_) => Kind::Solved,
            Outcome::Conflict(_) => Kind::Conflict,
            Outcome::Stuck(..) => Kind::Stuck,
        };
        let effect = scope
            .env
            .iter()
            .map(|value| self.toy(&quote(g, n, value).unwrap(), n))
            .collect();
        (kind, effect, scope)
    }
}

/// Whether the substitution `outer` leaves `inner`'s effect unchanged:
/// applying `outer` to what each variable became under `inner` gives what
/// it became under `outer`. Both ways round, the two are equivalent.
fn instance(outer: &[T], inner: &[T]) -> bool {
    inner
        .iter()
        .zip(outer)
        .all(|(i, o)| i.map(&|v| outer[v].clone()) == *o)
}

// Generating problems

/// A small deterministic generator (xorshift).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// A term of type `ty`, at most `depth` deep, if there is one.
fn gen_term(r: &mut Rng, ty: &Ty, depth: usize) -> Option<T> {
    let vars: Vec<T> = context()
        .iter()
        .enumerate()
        .filter(|(_, (_, t))| t == ty)
        .map(|(l, _)| T::V(l))
        .collect();
    let mut options: Vec<T> = vars;
    let leaf = depth == 0;
    match ty {
        Ty::Nat => {
            options.push(T::Z);
            if !leaf {
                options.push(T::S(b(gen_term(r, &Ty::Nat, depth - 1)?)));
                options.push(T::G(b(gen_term(r, &Ty::Nat, depth - 1)?)));
            }
        }
        Ty::Fin(n) => {
            if let T::S(k) = n {
                options.push(T::Fz(k.clone()));
                if !leaf && let Some(i) = gen_term(r, &Ty::Fin((**k).clone()), depth - 1) {
                    options.push(T::Fs(k.clone(), b(i)));
                }
            }
        }
        Ty::W => {
            let n = gen_term(r, &Ty::Nat, depth.saturating_sub(1))?;
            let i = gen_term(r, &Ty::Fin(T::S(b(n.clone()))), depth.saturating_sub(1))?;
            options.push(T::Mk(b(n), b(i)));
        }
        Ty::P => options.extend([T::A, T::B]),
        Ty::Hidden => options.push(T::Hide(b(gen_term(r, &Ty::Nat, depth.saturating_sub(1))?))),
        Ty::Tt => {
            let h = gen_term(r, &Ty::P, 0)?;
            let n = gen_term(r, &Ty::Nat, depth.saturating_sub(1))?;
            options.push(T::Mkt(b(h), b(n)));
        }
        Ty::Type => {
            options.extend([T::TyNat, T::TyW]);
            if !leaf {
                options.push(T::TyFin(b(gen_term(r, &Ty::Nat, depth - 1)?)));
            }
        }
    }
    if options.is_empty() {
        return None;
    }
    let pick = r.below(options.len());
    Some(options.swap_remove(pick))
}

fn gen_type(r: &mut Rng) -> Ty {
    let types = [
        Ty::Nat,
        Ty::Nat,
        Ty::Fin(T::S(b(T::S(b(T::Z))))),
        Ty::Fin(T::S(b(T::V(1)))),
        Ty::Fin(T::V(0)),
        Ty::W,
        Ty::W,
        Ty::P,
        Ty::Hidden,
        Ty::Tt,
        Ty::Type,
    ];
    types[r.below(types.len())].clone()
}

fn gen_problem(r: &mut Rng) -> Vec<(Ty, T, T)> {
    let n = 1 + r.below(3);
    let mut problem = Vec::new();
    while problem.len() < n {
        let ty = gen_type(r);
        let depth = r.below(4);
        if let (Some(l), Some(rh)) = (gen_term(r, &ty, depth), gen_term(r, &ty, depth)) {
            // As the reference compares terms syntactically, they start in
            // normal form (`g Z` is `Z`).
            problem.push((ty, l.map(&T::V), rh.map(&T::V)));
        }
    }
    problem
}

#[test]
fn production_agrees_with_the_reference_unifier() {
    let sig = Sig::new();
    let mut r = Rng(0x5eed_1234_abcd_ef01);
    let mut counts = [0usize; 3];
    for case in 0..4000 {
        let problem = gen_problem(&mut r);
        let (kind, effect) = reference(&problem);
        let (prod_kind, prod_effect, _) = sig.production(&problem);
        assert_eq!(
            kind, prod_kind,
            "case {case}: outcomes differ on {problem:?}"
        );
        counts[kind as usize] += 1;
        if kind == Kind::Solved {
            assert!(
                instance(&prod_effect, &effect) && instance(&effect, &prod_effect),
                "case {case}: effects differ on {problem:?}:\n  reference {effect:?}\n  \
                 production {prod_effect:?}"
            );
        }
    }
    // Every outcome is exercised.
    assert!(counts.iter().all(|&n| n > 200), "{counts:?}");
}

// Fixed problems, at both universes (test 24)

fn outcome(sig: &Sig, problem: &[(Ty, T, T)]) -> Kind {
    let (kind, effect) = reference(problem);
    let (prod, prod_effect, _) = sig.production(problem);
    assert_eq!(kind, prod);
    if kind == Kind::Solved {
        assert!(instance(&prod_effect, &effect) && instance(&effect, &prod_effect));
    }
    prod
}

#[test]
fn constructors_are_told_apart_only_in_type() {
    let sig = Sig::new();
    use Kind::*;
    let s = |t| T::S(b(t));
    // Data in `Type`: conflict and injectivity.
    assert_eq!(outcome(&sig, &[(Ty::Nat, T::Z, s(T::V(0)))]), Conflict);
    assert_eq!(outcome(&sig, &[(Ty::Nat, s(T::Z), s(T::V(0)))]), Solved);
    let mk_t = |h, n| T::Mkt(b(h), b(n));
    // Test 25's shape: a proof field before data.
    assert_eq!(
        outcome(&sig, &[(Ty::Tt, mk_t(T::A, T::Z), mk_t(T::B, s(T::Z)))]),
        Stuck
    );
    assert_eq!(
        outcome(&sig, &[(Ty::Tt, mk_t(T::V(4), T::Z), mk_t(T::A, s(T::Z)))]),
        Conflict
    );
    assert_eq!(
        outcome(&sig, &[(Ty::Tt, mk_t(T::A, T::Z), mk_t(T::A, s(T::Z)))]),
        Conflict
    );
    // Proofs: deletion and solution only (tests 22, 23).
    assert_eq!(outcome(&sig, &[(Ty::P, T::A, T::B)]), Stuck);
    assert_eq!(outcome(&sig, &[(Ty::P, T::A, T::A)]), Solved);
    assert_eq!(outcome(&sig, &[(Ty::P, T::V(4), T::B)]), Solved);
    let hide = |n| T::Hide(b(n));
    assert_eq!(
        outcome(&sig, &[(Ty::Hidden, hide(T::Z), hide(s(T::Z)))]),
        Stuck
    );
    assert_eq!(
        outcome(&sig, &[(Ty::Hidden, T::V(6), hide(s(T::Z)))]),
        Solved
    );
    // Types: never taken apart (test 6).
    let fin = |n| T::TyFin(b(n));
    assert_eq!(outcome(&sig, &[(Ty::Type, fin(T::V(0)), fin(T::Z))]), Stuck);
    assert_eq!(outcome(&sig, &[(Ty::Type, T::TyNat, T::TyW)]), Stuck);
    assert_eq!(outcome(&sig, &[(Ty::Type, T::V(8), fin(T::Z))]), Solved);
    // Opaque applications (test 4) and the occurs check (test 7).
    assert_eq!(outcome(&sig, &[(Ty::Nat, T::G(b(T::V(0))), T::Z)]), Stuck);
    assert_eq!(
        outcome(&sig, &[(Ty::Nat, T::G(b(s(T::V(0)))), T::V(1))]),
        Solved
    );
    assert_eq!(outcome(&sig, &[(Ty::Nat, T::V(0), s(T::V(0)))]), Stuck);
}

#[test]
fn dependent_fields_are_compared_in_order() {
    // Test 19: `Mk (g a) i' = Mk (S b) j'` stops at `g a = S b`; with the
    // first fields solvable, the second is compared at the solved type.
    let sig = Sig::new();
    let s = |t| T::S(b(t));
    let mk = |n, i| T::Mk(b(n), b(i));
    let fz = |n| T::Fz(b(n));
    let stuck = [(
        Ty::W,
        mk(T::G(b(T::V(0))), fz(T::G(b(T::V(0))))),
        mk(s(T::V(1)), fz(s(T::V(1)))),
    )];
    assert_eq!(outcome(&sig, &stuck), Kind::Stuck);
    let fine = [(Ty::W, mk(T::V(1), T::V(9)), mk(T::V(2), fz(T::V(2))))];
    assert_eq!(outcome(&sig, &fine), Kind::Solved);
}

// Direct checks on the production unifier

/// Checks what a solved problem left: the original equations hold, every
/// type is well scoped and mentions no solved variable, and "the type of
/// `x` mentions `y`" among the variables still flexible has no cycle.
fn check_invariants(sig: &Sig, problem: &[(Ty, T, T)], scope: &Scope) {
    let g = &sig.p.g;
    let n = scope.level();
    for (ty, l, r) in problem {
        let (l, r) = (sig.term(l, n), sig.term(r, n));
        let (l, r) = (
            eval(g, &scope.env, &l).unwrap(),
            eval(g, &scope.env, &r).unwrap(),
        );
        assert!(
            conv(g, n, &l, &r).unwrap(),
            "{ty:?}: the equation doesn't hold"
        );
    }
    let flexible: Vec<bool> = (0..n)
        .map(|l| scope.flexible(&Value::var(l)).is_some())
        .collect();
    let mut mentions = vec![BTreeSet::new(); n];
    for (l, ty) in scope.types.iter().enumerate() {
        let term = quote(g, n, ty).unwrap();
        for (t, binders) in term.subterms() {
            if let Term::Var(ix) = t
                && *ix >= binders
            {
                let level = n.checked_sub(ix - binders + 1).expect("well scoped");
                assert!(flexible[level], "a type mentions a solved variable");
                mentions[l].insert(level);
            }
        }
    }
    // No cycles: repeatedly remove a variable whose type mentions none left.
    let mut left: BTreeSet<usize> = (0..n).filter(|l| flexible[*l]).collect();
    while let Some(&l) = left
        .iter()
        .find(|l| mentions[**l].iter().all(|m| !left.contains(m) || m == *l))
    {
        assert!(
            !mentions[l].contains(&l),
            "a type mentions its own variable"
        );
        left.remove(&l);
    }
    assert!(left.is_empty(), "the types' dependencies have a cycle");
}

#[test]
fn solutions_make_the_equations_hold_and_keep_the_context_well_formed() {
    let sig = Sig::new();
    let mut r = Rng(0x0dd_ba11);
    let mut checked = 0;
    for _ in 0..1500 {
        let problem = gen_problem(&mut r);
        let (kind, _, scope) = sig.production(&problem);
        if kind == Kind::Solved {
            check_invariants(&sig, &problem, &scope);
            checked += 1;
        }
    }
    assert!(checked > 300, "{checked}");
}

#[test]
fn the_occurs_check_looks_through_types_transitively() {
    // y : Nat, P : Fin y -> Type, z : Fin y, u : P z, k : P z -> Nat.
    // `y = k u` mentions only `k` and `u`, but their types mention `P` and
    // `z`, whose types mention `y`.
    let sig = Sig::new();
    let g = &sig.p.g;
    let nat = sig.p.nat_ty();
    let fin = |n| Term::data(sig.fin, vec![n]);
    let telescope = [
        ("n0", nat.clone()),                          // 0: an unrelated Nat
        ("y", nat.clone()),                           // 1
        ("P", arrow(fin(v(0)), ty())),                // 2
        ("z", fin(v(1))),                             // 3
        ("u", app(v(1), [v(0)])),                     // 4: P z
        ("k", arrow(app(v(2), [v(1)]), nat.clone())), // 5: P z -> Nat
    ];
    let scope = || {
        let mut env = Vec::new();
        let mut types = Vec::new();
        for (l, (_, ty)) in telescope.iter().enumerate() {
            types.push(eval(g, &env, ty).unwrap());
            env.push(Value::var(l));
        }
        Scope {
            env,
            types,
            extra: Vec::new(),
            rigid: Vec::new(),
        }
    };
    let k_u = app(v(0), [v(1)]); // at depth 6: k = v0, u = v1
    let solve = |x: usize| {
        let mut scope = scope();
        let vars: Vec<Value> = (0..6).map(Value::var).collect();
        let lhs = eval(g, &vars, &v(5 - x)).unwrap();
        let rhs = eval(g, &vars, &k_u).unwrap();
        let binders = vec![(Name::from("e"), nat.clone().shift(g, 6, 0).unwrap())];
        unify(g, &mut scope, &binders, vars, vec![lhs], vec![rhs]).unwrap()
    };
    assert!(
        matches!(solve(1), Outcome::Stuck(..)),
        "y occurs, through types"
    );
    // Paired: an unrelated variable is solved.
    assert!(matches!(solve(0), Outcome::Solved(_)));
}

#[test]
fn refined_types_are_quoted_at_the_branch_depth() {
    // n : Nat, Q : Nat -> Type, h : Q n, then a field m : Nat bound later;
    // solving n := Succ m refines h's type to Q (Succ m), mentioning `m`.
    let sig = Sig::new();
    let g = &sig.p.g;
    let nat = sig.p.nat_ty();
    let telescope = [
        ("n", nat.clone()),
        ("Q", arrow(nat.clone(), ty())),
        ("h", app(v(0), [v(1)])),
        ("m", nat.clone()),
    ];
    let mut env = Vec::new();
    let mut types = Vec::new();
    for (l, (_, ty)) in telescope.iter().enumerate() {
        types.push(eval(g, &env, ty).unwrap());
        env.push(Value::var(l));
    }
    let mut scope = Scope {
        env,
        types,
        extra: Vec::new(),
        rigid: Vec::new(),
    };
    let vars: Vec<Value> = (0..4).map(Value::var).collect();
    let lhs = Value::var(0);
    let rhs = eval(g, &vars, &sig.p.succ(v(0))).unwrap();
    let binders = vec![(Name::from("e"), nat.shift(g, 4, 0).unwrap())];
    let outcome = unify(g, &mut scope, &binders, vars, vec![lhs], vec![rhs]).unwrap();
    assert!(matches!(outcome, Outcome::Solved(ref s) if s.len() == 1 && s[0].0 == 0));
    let h_ty = quote(g, 4, &scope.types[2]).unwrap();
    // `Q (Succ m)` at depth 4: Q is v2, m is v0.
    let names: Vec<Name> = ["n", "Q", "h", "m"].map(Name::from).to_vec();
    assert_eq!(
        stitchwort_core::pretty::term(g, &names, &h_ty),
        "Q (Succ m)"
    );
    assert!(h_ty.subterms().all(|(t, binders)| match t {
        Term::Var(ix) => *ix < 4 + binders,
        _ => true,
    }));
    // `n` now stands for `Succ m`, and is no longer flexible.
    assert!(scope.flexible(&Value::var(0)).is_none());
    assert!(matches!(&scope.env[3], Value::Neutral(Head::Var(3), _)));
}
