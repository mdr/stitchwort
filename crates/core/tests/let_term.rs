//! The kernel's transparent `let`, `Let(x, A, v, b)`, on hand-built core
//! terms (docs/proposals/let.md §6.2, stage 2): its typing rule, the NbE
//! invariant (a `let` takes a slot but no variable level, §A.2), evaluation,
//! hashing and termination. The elaborator doesn't produce `Let` yet
//! (stage 3), so everything here is the kernel's own checking.

mod common;

use std::rc::Rc;
use std::time::{Duration, Instant};

use common::*;
use stitchwort_core::check::{self, infer_closed};
use stitchwort_core::hash::def_hash;
use stitchwort_core::value::{conv, eval, quote};
use stitchwort_core::{DefId, Globals, Limits, Sort, Term};

fn rc(t: Term) -> Rc<Term> {
    Rc::new(t)
}

/// `let x : ty := value; body`.
fn let_(x: &str, ty: Term, value: Term, body: Term) -> Term {
    Term::Let(x.into(), rc(ty), rc(value), rc(body))
}

fn ann(e: Term, ty: Term) -> Term {
    Term::Ann(rc(e), rc(ty))
}

fn code<T>(r: Result<T, &'static str>) -> &'static str {
    r.err().unwrap_or("ok")
}

fn infer_code(g: &Globals, term: &Term) -> &'static str {
    infer_closed(g, term, span()).err().map_or("ok", |d| d.code)
}

/// The prelude, plus a length-indexed vector made by a type-level function
/// (core data types have no indices): `Vec 0 = Unit`, `Vec (k + 1) = Pair
/// Nat (Vec k)`, and `zeros : (n : Nat) -> Vec n`.
struct Vecs {
    p: Prelude,
    vec: DefId,
    zeros: DefId,
}

impl Vecs {
    fn new() -> Vecs {
        let mut p = Prelude::new();
        let nat = p.nat;
        let unit = data(&mut p.g, "Unit", vec![], Sort::Type(0));
        check::define_ctors(&mut p.g, unit, vec![ctor("tt", vec![])]).expect("Unit");
        let pair = data(
            &mut p.g,
            "Pair",
            vec![("a", ty()), ("b", ty())],
            Sort::Type(0),
        );
        check::define_ctors(
            &mut p.g,
            pair,
            vec![ctor("MkPair", vec![("fst", v(1)), ("snd", v(1))])],
        )
        .expect("Pair");
        let nat_ty = p.nat_ty();
        let vec = declare(&mut p.g, "Vec", arrow(nat_ty.clone(), ty()));
        let body = lam(
            "n",
            case(
                0,
                nat,
                vec![
                    (vec![], Term::Data(unit, vec![])),
                    (
                        vec!["k"],
                        Term::data(pair, vec![p.nat_ty(), app(Term::Def(vec), [v(0)])]),
                    ),
                ],
            ),
        );
        check::define_def(&mut p.g, vec, &body).expect("Vec");
        let zeros = declare(
            &mut p.g,
            "zeros",
            pi("n", nat_ty, app(Term::Def(vec), [v(0)])),
        );
        let body = lam(
            "n",
            case(
                0,
                nat,
                vec![
                    (vec![], Term::ctor(unit, 0, vec![])),
                    (
                        vec!["k"],
                        Term::ctor(pair, 0, vec![p.num(0), app(Term::Def(zeros), [v(0)])]),
                    ),
                ],
            ),
        );
        check::define_def(&mut p.g, zeros, &body).expect("zeros");
        Vecs { p, vec, zeros }
    }

    fn vec_of(&self, n: Term) -> Term {
        app(Term::Def(self.vec), [n])
    }
}

// The typing rule

/// `let n := 3; (zeros n : Vec n)` has type `Vec 3`: the body's type, with
/// `n` replaced by its value, usable (and quoted) outside the `let`.
#[test]
fn a_dependent_let_has_its_body_type_with_the_value_put_in() {
    let mut vs = Vecs::new();
    let three = vs.p.num(3);
    let term = let_(
        "n",
        vs.p.nat_ty(),
        three.clone(),
        ann(app(Term::Def(vs.zeros), [v(0)]), vs.vec_of(v(0))),
    );
    let (_, ty) = infer_closed(&vs.p.g, &term, span()).expect("checks");
    let g = &vs.p.g;
    let expected = eval(g, &[], &vs.vec_of(three.clone())).unwrap();
    assert!(conv(g, 0, &ty, &expected).unwrap());
    // Quoted outside the `let`, at depth 0, the type is closed: it checks
    // as a type in the empty context.
    let quoted = quote(g, 0, &ty).unwrap();
    assert_eq!(
        infer_code(g, &quoted),
        "ok",
        "the type mentions no variable: {quoted:?}"
    );
    // And as a definition's body, against `Vec 3`.
    let vec3 = vs.vec_of(three);
    assert_eq!(code(define(&mut vs.p.g, "z", vec3, term)), "ok");
}

/// A `let` whose type is a universe: `let T : Type := Nat; (2 : T)`.
#[test]
fn a_let_can_define_a_type() {
    let p = Prelude::new();
    let term = let_("T", ty(), p.nat_ty(), ann(p.num(2), v(0)));
    let (_, ty) = infer_closed(&p.g, &term, span()).expect("checks");
    assert!(conv(&p.g, 0, &ty, &eval(&p.g, &[], &p.nat_ty()).unwrap()).unwrap());
}

/// The value is visible: `let n := 2; (rfl : n + n = 4)` checks, but the
/// function form, `(\n => (rfl : n + n = 4)) 2`, which checks the body for
/// every `n`, doesn't.
#[test]
fn the_body_sees_the_value() {
    let p = Prelude::new();
    let claim = |n: Term| eq(None, p.plus(n.clone(), n), p.num(4));
    let transparent = let_("n", p.nat_ty(), p.num(2), ann(Term::Refl, claim(v(0))));
    assert_eq!(infer_code(&p.g, &transparent), "ok");
    let opaque = app(
        ann(lam("n", Term::Refl), pi("n", p.nat_ty(), claim(v(0)))),
        [p.num(2)],
    );
    assert_eq!(infer_code(&p.g, &opaque), "E-REFL");
}

/// A proof `let`, used twice: its type is a proposition, which the rule
/// treats like any other type.
#[test]
fn a_proof_let_can_be_used_twice() {
    let mut p = Prelude::new();
    let fact = eq(None, p.plus(p.num(2), p.num(2)), p.num(4));
    let (nat, zero) = (p.nat_ty(), p.num(0));
    let f = define(
        &mut p.g,
        "both",
        arrow(fact.clone(), arrow(fact.clone(), nat)),
        lam("p", lam("q", zero)),
    )
    .expect("both");
    let body = let_("p", fact, Term::Refl, app(Term::Def(f), [v(0), v(0)]));
    let nat = p.nat_ty();
    assert_eq!(code(define(&mut p.g, "usesTwice", nat, body)), "ok");
}

/// A dependent function after a `let`, whose type is used outside it:
/// `let n := 2; (\m => rfl : (m : Nat) -> n + m = n + m)`. Its type, quoted
/// at depth 0, mentions only its own binder, and is `(m : Nat) -> 2 + m = 2
/// + m`.
#[test]
fn a_dependent_function_type_after_a_let_is_closed_outside_it() {
    let p = Prelude::new();
    let g = &p.g;
    let fn_ty = |n: Term, m: Term| eq(None, p.plus(n.clone(), m.clone()), p.plus(n, m));
    let term = let_(
        "n",
        p.nat_ty(),
        p.num(2),
        ann(lam("m", Term::Refl), pi("m", p.nat_ty(), fn_ty(v(1), v(0)))),
    );
    let (term, ty) = infer_closed(g, &term, span()).expect("checks");
    let quoted = quote(g, 0, &ty).unwrap();
    assert_eq!(infer_code(g, &quoted), "ok", "closed: {quoted:?}");
    let (expected, _) =
        infer_closed(g, &pi("m", p.nat_ty(), fn_ty(p.num(2), v(0))), span()).unwrap();
    let expected = eval(g, &[], &expected).unwrap();
    assert!(conv(g, 0, &ty, &expected).unwrap());
    // Its value is a function, closed too, and applying it to a fresh
    // variable (level 0, the next free one outside) gives a proof.
    let value = eval(g, &[], &term).unwrap();
    assert_eq!(
        format!("{:?}", quote(g, 0, &value).unwrap()),
        format!("{:?}", lam("m", Term::Refl))
    );
}

/// Nested `let`s under binders: `\a => let x := a + 1; \b => let y := x + b;
/// (rfl : y = x + b)` against `(a b : Nat) -> (a + 1) + b = (a + 1) + b`.
/// Inside, `a` and `b` are variable levels 0 and 2: `x`'s slot (1) has no
/// level, so quoting at a depth that counts it must leave the gap.
#[test]
fn nested_lets_under_binders() {
    let mut p = Prelude::new();
    let goal = |a: Term, b: Term| {
        let lhs = p.plus(p.plus(a, p.num(1)), b);
        eq(None, lhs.clone(), lhs)
    };
    let ty = pi("a", p.nat_ty(), pi("b", p.nat_ty(), goal(v(1), v(0))));
    // Under `y`: y = 0, b = 1, x = 2, a = 3.
    let body = lam(
        "a",
        let_(
            "x",
            p.nat_ty(),
            p.plus(v(0), p.num(1)),
            lam(
                "b",
                let_(
                    "y",
                    p.nat_ty(),
                    p.plus(v(1), v(0)),
                    ann(Term::Refl, eq(None, v(0), p.plus(v(2), v(1)))),
                ),
            ),
        ),
    );
    assert_eq!(
        code(define(&mut p.g, "nested", ty.clone(), body.clone())),
        "ok"
    );
    // Its normal form is `\a => \b => rfl`: no `let` is quoted back.
    let value = eval(&p.g, &[], &body).unwrap();
    let normal = quote(&p.g, 0, &value).unwrap();
    assert_eq!(
        format!("{normal:?}"),
        format!("{:?}", lam("a", lam("b", Term::Refl)))
    );
    // The same body against a goal that isn't what `y` is: rejected.
    let wrong = pi("a", p.nat_ty(), pi("b", p.nat_ty(), eq(None, v(0), v(1))));
    let body_wrong = lam(
        "a",
        let_(
            "x",
            p.nat_ty(),
            p.plus(v(0), p.num(1)),
            lam("b", let_("y", p.nat_ty(), p.plus(v(1), v(0)), Term::Refl)),
        ),
    );
    assert_eq!(code(define(&mut p.g, "wrong", wrong, body_wrong)), "E-REFL");
}

// Rejections

#[test]
fn rejects_a_value_that_doesnt_match_its_annotation() {
    let p = Prelude::new();
    assert_eq!(
        infer_code(&p.g, &let_("x", p.nat_ty(), Term::Refl, v(0))),
        "E-TYPE-MISMATCH"
    );
    let not_nat = let_("x", p.nat_ty(), ann(Term::Sort(Sort::Prop), ty()), v(0));
    assert_eq!(infer_code(&p.g, &not_nat), "E-TYPE-MISMATCH");
}

#[test]
fn rejects_an_annotation_that_isnt_a_type() {
    let p = Prelude::new();
    assert_eq!(
        infer_code(&p.g, &let_("x", p.num(3), p.num(3), v(0))),
        "E-NOT-A-TYPE"
    );
}

/// The value is known exactly: `let n := 3; (rfl : n = 4)` is refused.
#[test]
fn rejects_a_claim_about_the_value_that_is_false() {
    let p = Prelude::new();
    let term = let_(
        "n",
        p.nat_ty(),
        p.num(3),
        ann(Term::Refl, eq(None, v(0), p.num(4))),
    );
    assert_eq!(infer_code(&p.g, &term), "E-REFL");
}

/// A `let` is a leaf: no case tree under it (docs/proposals/let.md §A.5).
#[test]
fn rejects_a_case_under_a_let() {
    let mut p = Prelude::new();
    let nat = p.nat;
    let ty = arrow(p.nat_ty(), p.nat_ty());
    let body = lam(
        "n",
        let_(
            "m",
            p.nat_ty(),
            v(0),
            case(1, nat, vec![(vec![], p.num(0)), (vec!["k"], p.num(1))]),
        ),
    );
    assert_eq!(code(define(&mut p.g, "f", ty, body)), "E-MALFORMED");
}

/// A definition the kernel accepted and hashed, with its `let`'s value then
/// changed (as a buggy elaborator, or a tampered store, might): the kernel
/// itself refuses it, and the hash tells the two apart.
#[test]
fn a_mutated_let_is_refused_by_the_kernel() {
    let make = |p: &Prelude, value: usize| {
        let_(
            "n",
            p.nat_ty(),
            p.num(value),
            ann(Term::Refl, eq(None, v(0), p.num(3))),
        )
    };
    let claim = |p: &Prelude| eq(None, p.num(3), p.num(3));
    let mut p = Prelude::new();
    let (good, bad, ty) = (make(&p, 3), make(&p, 4), claim(&p));
    let id = define(&mut p.g, "good", ty.clone(), good.clone()).expect("checks");
    let hash = def_hash(&p.g, id).unwrap().expect("final");
    assert_eq!(code(define(&mut p.g, "bad", ty.clone(), bad)), "E-REFL");

    // The same body as a function applied to the value hashes differently
    // (and is refused: the function form can't see the value).
    let mut q = Prelude::new();
    let id = define(&mut q.g, "good", ty.clone(), good).unwrap();
    assert_eq!(def_hash(&q.g, id).unwrap(), Some(hash), "deterministic");
    let mut r = Prelude::new();
    let five = let_(
        "n",
        r.nat_ty(),
        r.num(5),
        ann(Term::Refl, eq(None, r.num(3), r.num(3))),
    );
    let id = define(&mut r.g, "good", ty, five).unwrap();
    assert_ne!(
        def_hash(&r.g, id).unwrap(),
        Some(hash),
        "the value is hashed"
    );
}

// Evaluation

/// `let` is strict and shared: the value is computed once, and the body sees
/// it wherever it's used, including inside a function made in the body.
#[test]
fn evaluation_puts_the_value_in_the_environment() {
    let p = Prelude::new();
    let g = &p.g;
    // let x := 2 + 3; \y => x + y, applied to 1.
    let f = let_(
        "x",
        p.nat_ty(),
        p.plus(p.num(2), p.num(3)),
        lam("y", p.plus(v(1), v(0))),
    );
    let applied = app(f, [p.num(1)]);
    let value = eval(g, &[], &applied).unwrap();
    assert_eq!(
        format!("{:?}", quote(g, 0, &value).unwrap()),
        format!(
            "{:?}",
            quote(g, 0, &eval(g, &[], &p.num(6)).unwrap()).unwrap()
        )
    );
    // On an open term the value stays stuck, and the body has it.
    let open = let_("x", p.nat_ty(), p.plus(v(0), p.num(1)), p.plus(v(0), v(0)));
    let value = eval(g, &[stitchwort_core::Value::var(0)], &open).unwrap();
    let x = p.plus(v(0), p.num(1));
    let expected = eval(g, &[stitchwort_core::Value::var(0)], &p.plus(x.clone(), x)).unwrap();
    assert!(conv(g, 1, &value, &expected).unwrap());
}

// Termination: `let x := v` is exactly as small as `v` (§6.1 rule 3)

/// `f n = case n of Zero -> 0; Succ k -> body`, with `k` as variable 0 and
/// `n` as variable 1 in `body`.
fn recursive(p: &mut Prelude, name: &str, succ: impl Fn(DefId) -> Term) -> &'static str {
    let nat = p.nat;
    let (nat_ty, zero) = (p.nat_ty(), p.num(0));
    let id = declare(&mut p.g, name, arrow(nat_ty.clone(), nat_ty));
    let body = lam(
        "n",
        case(0, nat, vec![(vec![], zero), (vec!["k"], succ(id))]),
    );
    check::define_def(&mut p.g, id, &body)
        .err()
        .map_or("ok", |d| d.code)
}

#[test]
fn a_let_of_a_smaller_value_is_smaller() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let r = recursive(&mut p, "down", |f| {
        let_("y", nat.clone(), v(0), app(Term::Def(f), [v(0)]))
    });
    assert_eq!(r, "ok");
}

#[test]
fn a_let_of_the_parameter_is_not_smaller() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let r = recursive(&mut p, "same", |f| {
        let_("y", nat.clone(), v(1), app(Term::Def(f), [v(0)]))
    });
    assert_eq!(r, "E-TERMINATION");
    // Rebuilt from the match, it's equal to the parameter: still not smaller.
    let n = p.nat;
    let rebuilt = recursive(&mut p, "rebuilt", |f| {
        let_(
            "y",
            nat.clone(),
            Term::ctor(n, 1, vec![v(0)]),
            app(Term::Def(f), [v(0)]),
        )
    });
    assert_eq!(rebuilt, "E-TERMINATION");
}

/// A recursive call can't hide in a `let`'s value.
#[test]
fn a_call_in_a_lets_value_is_checked() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let r = recursive(&mut p, "hidden", |f| {
        let_("y", nat.clone(), app(Term::Def(f), [v(1)]), v(0))
    });
    assert_eq!(r, "E-TERMINATION");
    let ok = recursive(&mut p, "fine", |f| {
        let_("y", nat.clone(), app(Term::Def(f), [v(0)]), v(0))
    });
    assert_eq!(ok, "ok");
}

// Cost

/// Twenty nested `let`s on an unknown `a`, each the previous one used twice:
/// `x1 := a + a; x2 := x1 + x1; …`. A claim about `x20` is checked and,
/// being false, printed. Values share, but a normal form would be 2^20 times
/// `a`: it must finish under the default limits, with an answer or a
/// resource error, not hang (docs/proposals/let.md §4.3).
#[test]
fn deeply_nested_lets_finish_under_the_budget() {
    let p = Prelude::new();
    let g = &p.g;
    let depth = 20;
    // Under the lets: x_depth is variable 0, …, a is variable `depth`.
    // `let proof : x20 = rhs := rfl; 0`.
    let claim = |rhs: Term| let_("proof", eq(None, v(0), rhs), Term::Refl, p.num(0));
    let build = |innermost: Term| {
        let mut body = innermost;
        for _ in 0..depth {
            body = let_("x", p.nat_ty(), p.plus(v(0), v(0)), body);
        }
        ann(lam("a", body), arrow(p.nat_ty(), p.nat_ty()))
    };
    // `x20 = x20`, then the false `x20 = 0`.
    let same = build(claim(v(0)));
    let wrong = build(claim(p.num(0)));
    for (term, allowed) in [
        (same, ["ok", "E-RESOURCE"]),
        (wrong, ["E-REFL", "E-RESOURCE"]),
    ] {
        let _op = g.budget.operation(Limits::default());
        let started = Instant::now();
        let r = infer_closed(g, &term, span())
            .err()
            .map_or("ok", |d| d.code);
        let elapsed = started.elapsed();
        assert!(allowed.contains(&r), "unexpected result {r}");
        assert!(elapsed < Duration::from_secs(20), "took {elapsed:?}");
        eprintln!("nested lets: {r} in {elapsed:?}");
    }
}

// Cost at check time: a `let`'s value is computed only when checking needs it

/// `count n`, a definition that takes `n` steps to compute `n` (the
/// prelude's numbers are native, so `+` would be instant).
fn count(p: &mut Prelude) -> DefId {
    let nat = p.nat;
    let (nat_ty, zero) = (p.nat_ty(), p.num(0));
    let id = declare(&mut p.g, "count", arrow(nat_ty.clone(), nat_ty));
    let body = lam(
        "n",
        case(
            0,
            nat,
            vec![
                (vec![], zero),
                (
                    vec!["k"],
                    Term::ctor(nat, 1, vec![app(Term::Def(id), [v(0)])]),
                ),
            ],
        ),
    );
    check::define_def(&mut p.g, id, &body).expect("count");
    id
}

/// A number literal (`Prelude::num` builds unary terms, too deep for this).
fn lit(n: u32) -> Term {
    Term::Nat(Rc::new(n.into()))
}

/// The work checking `term` takes, and its result.
fn work(g: &Globals, term: &Term) -> (u64, &'static str) {
    let _op = g.budget.operation(Limits::default());
    let before = g.budget.total_work();
    let r = infer_code(g, term);
    (g.budget.total_work() - before, r)
}

#[test]
fn a_value_no_type_needs_is_not_computed_while_checking() {
    let mut p = Prelude::new();
    stitchwort_core::native::register_nat(&mut p.g, p.nat).expect("Nat");
    let count = count(&mut p);
    let big = |_: &Prelude| app(Term::Def(count), [lit(20_000)]);
    let nat = p.nat_ty();
    // Unused, and used only as an argument whose type doesn't depend on it.
    let unused = let_("x", nat.clone(), big(&p), p.num(0));
    let used = let_("x", nat.clone(), big(&p), p.plus(v(0), v(0)));
    // A type mentions it: now it's computed (once).
    let needed = let_(
        "x",
        nat.clone(),
        big(&p),
        ann(Term::Refl, eq(None, v(0), lit(20_000))),
    );
    let (unused_work, r1) = work(&p.g, &unused);
    let (used_work, r2) = work(&p.g, &used);
    let (needed_work, r3) = work(&p.g, &needed);
    assert_eq!((r1, r2, r3), ("ok", "ok", "ok"));
    assert!(unused_work < 1_000, "{unused_work}");
    assert!(used_work < 1_000, "{used_work}");
    assert!(needed_work > 20_000, "{needed_work}");
    // Used twice in types: still computed once.
    let twice = let_(
        "x",
        nat,
        big(&p),
        ann(
            Term::Refl,
            eq(None, p.plus(v(0), v(0)), p.plus(lit(20_000), lit(20_000))),
        ),
    );
    let (twice_work, r4) = work(&p.g, &twice);
    assert_eq!(r4, "ok");
    // The same with the value written out twice (no `let`) computes it
    // twice: the `let` saves one computation.
    let inline = ann(
        Term::Refl,
        eq(
            None,
            p.plus(big(&p), big(&p)),
            p.plus(lit(20_000), lit(20_000)),
        ),
    );
    let (inline_work, r5) = work(&p.g, &inline);
    assert_eq!(r5, "ok");
    assert!(
        twice_work + needed_work / 2 < inline_work,
        "{twice_work} with a `let`, {inline_work} without, {needed_work} for one"
    );
}

/// A `let` whose value mentions an earlier pending `let`: computing the
/// later one computes the earlier one first, in its own scope.
#[test]
fn a_pending_let_computes_the_ones_its_value_mentions() {
    let p = Prelude::new();
    let nat = p.nat_ty();
    // \z => let a := 2; let b := a + 1; let c := z + 7; (rfl : b = 3)
    let term = ann(
        lam(
            "z",
            let_(
                "a",
                nat.clone(),
                p.num(2),
                let_(
                    "b",
                    nat.clone(),
                    p.plus(v(0), p.num(1)),
                    let_(
                        "c",
                        nat.clone(),
                        p.plus(v(2), p.num(7)),
                        ann(Term::Refl, eq(None, v(1), p.num(3))),
                    ),
                ),
            ),
        ),
        pi("z", nat.clone(), eq(None, p.num(3), p.num(3))),
    );
    assert_eq!(infer_code(&p.g, &term), "ok");
    // \z => let a := 2; let c := z + 7; (rfl : c = z + 7): `c` is computed
    // from the binder `z`, in its own scope.
    let term = ann(
        lam(
            "z",
            let_(
                "a",
                nat.clone(),
                p.num(2),
                let_(
                    "c",
                    nat.clone(),
                    p.plus(v(1), p.num(7)),
                    ann(Term::Refl, eq(None, v(0), p.plus(v(2), p.num(7)))),
                ),
            ),
        ),
        pi(
            "z",
            nat,
            eq(None, p.plus(v(0), p.num(7)), p.plus(v(0), p.num(7))),
        ),
    );
    assert_eq!(infer_code(&p.g, &term), "ok");
}
