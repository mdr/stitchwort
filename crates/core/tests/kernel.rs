//! Kernel tests on hand-built core terms. The kernel's job is to catch a buggy
//! elaborator, so these include terms the elaborator would never produce. Every
//! rejection must be a diagnostic with the expected code, never a panic.

mod common;

use std::rc::Rc;

use common::*;
use stitchwort_core::check::infer_closed;
use stitchwort_core::value::{conv, eval, quote};
use stitchwort_core::{Globals, Icit, Sort, Term, Value};

fn nat_value(term: &Term) -> Option<usize> {
    match term.strip_loc() {
        Term::Ctor(_, 0, _) => Some(0),
        Term::Ctor(_, 1, args) => nat_value(&args[0]).map(|n| n + 1),
        _ => None,
    }
}

/// Checks a closed term with the kernel and normalises it.
fn normalise(g: &Globals, term: &Term) -> Term {
    let (term, _) = infer_closed(g, term, span()).expect("term checks");
    quote(g, 0, &eval(g, &[], &term))
}

fn infer_code(g: &Globals, term: &Term) -> &'static str {
    infer_closed(g, term, span()).err().map_or("ok", |d| d.code)
}

/// Structural equality, ignoring source locations and binder names.
fn same(a: &Term, b: &Term) -> bool {
    match (a.strip_loc(), b.strip_loc()) {
        (Term::Var(x), Term::Var(y)) => x == y,
        (Term::Def(x), Term::Def(y)) => x == y,
        (Term::Sort(x), Term::Sort(y)) => x == y,
        (Term::Refl, Term::Refl) => true,
        (Term::Data(d1, a1), Term::Data(d2, a2)) => d1 == d2 && all_same(a1, a2),
        (Term::Ctor(d1, c1, a1), Term::Ctor(d2, c2, a2)) => {
            d1 == d2 && c1 == c2 && all_same(a1, a2)
        }
        (Term::Pi(_, i1, a1, b1), Term::Pi(_, i2, a2, b2)) => {
            i1 == i2 && same(a1, a2) && same(b1, b2)
        }
        (Term::Lam(_, i1, b1), Term::Lam(_, i2, b2)) => i1 == i2 && same(b1, b2),
        (Term::App(f1, a1, i1), Term::App(f2, a2, i2)) => i1 == i2 && same(f1, f2) && same(a1, a2),
        (Term::Eq(t1, x1, y1), Term::Eq(t2, x2, y2)) => {
            t1.is_some() == t2.is_some()
                && t1.iter().zip(t2).all(|(a, b)| same(a, b))
                && same(x1, x2)
                && same(y1, y2)
        }
        (Term::J(m1, b1, p1), Term::J(m2, b2, p2)) => same(m1, m2) && same(b1, b2) && same(p1, p2),
        _ => false,
    }
}

fn all_same(xs: &[Term], ys: &[Term]) -> bool {
    xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| same(x, y))
}

// Computation and proofs by computation

#[test]
fn add_computes() {
    let p = Prelude::new();
    let result = normalise(&p.g, &p.plus(p.num(2), p.num(3)));
    assert_eq!(nat_value(&result), Some(5));
}

#[test]
fn refl_proves_an_equation_that_holds_by_computation() {
    let mut p = Prelude::new();
    let statement = eq(None, p.plus(p.num(2), p.num(2)), p.num(4));
    assert!(define(&mut p.g, "fourIsFour", statement, Term::Refl).is_ok());
}

#[test]
fn refl_rejects_a_false_equation() {
    let mut p = Prelude::new();
    let statement = eq(None, p.plus(p.num(2), p.num(2)), p.num(5));
    assert_eq!(
        define(&mut p.g, "wrong", statement, Term::Refl),
        Err("E-REFL")
    );
}

#[test]
fn refl_rejects_an_equation_that_needs_induction() {
    let mut p = Prelude::new();
    // (n : Nat) -> n + 0 = n is true, but `add` recurses on its first argument.
    let statement = pi("n", p.nat_ty(), eq(None, p.plus(v(0), p.num(0)), v(0)));
    assert_eq!(
        define(&mut p.g, "plusZero", statement, lam("n", Term::Refl)),
        Err("E-REFL")
    );
}

// Malformed terms are rejected, never a panic

#[test]
fn rejects_an_unsolved_metavariable() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    assert_eq!(
        define(&mut p.g, "x", nat, Term::Meta(0)),
        Err("E-MALFORMED")
    );
}

#[test]
fn rejects_an_out_of_scope_variable() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    assert_eq!(define(&mut p.g, "x", nat, v(3)), Err("E-MALFORMED"));
}

#[test]
fn rejects_a_constructor_with_the_wrong_number_of_fields() {
    let mut p = Prelude::new();
    let body = Term::Ctor(p.nat, 1, vec![]);
    let nat = p.nat_ty();
    assert_eq!(define(&mut p.g, "x", nat, body), Err("E-MALFORMED"));
}

#[test]
fn rejects_an_unknown_constructor() {
    let mut p = Prelude::new();
    let body = Term::Ctor(p.nat, 7, vec![]);
    let nat = p.nat_ty();
    assert_eq!(define(&mut p.g, "x", nat, body), Err("E-MALFORMED"));
}

#[test]
fn rejects_a_data_type_with_the_wrong_number_of_parameters() {
    let mut p = Prelude::new();
    let body = Term::Data(p.list, vec![]);
    assert_eq!(define(&mut p.g, "t", ty(), body), Err("E-MALFORMED"));
}

#[test]
fn rejects_a_branch_binding_the_wrong_number_of_fields() {
    let mut p = Prelude::new();
    let body = lam(
        "n",
        case(0, p.nat, vec![(vec![], p.num(0)), (vec![], p.num(0))]),
    );
    let ty = arrow(p.nat_ty(), p.nat_ty());
    assert_eq!(define(&mut p.g, "f", ty, body), Err("E-MALFORMED"));
}

#[test]
fn rejects_a_case_outside_a_case_tree() {
    let mut p = Prelude::new();
    let inner = lam(
        "m",
        case(0, p.nat, vec![(vec![], p.num(0)), (vec!["k"], p.num(1))]),
    );
    let body = lam("n", app(inner, [v(0)]));
    let ty = arrow(p.nat_ty(), p.nat_ty());
    assert_eq!(define(&mut p.g, "f", ty, body), Err("E-MALFORMED"));
}

#[test]
fn rejects_a_case_in_a_type() {
    let mut p = Prelude::new();
    let bad_ty = pi(
        "n",
        p.nat_ty(),
        case(0, p.nat, vec![(vec![], ty()), (vec!["k"], ty())]),
    );
    assert_eq!(
        define(&mut p.g, "f", bad_ty, Term::Refl),
        Err("E-MALFORMED")
    );
}

#[test]
fn rejects_a_case_on_a_variable_of_another_type() {
    let mut p = Prelude::new();
    let ty = arrow(Term::Data(p.list, vec![p.nat_ty()]), p.nat_ty());
    let body = lam(
        "xs",
        case(0, p.nat, vec![(vec![], p.num(0)), (vec!["k"], p.num(1))]),
    );
    assert_eq!(define(&mut p.g, "f", ty, body), Err("E-TYPE-MISMATCH"));
}

#[test]
fn rejects_a_case_with_a_missing_branch() {
    let mut p = Prelude::new();
    let ty = arrow(p.nat_ty(), p.nat_ty());
    let body = lam("n", case(0, p.nat, vec![(vec![], p.num(0))]));
    assert_eq!(define(&mut p.g, "f", ty, body), Err("E-NONEXHAUSTIVE"));
}

#[test]
fn rejects_a_reference_to_an_unknown_definition() {
    let p = Prelude::new();
    assert_eq!(
        infer_code(&p.g, &Term::Def(stitchwort_core::DefId(99))),
        "E-MALFORMED"
    );
}

// Implicitness must agree

#[test]
fn rejects_an_implicit_argument_to_an_explicit_parameter() {
    let p = Prelude::new();
    let term = Term::App(Rc::new(Term::Def(p.add)), Rc::new(p.num(1)), Icit::Implicit);
    assert_eq!(infer_code(&p.g, &term), "E-NOT-A-FUNCTION");
}

#[test]
fn rejects_a_lambda_of_the_wrong_implicitness() {
    let mut p = Prelude::new();
    let ty = ipi("n", p.nat_ty(), p.nat_ty());
    assert_eq!(
        define(&mut p.g, "f", ty, lam("n", v(0))),
        Err("E-TYPE-MISMATCH")
    );
}

#[test]
fn accepts_matching_implicitness() {
    let mut p = Prelude::new();
    let ty = ipi("n", p.nat_ty(), p.nat_ty());
    let f = define(&mut p.g, "f", ty, ilam("n", v(0))).expect("f checks");
    let call = Term::App(Rc::new(Term::Def(f)), Rc::new(p.num(3)), Icit::Implicit);
    assert_eq!(nat_value(&normalise(&p.g, &call)), Some(3));
}

// Termination

fn nat_to_nat(p: &Prelude) -> Term {
    arrow(p.nat_ty(), p.nat_ty())
}

/// Declares `name : Nat -> Nat` and defines it with a body that may refer to
/// itself.
fn recursive(
    p: &mut Prelude,
    name: &str,
    body: impl FnOnce(Term) -> Term,
) -> Result<(), &'static str> {
    let ty = nat_to_nat(p);
    let id = declare(&mut p.g, name, ty);
    stitchwort_core::check::define_def(&mut p.g, id, &body(Term::Def(id))).map_err(|d| d.code)
}

#[test]
fn rejects_recursion_on_a_larger_argument() {
    let mut p = Prelude::new();
    let nat = p.nat;
    let result = recursive(&mut p, "grow", |f| {
        lam("n", app(f, [Term::Ctor(nat, 1, vec![v(0)])]))
    });
    assert_eq!(result, Err("E-TERMINATION"));
}

#[test]
fn rejects_a_bare_self_reference() {
    let mut p = Prelude::new();
    assert_eq!(recursive(&mut p, "loop", |f| f), Err("E-TERMINATION"));
}

#[test]
fn rejects_a_self_reference_passed_as_an_argument() {
    let mut p = Prelude::new();
    // \n -> ((\g -> g n) : (Nat -> Nat) -> Nat) f
    let nat_to_nat = arrow(p.nat_ty(), p.nat_ty());
    let apply_to_n = Term::Ann(
        Rc::new(lam("g", app(v(0), [v(1)]))),
        Rc::new(arrow(nat_to_nat, p.nat_ty())),
    );
    let result = recursive(&mut p, "sneaky", |f| lam("n", app(apply_to_n, [f])));
    assert_eq!(result, Err("E-TERMINATION"));
}

#[test]
fn rejects_recursion_on_the_matched_variable_itself() {
    let mut p = Prelude::new();
    let (nat, zero) = (p.nat, p.num(0));
    // n matched as Succ m, but the call passes n again.
    let result = recursive(&mut p, "same", |f| {
        lam(
            "n",
            case(0, nat, vec![(vec![], zero), (vec!["m"], app(f, [v(1)]))]),
        )
    });
    assert_eq!(result, Err("E-TERMINATION"));
}

#[test]
fn accepts_recursion_on_a_field_of_a_field() {
    let mut p = Prelude::new();
    let nat = p.nat;
    let zero = || Term::Ctor(nat, 0, vec![]);
    // half n = case n of Zero -> 0; Succ m -> case m of Zero -> 0; Succ k -> Succ (half k)
    let result = recursive(&mut p, "half", |f| {
        lam(
            "n",
            case(
                0,
                nat,
                vec![
                    (vec![], zero()),
                    (
                        vec!["m"],
                        case(
                            0,
                            nat,
                            vec![
                                (vec![], zero()),
                                (vec!["k"], Term::Ctor(nat, 1, vec![app(f, [v(0)])])),
                            ],
                        ),
                    ),
                ],
            ),
        )
    });
    assert_eq!(result, Ok(()));
}

#[test]
fn accepts_recursion_on_the_second_parameter() {
    let mut p = Prelude::new();
    let (nat, nat_ty) = (p.nat, p.nat_ty());
    let ty = arrow(nat_ty.clone(), arrow(nat_ty.clone(), nat_ty));
    let id = declare(&mut p.g, "addRight", ty);
    // addRight m n = case n of Zero -> m; Succ k -> Succ (addRight m k)
    let body = lam(
        "m",
        lam(
            "n",
            case(
                0,
                nat,
                vec![
                    (vec![], v(1)),
                    (
                        vec!["k"],
                        Term::Ctor(nat, 1, vec![app(Term::Def(id), [v(2), v(0)])]),
                    ),
                ],
            ),
        ),
    );
    assert!(stitchwort_core::check::define_def(&mut p.g, id, &body).is_ok());
}

// Universes

#[test]
fn rejects_type_in_type() {
    let mut p = Prelude::new();
    assert_eq!(define(&mut p.g, "t", ty(), ty()), Err("E-UNIVERSE"));
}

#[test]
fn a_function_type_into_prop_is_a_prop_whatever_its_domain() {
    let p = Prelude::new();
    let statement = pi("a", ty_n(5), eq(None, v(0), v(0)));
    let (_, sort) = infer_closed(&p.g, &statement, span()).expect("checks");
    assert!(matches!(sort, Value::Sort(Sort::Prop)));
}

#[test]
fn a_function_type_lives_in_the_larger_universe() {
    let p = Prelude::new();
    let (_, sort) = infer_closed(&p.g, &pi("a", ty(), ty()), span()).expect("checks");
    assert!(matches!(sort, Value::Sort(Sort::Type(1))));
}

// Data declarations

fn data_code(
    g: &mut Globals,
    name: &str,
    params: Vec<(&str, Term)>,
    sort: Sort,
    fields: impl FnOnce(stitchwort_core::DataId) -> Vec<(&'static str, Term)>,
) -> &'static str {
    let d = data(g, name, params, sort);
    let fields = fields(d);
    stitchwort_core::check::define_ctors(g, d, vec![ctor("C", fields)])
        .err()
        .map_or("ok", |e| e.code)
}

#[test]
fn rejects_a_negative_occurrence() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let code = data_code(&mut p.g, "Bad", vec![], Sort::Type(0), |d| {
        vec![("f", arrow(Term::Data(d, vec![]), nat))]
    });
    assert_eq!(code, "E-POSITIVITY");
}

#[test]
fn rejects_a_recursive_occurrence_with_different_parameters() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let code = data_code(&mut p.g, "T", vec![("a", ty())], Sort::Type(0), |d| {
        vec![("f", Term::Data(d, vec![nat]))]
    });
    assert_eq!(code, "E-POSITIVITY");
}

#[test]
fn rejects_a_nested_occurrence_conservatively() {
    let mut p = Prelude::new();
    let list = p.list;
    let code = data_code(&mut p.g, "Rose", vec![], Sort::Type(0), |d| {
        vec![("children", Term::Data(list, vec![Term::Data(d, vec![])]))]
    });
    assert_eq!(code, "E-POSITIVITY");
}

#[test]
fn accepts_an_occurrence_as_a_function_result() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let code = data_code(&mut p.g, "Stream", vec![], Sort::Type(0), |d| {
        vec![("rest", arrow(nat, Term::Data(d, vec![])))]
    });
    assert_eq!(code, "ok");
}

#[test]
fn rejects_a_field_too_large_for_its_universe() {
    let mut p = Prelude::new();
    let code = data_code(&mut p.g, "Box", vec![], Sort::Type(0), |_| {
        vec![("t", ty())]
    });
    assert_eq!(code, "E-UNIVERSE");
}

// Prop elimination

/// `Or p q` and `And p q`, and `(p q : Prop) -> X p q -> result` where the
/// body matches on the proof.
struct Props {
    p: Prelude,
    or: stitchwort_core::DataId,
    and: stitchwort_core::DataId,
}

fn props() -> Props {
    let mut p = Prelude::new();
    let params = || vec![("p", prop()), ("q", prop())];
    let or = data(&mut p.g, "Or", params(), Sort::Prop);
    stitchwort_core::check::define_ctors(
        &mut p.g,
        or,
        vec![
            ctor("Inl", vec![("l", v(1))]),
            ctor("Inr", vec![("r", v(0))]),
        ],
    )
    .expect("Or");
    let and = data(&mut p.g, "And", params(), Sort::Prop);
    stitchwort_core::check::define_ctors(
        &mut p.g,
        and,
        vec![ctor("Both", vec![("l", v(1)), ("r", v(1))])],
    )
    .expect("And");
    Props { p, or, and }
}

/// `(p q : Prop) -> D p q -> result`, defined by matching on the proof.
/// `result` is written in the context `[p, q]`.
fn eliminate(
    props: &mut Props,
    d: stitchwort_core::DataId,
    result: Term,
    branches: Vec<(Vec<&str>, Term)>,
) -> Result<stitchwort_core::DefId, &'static str> {
    let ty = pi(
        "p",
        prop(),
        pi("q", prop(), arrow(Term::Data(d, vec![v(1), v(0)]), result)),
    );
    let body = lam("p", lam("q", lam("h", case(0, d, branches))));
    define(&mut props.p.g, "elim", ty, body)
}

#[test]
fn rejects_matching_on_or_to_produce_data() {
    let mut s = props();
    let (or, nat) = (s.or, s.p.nat_ty());
    let (zero, one) = (s.p.num(0), s.p.num(1));
    let result = eliminate(&mut s, or, nat, vec![(vec!["l"], zero), (vec!["r"], one)]);
    assert_eq!(result.err(), Some("E-PROP-ELIM"));
}

#[test]
fn accepts_matching_on_and_to_produce_data() {
    let mut s = props();
    let (and, nat, zero) = (s.and, s.p.nat_ty(), s.p.num(0));
    let result = eliminate(&mut s, and, nat, vec![(vec!["l", "r"], zero)]);
    assert!(result.is_ok());
}

#[test]
fn accepts_matching_on_or_to_produce_a_proof() {
    let mut s = props();
    let or = s.or;
    // (p q : Prop) -> Or p q -> Or q p. In the branches: [p, q, h, field].
    let swapped = Term::Data(or, vec![v(0), v(1)]);
    let result = eliminate(
        &mut s,
        or,
        swapped,
        vec![
            (vec!["l"], Term::Ctor(or, 1, vec![v(0)])),
            (vec!["r"], Term::Ctor(or, 0, vec![v(0)])),
        ],
    );
    assert_eq!(result.err(), None);
}

#[test]
fn rejects_extracting_a_type_hidden_in_a_proof() {
    let mut p = Prelude::new();
    let hidden = data(&mut p.g, "HiddenType", vec![], Sort::Prop);
    stitchwort_core::check::define_ctors(&mut p.g, hidden, vec![ctor("Hide", vec![("a", ty())])])
        .expect("HiddenType: Prop data may have large fields");
    let ty = arrow(Term::Data(hidden, vec![]), ty());
    let body = lam("h", case(0, hidden, vec![(vec!["a"], v(0))]));
    assert_eq!(define(&mut p.g, "reveal", ty, body), Err("E-PROP-ELIM"));
}

// Equality

#[test]
fn j_transports_along_an_equation() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    // sym : (x y : Nat) -> x = y -> y = x
    let ty = pi(
        "x",
        nat.clone(),
        pi("y", nat, arrow(eq(None, v(1), v(0)), eq(None, v(0), v(1)))),
    );
    // In the motive's body the context is [x, y, p, y', p'].
    let motive = lam("y'", lam("p'", eq(None, v(1), v(4))));
    let body = lam(
        "x",
        lam(
            "y",
            lam(
                "p",
                Term::J(Rc::new(motive), Rc::new(Term::Refl), Rc::new(v(0))),
            ),
        ),
    );
    assert!(define(&mut p.g, "sym", ty, body).is_ok());
}

#[test]
fn rejects_j_on_something_that_is_not_an_equation() {
    let p = Prelude::new();
    let motive = lam("y", lam("p", p.nat_ty()));
    let term = Term::J(Rc::new(motive), Rc::new(p.num(0)), Rc::new(p.num(1)));
    assert_eq!(infer_code(&p.g, &term), "E-TYPE-MISMATCH");
}

// Evaluation

#[test]
fn recursive_definitions_stay_folded_on_unknown_arguments() {
    let p = Prelude::new();
    // \n -> add n 0 normalises to itself: `add` can't unfold on a variable.
    let term = Term::Ann(
        Rc::new(lam("n", p.plus(v(0), p.num(0)))),
        Rc::new(arrow(p.nat_ty(), p.nat_ty())),
    );
    let normal = normalise(&p.g, &term);
    assert!(
        same(&normal, &lam("n", p.plus(v(0), p.num(0)))),
        "{normal:?}"
    );
}

#[test]
fn conversion_includes_eta() {
    let p = Prelude::new();
    let add = eval(&p.g, &[], &Term::Def(p.add));
    let eta = eval(&p.g, &[], &lam("x", app(Term::Def(p.add), [v(0)])));
    assert!(conv(&p.g, 0, &add, &eta));
    assert!(conv(&p.g, 0, &eta, &add));
}

#[test]
fn normalising_twice_changes_nothing() {
    let p = Prelude::new();
    let terms = [
        p.plus(p.num(3), p.num(4)),
        Term::Ann(
            Rc::new(lam("n", p.plus(p.num(2), v(0)))),
            Rc::new(arrow(p.nat_ty(), p.nat_ty())),
        ),
        pi("a", ty(), arrow(v(0), v(0))),
    ];
    for term in terms {
        let once = normalise(&p.g, &term);
        let twice = normalise(
            &p.g,
            &Term::Ann(
                Rc::new(once.clone()),
                Rc::new(quote(
                    &p.g,
                    0,
                    &infer_closed(&p.g, &term, span()).expect("checks").1,
                )),
            ),
        );
        assert!(same(&once, &twice), "{once:?} vs {twice:?}");
    }
}

// Definitional equality must say *no* to things that differ. (The examples
// can't test this: the elaborator rejects such proofs before the kernel runs.)

#[test]
fn conversion_distinguishes_values_that_differ_anywhere() {
    let p = Prelude::new();
    let g = &p.g;
    let nat = p.nat_ty();
    let list = |t: Term| Term::Data(p.list, vec![t]);
    let cons = |h: Term, t: Term| Term::Ctor(p.list, 1, vec![h, t]);
    let nil = || Term::Ctor(p.list, 0, vec![]);
    // Closed values, built without type checking.
    let value = |t: &Term| eval(g, &[], t);
    let differ = [
        // Function types: domain, codomain, implicitness.
        (
            arrow(nat.clone(), nat.clone()),
            arrow(list(nat.clone()), nat.clone()),
        ),
        (
            arrow(nat.clone(), nat.clone()),
            arrow(nat.clone(), list(nat.clone())),
        ),
        (
            pi("x", nat.clone(), nat.clone()),
            ipi("x", nat.clone(), nat.clone()),
        ),
        // Data type parameters.
        (list(nat.clone()), list(list(nat.clone()))),
        // Constructor fields, first and second.
        (cons(p.num(1), nil()), cons(p.num(2), nil())),
        (cons(p.num(1), nil()), cons(p.num(1), cons(p.num(1), nil()))),
        // Equations: each side, and the type.
        (
            eq(Some(nat.clone()), p.num(1), p.num(1)),
            eq(Some(nat.clone()), p.num(2), p.num(1)),
        ),
        (
            eq(Some(nat.clone()), p.num(1), p.num(1)),
            eq(Some(nat.clone()), p.num(1), p.num(2)),
        ),
        (
            eq(Some(list(nat.clone())), nil(), nil()),
            eq(Some(list(list(nat.clone()))), nil(), nil()),
        ),
        // Function bodies.
        (
            lam("x", p.plus(v(0), p.num(1))),
            lam("x", p.plus(v(0), p.num(2))),
        ),
        (Term::Refl, p.num(0)),
    ];
    for (a, b) in &differ {
        assert!(
            !conv(g, 0, &value(a), &value(b)),
            "{a:?} should differ from {b:?}"
        );
        assert!(
            !conv(g, 0, &value(b), &value(a)),
            "{b:?} should differ from {a:?}"
        );
    }
    for (a, _) in &differ {
        assert!(
            conv(g, 0, &value(a), &value(a)),
            "{a:?} should equal itself"
        );
    }
}

#[test]
fn conversion_distinguishes_stuck_computations() {
    let p = Prelude::new();
    let g = &p.g;
    // With two variables x (level 0) and y (level 1) in scope.
    let env = [Value::var(0), Value::var(1)];
    let value = |t: &Term| eval(g, &env, t);
    let x = v(1);
    let y = v(0);
    let differ = [
        (x.clone(), y.clone()),
        (p.plus(x.clone(), p.num(1)), p.plus(x.clone(), p.num(2))),
        (p.plus(x.clone(), p.num(1)), p.plus(y.clone(), p.num(1))),
        (
            p.plus(x.clone(), p.num(1)),
            app(Term::Def(p.add), [x.clone()]),
        ),
    ];
    for (a, b) in &differ {
        assert!(
            !conv(g, 2, &value(a), &value(b)),
            "{a:?} should differ from {b:?}"
        );
    }
    assert!(conv(
        g,
        2,
        &value(&p.plus(x.clone(), y.clone())),
        &value(&p.plus(x, y))
    ));
}

#[test]
fn conversion_compares_stuck_transports() {
    let p = Prelude::new();
    let g = &p.g;
    let nat = p.nat_ty();
    // J m b h, stuck on a proof variable h (level 0).
    let stuck = |motive: Term, base: Term| {
        eval(
            g,
            &[Value::var(0)],
            &Term::J(Rc::new(motive), Rc::new(base), Rc::new(v(0))),
        )
    };
    let motive = |t: Term| lam("y", lam("q", t));
    let a = stuck(motive(nat.clone()), p.num(1));
    assert!(conv(g, 1, &a, &stuck(motive(nat.clone()), p.num(1))));
    assert!(
        !conv(g, 1, &a, &stuck(motive(nat.clone()), p.num(2))),
        "different base"
    );
    assert!(
        !conv(g, 1, &a, &stuck(motive(ty()), p.num(1))),
        "different motive"
    );
}

// More checking rules

#[test]
fn constants_unfold() {
    let mut p = Prelude::new();
    let (nat, num_two) = (p.nat_ty(), p.num(2));
    let two = define(&mut p.g, "two", nat, num_two).expect("two checks");
    let statement = eq(None, Term::Def(two), p.num(2));
    assert!(define(&mut p.g, "twoIsTwo", statement, Term::Refl).is_ok());
}

#[test]
fn rejects_a_constructor_of_another_type() {
    let mut p = Prelude::new();
    let list_of_nat = Term::Data(p.list, vec![p.nat_ty()]);
    let zero = Term::Ctor(p.nat, 0, vec![]);
    assert_eq!(
        define(&mut p.g, "x", list_of_nat, zero),
        Err("E-TYPE-MISMATCH")
    );
    let nat_to_nat = arrow(p.nat_ty(), p.nat_ty());
    assert_eq!(
        define(&mut p.g, "f", nat_to_nat, Term::Ctor(p.nat, 0, vec![])),
        Err("E-TYPE-MISMATCH")
    );
}

#[test]
fn rejects_refl_where_an_equation_is_not_expected() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    assert_eq!(
        define(&mut p.g, "x", nat, Term::Refl),
        Err("E-TYPE-MISMATCH")
    );
}

#[test]
fn infers_an_equation_from_its_right_side_when_the_left_is_ambiguous() {
    let p = Prelude::new();
    // (xs : List Nat) -> Nil = xs: `Nil` alone could be any list.
    let statement = pi(
        "xs",
        Term::Data(p.list, vec![p.nat_ty()]),
        eq(None, Term::Ctor(p.list, 0, vec![]), v(0)),
    );
    assert_eq!(infer_code(&p.g, &statement), "ok");
    let both_ambiguous = eq(
        None,
        Term::Ctor(p.list, 0, vec![]),
        Term::Ctor(p.list, 0, vec![]),
    );
    assert_eq!(infer_code(&p.g, &both_ambiguous), "E-CANNOT-INFER");
}

#[test]
fn positivity_looks_inside_every_part_of_a_negative_position() {
    let p = Prelude::new();
    let nat = p.nat_ty();
    let identity = || Term::Ann(Rc::new(lam("t", v(0))), Rc::new(arrow(ty(), ty())));
    // Each field takes a `D` as input, hidden somewhere in the domain. (`DataId(0)`
    // is `Nat`.)
    let hidden: Vec<Box<dyn Fn(Term) -> Term>> = vec![
        Box::new(|d| d),
        Box::new(move |d| app(identity(), [d])),
        Box::new(|d| Term::Ann(Rc::new(d), Rc::new(ty()))),
        Box::new(|d| {
            eq(
                Some(ty()),
                d,
                Term::Data(stitchwort_core::DataId(0), vec![]),
            )
        }),
        Box::new(|d| arrow(d, Term::Data(stitchwort_core::DataId(0), vec![]))),
    ];
    for (i, hide) in hidden.iter().enumerate() {
        let mut g = Prelude::new().g;
        let d = data(&mut g, "Bad", vec![], Sort::Type(0));
        let field = arrow(hide(Term::Data(d, vec![])), nat.clone());
        let result =
            stitchwort_core::check::define_ctors(&mut g, d, vec![ctor("C", vec![("f", field)])]);
        assert_eq!(
            result.err().map(|e| e.code),
            Some("E-POSITIVITY"),
            "case {i}"
        );
    }
}

#[test]
fn accepts_a_parameterised_type_as_a_function_result() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    // type T (a : Type) = C (f : Nat -> T a). Under the arrow, `a` is v(1).
    let code = data_code(&mut p.g, "T", vec![("a", ty())], Sort::Type(0), |d| {
        vec![("f", pi("_", nat, Term::Data(d, vec![v(1)])))]
    });
    assert_eq!(code, "ok");
}

#[test]
fn rejects_a_case_anywhere_outside_a_case_tree() {
    let p = Prelude::new();
    let nat = p.nat_ty();
    let a_case = || {
        case(
            0,
            p.nat,
            vec![(vec![], nat.clone()), (vec!["k"], nat.clone())],
        )
    };
    // Each is the type of `f : Nat -> …`, with a case in a different place.
    let places = [
        pi("n", nat.clone(), a_case()),
        pi("n", a_case(), nat.clone()),
        pi("n", nat.clone(), arrow(nat.clone(), a_case())),
        pi("n", nat.clone(), app(lam("x", v(0)), [a_case()])),
        pi("n", nat.clone(), app(a_case(), [nat.clone()])),
        pi("n", nat.clone(), Term::Data(p.list, vec![a_case()])),
        pi(
            "n",
            nat.clone(),
            Term::Ann(Rc::new(nat.clone()), Rc::new(a_case())),
        ),
        pi(
            "n",
            nat.clone(),
            Term::Ann(Rc::new(a_case()), Rc::new(nat.clone())),
        ),
        pi("n", nat.clone(), eq(None, nat.clone(), a_case())),
        pi(
            "n",
            nat.clone(),
            eq(Some(a_case()), nat.clone(), nat.clone()),
        ),
        pi(
            "n",
            nat.clone(),
            Term::J(
                Rc::new(nat.clone()),
                Rc::new(nat.clone()),
                Rc::new(a_case()),
            ),
        ),
        pi(
            "n",
            nat.clone(),
            Term::J(
                Rc::new(nat.clone()),
                Rc::new(a_case()),
                Rc::new(nat.clone()),
            ),
        ),
        pi(
            "n",
            nat.clone(),
            Term::Ctor(p.list, 1, vec![nat.clone(), a_case()]),
        ),
    ];
    for (i, ty) in places.into_iter().enumerate() {
        let mut g = Prelude::new().g;
        assert_eq!(
            define(&mut g, "f", ty, Term::Refl),
            Err("E-MALFORMED"),
            "place {i}"
        );
    }
}

#[test]
fn records_which_fields_are_erased() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let d = data(&mut p.g, "Mixed", vec![], Sort::Type(1));
    let fields = vec![
        ("n", nat.clone()),
        ("t", ty()),
        ("family", arrow(nat.clone(), ty())),
        ("proof", eq(None, p.num(0), p.num(0))),
        ("f", arrow(nat.clone(), nat)),
    ];
    stitchwort_core::check::define_ctors(&mut p.g, d, vec![ctor("C", fields)]).expect("checks");
    assert_eq!(
        p.g.data(d).ctors[0].field_erased,
        vec![false, true, true, true, false]
    );
}

#[test]
fn conversion_keeps_nested_binders_apart() {
    let p = Prelude::new();
    let g = &p.g;
    let closed = |t: &Term| eval(g, &[], t);
    // \x y -> x  vs  \x y -> y
    let first = lam("x", lam("y", v(1)));
    let second = lam("x", lam("y", v(0)));
    assert!(!conv(g, 0, &closed(&first), &closed(&second)));
    // (x : Type) -> (y : Type) -> x  vs  … -> y
    let first = pi("x", ty(), pi("y", ty(), v(1)));
    let second = pi("x", ty(), pi("y", ty(), v(0)));
    assert!(!conv(g, 0, &closed(&first), &closed(&second)));
    // Eta, twice: with f a variable, \x y -> f y x is not f.
    let f = Value::var(0);
    let flipped = eval(
        g,
        std::slice::from_ref(&f),
        &lam("x", lam("y", app(v(2), [v(0), v(1)]))),
    );
    let unflipped = eval(
        g,
        std::slice::from_ref(&f),
        &lam("x", lam("y", app(v(2), [v(1), v(0)]))),
    );
    assert!(!conv(g, 1, &flipped, &f));
    assert!(conv(g, 1, &unflipped, &f));
}

#[test]
fn rejects_a_constructor_of_a_parameterised_type_where_another_type_is_expected() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let nil = Term::Ctor(p.list, 0, vec![]);
    assert_eq!(define(&mut p.g, "x", nat, nil), Err("E-TYPE-MISMATCH"));
}

#[test]
fn auto_parameters_must_agree_like_other_implicitness() {
    let mut p = Prelude::new();
    let ty = Term::Pi(
        "n".into(),
        Icit::Auto,
        Rc::new(p.nat_ty()),
        Rc::new(p.nat_ty()),
    );
    let f = define(
        &mut p.g,
        "f",
        ty.clone(),
        Term::Lam("n".into(), Icit::Auto, Rc::new(v(0))),
    )
    .expect("matching auto lambda checks");
    assert_eq!(
        define(&mut p.g, "g", ty, ilam("n", v(0))),
        Err("E-TYPE-MISMATCH"),
        "an implicit lambda isn't an auto one"
    );
    let implicit_call = Term::App(Rc::new(Term::Def(f)), Rc::new(p.num(1)), Icit::Implicit);
    assert_eq!(infer_code(&p.g, &implicit_call), "E-NOT-A-FUNCTION");
    let auto_call = Term::App(Rc::new(Term::Def(f)), Rc::new(p.num(1)), Icit::Auto);
    assert_eq!(infer_code(&p.g, &auto_call), "ok");
}

#[test]
fn matching_refines_the_types_of_later_variables() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    // (n : Nat) -> n = 0 -> Nat, matching on n: in the `Zero` branch the proof
    // has type `0 = 0`, so it can be returned where that's expected.
    let ty = pi(
        "n",
        nat.clone(),
        arrow(eq(None, v(0), p.num(0)), eq(None, p.num(0), p.num(0))),
    );
    let body = lam(
        "n",
        lam(
            "h",
            case(1, p.nat, vec![(vec![], v(0)), (vec!["k"], Term::Refl)]),
        ),
    );
    assert_eq!(define(&mut p.g, "refined", ty, body).err(), None);
}

// Validators: what extracted JS runs to check an export's preconditions.

/// A prelude with `Decidable`, and a definition `f : (n : Nat) -> [auto ok : n = n] -> Nat`.
fn with_decidable() -> (Prelude, stitchwort_core::DataId, stitchwort_core::DefId) {
    let mut p = Prelude::new();
    let void = data(&mut p.g, "Void", vec![], Sort::Prop);
    stitchwort_core::check::define_ctors(&mut p.g, void, vec![]).unwrap();
    let decidable = data(&mut p.g, "Decidable", vec![("p", prop())], Sort::Type(0));
    stitchwort_core::check::define_ctors(
        &mut p.g,
        decidable,
        vec![
            ctor("Yes", vec![("proof", v(0))]),
            ctor(
                "No",
                vec![("refutation", arrow(v(0), Term::Data(void, vec![])))],
            ),
        ],
    )
    .unwrap();
    let ty = pi(
        "n",
        p.nat_ty(),
        Term::Pi(
            "ok".into(),
            Icit::Auto,
            Rc::new(eq(None, v(0), v(0))),
            Rc::new(p.nat_ty()),
        ),
    );
    let body = lam("n", Term::Lam("ok".into(), Icit::Auto, Rc::new(v(1))));
    let f = define(&mut p.g, "f", ty, body).unwrap();
    (p, decidable, f)
}

fn validate(
    p: &mut Prelude,
    f: stitchwort_core::DefId,
    param: usize,
    d: stitchwort_core::DataId,
    decision: Term,
) -> &'static str {
    stitchwort_core::check::add_validator(&mut p.g, f, param, d, &decision)
        .err()
        .map_or("ok", |e| e.code)
}

#[test]
fn accepts_a_validator_that_decides_the_precondition() {
    let (mut p, decidable, f) = with_decidable();
    // `Yes rfl`, in the context [n].
    let yes = Term::Ctor(decidable, 0, vec![Term::Refl]);
    assert_eq!(validate(&mut p, f, 1, decidable, yes), "ok");
    assert_eq!(p.g.def(f).validators.len(), 1);
}

#[test]
fn rejects_validators_that_do_not_decide_the_precondition() {
    let (mut p, decidable, f) = with_decidable();
    let yes = || Term::Ctor(decidable, 0, vec![Term::Refl]);
    // Not for a proof parameter: `n` is data.
    assert_eq!(validate(&mut p, f, 0, decidable, yes()), "E-MALFORMED");
    // No such parameter.
    assert_eq!(validate(&mut p, f, 5, decidable, yes()), "E-MALFORMED");
    // A decision of something else: `Yes` of a proof of `0 = 0` has type
    // `Decidable (0 = 0)`, not `Decidable (n = n)`.
    let other = Term::Ann(
        Rc::new(Term::Ctor(decidable, 0, vec![Term::Refl])),
        Rc::new(Term::Data(decidable, vec![eq(None, p.num(0), p.num(0))])),
    );
    assert_eq!(validate(&mut p, f, 1, decidable, other), "E-TYPE-MISMATCH");
    // A `case` isn't allowed in a validator.
    let with_case = case(0, p.nat, vec![(vec![], yes()), (vec!["k"], yes())]);
    assert_eq!(validate(&mut p, f, 1, decidable, with_case), "E-MALFORMED");
}

#[test]
fn rejects_validators_whose_data_type_is_not_shaped_like_decidable() {
    let (mut p, _, f) = with_decidable();
    // Each of these differs from `Decidable` in one way that matters: extracted
    // JS reads the first constructor as "the precondition holds".
    type Shape<'a> = (Vec<(&'a str, Term)>, Vec<stitchwort_core::check::CtorDecl>);
    let shapes: Vec<Shape> = vec![
        // A `Type` parameter instead of a `Prop`.
        (
            vec![("p", ty())],
            vec![ctor("Yes", vec![("proof", v(0))]), ctor("No", vec![])],
        ),
        // Two parameters.
        (
            vec![("p", prop()), ("q", prop())],
            vec![ctor("Yes", vec![("proof", v(1))]), ctor("No", vec![])],
        ),
        // Only one constructor.
        (
            vec![("p", prop())],
            vec![ctor("Yes", vec![("proof", v(0))])],
        ),
        // The first constructor carries no proof.
        (
            vec![("p", prop())],
            vec![ctor("Yes", vec![]), ctor("No", vec![("proof", v(0))])],
        ),
        // The first constructor carries something other than a proof of `p`.
        (
            vec![("p", prop())],
            vec![ctor("Yes", vec![("proof", prop())]), ctor("No", vec![])],
        ),
    ];
    for (i, (params, ctors)) in shapes.into_iter().enumerate() {
        let d = data(&mut p.g, &format!("Fake{i}"), params, Sort::Type(1));
        stitchwort_core::check::define_ctors(&mut p.g, d, ctors).expect("data checks");
        // Whatever the decision term, the shape is refused first.
        assert_eq!(
            validate(&mut p, f, 1, d, Term::Refl),
            "E-MALFORMED",
            "shape {i}"
        );
    }
}

// Refinement with dependent fields (from the second review of the abilities
// design): matching a field after later fields are bound must refine their
// types, in the kernel itself.

/// `B = F | T`, `PT : B -> Type` with `PT F = B` and `PT T = Nat`, and
/// `Tree = Leaf | Node (tag : B) (payload : PT tag) (rest : PT tag -> Tree)`.
struct DepTree {
    b: stitchwort_core::DataId,
    tree: stitchwort_core::DataId,
}

fn dep_tree(p: &mut Prelude) -> DepTree {
    use stitchwort_core::check::define_ctors;
    let b = data(&mut p.g, "B", vec![], Sort::Type(0));
    define_ctors(&mut p.g, b, vec![ctor("F", vec![]), ctor("T", vec![])]).unwrap();
    let b_ty = Term::Data(b, vec![]);
    let pt_body = lam(
        "x",
        case(0, b, vec![(vec![], b_ty.clone()), (vec![], p.nat_ty())]),
    );
    let pt = define(&mut p.g, "PT", arrow(b_ty.clone(), ty()), pt_body).unwrap();
    let tree = data(&mut p.g, "Tree", vec![], Sort::Type(0));
    let pt_of = |ix| app(Term::Def(pt), [v(ix)]);
    define_ctors(
        &mut p.g,
        tree,
        vec![
            ctor("Leaf", vec![]),
            ctor(
                "Node",
                vec![
                    ("tag", b_ty),
                    ("payload", pt_of(0)),
                    ("rest", arrow(pt_of(1), Term::Data(tree, vec![]))),
                ],
            ),
        ],
    )
    .unwrap();
    DepTree { b, tree }
}

/// `walk : Tree -> Nat`, matching `Node tag payload rest` and then `tag`,
/// with the given bodies for the `F` and `T` branches. In them, `rest` is
/// `v(0)`, `payload` is `v(1)` and `tag` is `v(2)`.
fn walk_tree(
    p: &mut Prelude,
    f_body: impl Fn(&Prelude, Term) -> Term,
    t_body: impl Fn(&Prelude, Term) -> Term,
) -> Result<(), &'static str> {
    let d = dep_tree(p);
    let ty = arrow(Term::Data(d.tree, vec![]), p.nat_ty());
    let id = declare(&mut p.g, "walk", ty);
    let walk = Term::Def(id);
    let body = lam(
        "t",
        case(
            0,
            d.tree,
            vec![
                (vec![], p.num(0)),
                (
                    vec!["tag", "payload", "rest"],
                    case(
                        2,
                        d.b,
                        vec![(vec![], f_body(p, walk.clone())), (vec![], t_body(p, walk))],
                    ),
                ),
            ],
        ),
    );
    stitchwort_core::check::define_def(&mut p.g, id, &body).map_err(|e| e.code)
}

#[test]
fn matching_an_earlier_field_refines_later_ones() {
    let mut p = Prelude::new();
    // F: walk (rest payload), with payload : B. T: walk (rest (payload + 1)).
    let result = walk_tree(
        &mut p,
        |_, walk| app(walk, [app(v(0), [v(1)])]),
        |p, walk| app(walk, [app(v(0), [p.plus(v(1), p.num(1))])]),
    );
    assert_eq!(result, Ok(()));
}

#[test]
fn refinement_keeps_branches_apart() {
    // Treating the `F` branch's payload (a `B`) as a number.
    let mut p = Prelude::new();
    let result = walk_tree(
        &mut p,
        |p, walk| app(walk, [app(v(0), [p.plus(v(1), p.num(1))])]),
        |p, walk| app(walk, [app(v(0), [p.plus(v(1), p.num(1))])]),
    );
    assert_eq!(result, Err("E-TYPE-MISMATCH"));
    // Passing a `B` to the `T` branch's `rest`, which wants a number.
    let mut p = Prelude::new();
    let result = walk_tree(
        &mut p,
        |_, walk| app(walk, [app(v(0), [v(1)])]),
        |p, walk| {
            let f = Term::Ctor(p.g.find_data("B").unwrap(), 0, vec![]);
            app(walk, [app(v(0), [f])])
        },
    );
    assert_eq!(result, Err("E-TYPE-MISMATCH"));
}

#[test]
fn a_hidden_negative_occurrence_is_refused() {
    use stitchwort_core::check::define_ctors;
    // `Bad` is declared, then `Neg n = Bad -> Nat` is defined, then `Bad`'s
    // constructor takes a `Neg 0`, which is `Bad -> Nat` in disguise.
    let mut p = Prelude::new();
    let bad = data(&mut p.g, "Bad", vec![], Sort::Type(0));
    let neg_ty = arrow(p.nat_ty(), ty());
    let neg_body = lam("n", arrow(Term::Data(bad, vec![]), p.nat_ty()));
    let neg = define(&mut p.g, "Neg", neg_ty, neg_body).unwrap();
    let field = app(Term::Def(neg), [p.num(0)]);
    let result = define_ctors(&mut p.g, bad, vec![ctor("MkBad", vec![("f", field)])]);
    assert_eq!(result.err().map(|e| e.code), Some("E-POSITIVITY"));
}

#[test]
fn a_negative_occurrence_hidden_in_a_later_data_type_is_refused() {
    use stitchwort_core::check::define_ctors;
    // `Wrap = MkWrap (Bad -> Nat)`, declared after `Bad`, then used in `Bad`.
    let mut p = Prelude::new();
    let bad = data(&mut p.g, "Bad", vec![], Sort::Type(0));
    let wrap = data(&mut p.g, "Wrap", vec![], Sort::Type(0));
    let neg = arrow(Term::Data(bad, vec![]), p.nat_ty());
    define_ctors(&mut p.g, wrap, vec![ctor("MkWrap", vec![("f", neg)])]).unwrap();
    let field = Term::Data(wrap, vec![]);
    let result = define_ctors(&mut p.g, bad, vec![ctor("MkBad", vec![("w", field)])]);
    assert_eq!(result.err().map(|e| e.code), Some("E-POSITIVITY"));
}

#[test]
fn constructors_are_defined_only_once() {
    use stitchwort_core::check::define_ctors;
    let mut p = Prelude::new();
    let d = data(&mut p.g, "D", vec![], Sort::Type(0));
    define_ctors(&mut p.g, d, vec![]).unwrap();
    let again = define_ctors(&mut p.g, d, vec![ctor("C", vec![])]);
    assert_eq!(again.err().map(|e| e.code), Some("E-MALFORMED"));
}

#[test]
fn an_under_applied_definition_is_a_function_for_conversion() {
    // `succ n = Succ n`, unapplied, equals `\n -> Succ n`.
    let mut p = Prelude::new();
    let nat = p.nat;
    let ty = arrow(p.nat_ty(), p.nat_ty());
    let succ = define(
        &mut p.g,
        "succ",
        ty,
        lam("n", Term::Ctor(nat, 1, vec![v(0)])),
    )
    .unwrap();
    let f = eval(&p.g, &[], &Term::Def(succ));
    let g = eval(&p.g, &[], &lam("n", Term::Ctor(nat, 1, vec![v(0)])));
    assert!(conv(&p.g, 0, &f, &g));
    assert!(conv(&p.g, 0, &g, &f));
    let other = eval(&p.g, &[], &lam("n", v(0)));
    assert!(!conv(&p.g, 0, &f, &other));
}
