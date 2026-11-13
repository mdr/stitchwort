//! Kernel tests on hand-built core terms. The kernel's job is to catch a buggy
//! elaborator, so these include terms the elaborator would never produce. Every
//! rejection must be a diagnostic with the expected code, never a panic.

use std::rc::Rc;

use crate::common::*;
use stitchwort_core::check::infer_closed;
use stitchwort_core::value::{conv, eval, quote};
use stitchwort_core::{Icit, Kernel, Sort, Term, Value};

fn nat_value(term: &Term) -> Option<usize> {
    match term.strip_loc() {
        Term::Ctor(_, 0, _) => Some(0),
        Term::Ctor(_, 1, args) => nat_value(&args[0]).map(|n| n + 1),
        _ => None,
    }
}

/// Checks a closed term with the kernel and normalises it.
fn normalise(g: &Kernel, term: &Term) -> Term {
    let (term, _) = infer_closed(&g.ev(), term, span()).expect("term checks");
    quote(&g.ev(), 0, &eval(&g.ev(), &[], &term).unwrap()).unwrap()
}

fn infer_code(g: &Kernel, term: &Term) -> &'static str {
    infer_closed(&g.ev(), term, span())
        .err()
        .map_or("ok", |d| d.code)
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

fn all_same(xs: &[Rc<Term>], ys: &[Rc<Term>]) -> bool {
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
    let ty = arrow(Term::data(p.list, vec![p.nat_ty()]), p.nat_ty());
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
        lam("n", app(f, [Term::ctor(nat, 1, vec![v(0)])]))
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
    // n => ((g => g n) : (Nat -> Nat) -> Nat) f
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
                                (vec!["k"], Term::ctor(nat, 1, vec![app(f, [v(0)])])),
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
                        Term::ctor(nat, 1, vec![app(Term::Def(id), [v(2), v(0)])]),
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
    let (_, sort) = infer_closed(&p.g.ev(), &statement, span()).expect("checks");
    assert!(matches!(sort, Value::Sort(Sort::Prop)));
}

#[test]
fn a_function_type_lives_in_the_larger_universe() {
    let p = Prelude::new();
    let (_, sort) = infer_closed(&p.g.ev(), &pi("a", ty(), ty()), span()).expect("checks");
    assert!(matches!(sort, Value::Sort(Sort::Type(1))));
}

// Data declarations

fn data_code(
    g: &mut Kernel,
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
        vec![("f", Term::data(d, vec![nat]))]
    });
    assert_eq!(code, "E-POSITIVITY");
}

// Nested occurrences (docs/proposals/nested-data-types.md §5).

#[test]
fn accepts_a_nested_occurrence_at_a_nestable_parameter() {
    let mut p = Prelude::new();
    let list = p.list;
    assert_eq!(p.g.data(list).nestable(), &[Ok(())]);
    let code = data_code(&mut p.g, "Rose", vec![], Sort::Type(0), |d| {
        vec![("children", Term::data(list, vec![Term::Data(d, vec![])]))]
    });
    assert_eq!(code, "ok");
}

/// `Neg (a) = MkNeg (consume: a → Nat)`: `a` isn't nestable.
fn neg(p: &mut Prelude) -> stitchwort_core::DataId {
    let nat = p.nat_ty();
    let neg = data(&mut p.g, "Neg", vec![("a", ty())], Sort::Type(0));
    let consume = ctor("MkNeg", vec![("consume", arrow(v(0), nat))]);
    stitchwort_core::check::define_ctors(&mut p.g, neg, vec![consume]).expect("Neg");
    neg
}

#[test]
fn a_parameter_taken_as_input_isnt_nestable() {
    use stitchwort_core::globals::{NotNestable, ParamUse};
    let mut p = Prelude::new();
    let neg = neg(&mut p);
    assert_eq!(
        p.g.data(neg).nestable(),
        &[Err(NotNestable::Field {
            data: neg,
            ctor: 0,
            field: 0,
            how: ParamUse::Input
        })]
    );
    let list = p.list;
    // Refused through `List` too: `List (Neg Bad)`.
    let bad = data(&mut p.g, "Bad", vec![], Sort::Type(0));
    let field = Term::data(list, vec![Term::data(neg, vec![Term::Data(bad, vec![])])]);
    let e = stitchwort_core::check::define_ctors(
        &mut p.g,
        bad,
        vec![ctor("MkBad", vec![("inner", field)])],
    )
    .expect_err("refused");
    assert_eq!(e.code, "E-POSITIVITY");
    assert_eq!(
        e.message,
        "`Bad` is used inside `Neg`, and `Neg`'s field `consume` takes its parameter `a` as a \
         function's input"
    );
}

#[test]
fn a_parameter_of_a_type_wrapping_a_non_nestable_one_isnt_nestable() {
    use stitchwort_core::globals::{NotNestable, ParamUse};
    let mut p = Prelude::new();
    let neg = neg(&mut p);
    let list = p.list;
    let wrap = data(&mut p.g, "Wrap", vec![("a", ty())], Sort::Type(0));
    let inner = Term::data(list, vec![Term::data(neg, vec![v(0)])]);
    stitchwort_core::check::define_ctors(
        &mut p.g,
        wrap,
        vec![ctor("MkWrap", vec![("inner", inner)])],
    )
    .expect("Wrap");
    assert_eq!(
        p.g.data(wrap).nestable(),
        &[Err(NotNestable::Field {
            data: wrap,
            ctor: 0,
            field: 0,
            how: ParamUse::AtParameter {
                outer: neg,
                param: 0
            }
        })]
    );
}

#[test]
fn a_parameter_in_a_later_parameters_type_isnt_nestable() {
    use stitchwort_core::globals::NotNestable;
    let mut p = Prelude::new();
    let list = p.list;
    let dep = data(
        &mut p.g,
        "Dep",
        vec![("a", ty()), ("xs", Term::data(list, vec![v(0)]))],
        Sort::Type(0),
    );
    stitchwort_core::check::define_ctors(&mut p.g, dep, vec![ctor("MkDep", vec![("y", v(1))])])
        .expect("Dep");
    assert_eq!(
        p.g.data(dep).nestable(),
        &[
            Err(NotNestable::LaterParameter(1)),
            Err(NotNestable::NotAType)
        ]
    );
}

#[test]
fn a_field_may_not_mention_an_earlier_recursive_field() {
    // `FSucc (n: Fnat) (same: n = n)`: refused for depending on `n`, before
    // anything else.
    let mut p = Prelude::new();
    let code = data_code(&mut p.g, "Fnat", vec![], Sort::Type(0), |d| {
        let fnat = || Rc::new(Term::Data(d, vec![]));
        vec![
            ("n", Term::Data(d, vec![])),
            ("same", Term::Eq(Some(fnat()), Rc::new(v(0)), Rc::new(v(0)))),
        ]
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
        pi("q", prop(), arrow(Term::data(d, vec![v(1), v(0)]), result)),
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
    let swapped = Term::data(or, vec![v(0), v(1)]);
    let result = eliminate(
        &mut s,
        or,
        swapped,
        vec![
            (vec!["l"], Term::ctor(or, 1, vec![v(0)])),
            (vec!["r"], Term::ctor(or, 0, vec![v(0)])),
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

// The sort of a variable applied to arguments (`sort_of`, seen through
// `telescope`'s erasure flags and errors)

/// The erasure flags `telescope` gives the parameters of the closed type
/// `ty`, or the code of its error.
fn erased_params(p: &Prelude, ty: &Term) -> Result<Vec<bool>, &'static str> {
    let value = eval(&p.g.ev(), &[], ty).expect("type evaluates");
    stitchwort_core::check::telescope(&p.g.ev(), &value, span())
        .map(|t| t.params.iter().map(|(_, _, erased)| *erased).collect())
        .map_err(|d| d.code)
}

#[test]
fn sort_of_an_applied_variable_follows_the_codomain_of_its_type() {
    let p = Prelude::new();
    // (q : (T : Type 1) -> T) -> q Prop -> q (Type 0) -> Nat: `q Prop` is
    // a proposition (its proof is erased), `q (Type 0)` a type.
    let ty = pi(
        "q",
        pi("T", ty_n(1), v(0)),
        pi(
            "x",
            app(v(0), [prop()]),
            pi("y", app(v(1), [ty()]), p.nat_ty()),
        ),
    );
    assert_eq!(erased_params(&p, &ty), Ok(vec![false, true, false]));
}

#[test]
fn sort_of_an_applied_variable_still_rejects_wrong_applications() {
    let p = Prelude::new();
    let zero = p.num(0);
    // `q 0` with `q : Nat -> Nat -> Prop` is a function, not a type.
    let partial = pi(
        "q",
        arrow(p.nat_ty(), arrow(p.nat_ty(), prop())),
        pi("x", app(v(0), [zero.clone()]), p.nat_ty()),
    );
    assert_eq!(erased_params(&p, &partial), Err("E-NOT-A-TYPE"));
    // `q 0 0` with `q : Nat -> Prop` applies a non-function.
    let over = pi(
        "q",
        arrow(p.nat_ty(), prop()),
        pi("x", app(v(0), [zero.clone(), zero]), p.nat_ty()),
    );
    assert_eq!(erased_params(&p, &over), Err("E-NOT-A-FUNCTION"));
}

#[test]
fn rejects_matching_on_or_to_produce_a_type_valued_variable_applied_to_a_big_term() {
    let mut s = props();
    let or = s.or;
    let big = s.p.plus(s.p.num(20), s.p.num(20));
    // (r : Nat -> Type) (p q : Prop) (w : r big) -> Or p q -> r big
    let ty = pi(
        "r",
        arrow(s.p.nat_ty(), ty()),
        pi(
            "p",
            prop(),
            pi(
                "q",
                prop(),
                pi(
                    "w",
                    app(v(2), [big.clone()]),
                    arrow(Term::data(or, vec![v(2), v(1)]), app(v(3), [big])),
                ),
            ),
        ),
    );
    let body = lam(
        "r",
        lam(
            "p",
            lam(
                "q",
                lam(
                    "w",
                    lam("h", case(0, or, vec![(vec!["l"], v(2)), (vec!["r"], v(2))])),
                ),
            ),
        ),
    );
    assert_eq!(define(&mut s.p.g, "elim", ty, body), Err("E-PROP-ELIM"));
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
    // n => add n 0 normalises to itself: `add` can't unfold on a variable.
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
    let add = eval(&p.g.ev(), &[], &Term::Def(p.add)).unwrap();
    let eta = eval(&p.g.ev(), &[], &lam("x", app(Term::Def(p.add), [v(0)]))).unwrap();
    assert!(conv(&p.g.ev(), 0, &add, &eta).unwrap());
    assert!(conv(&p.g.ev(), 0, &eta, &add).unwrap());
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
                Rc::new(
                    quote(
                        &p.g.ev(),
                        0,
                        &infer_closed(&p.g.ev(), &term, span()).expect("checks").1,
                    )
                    .unwrap(),
                ),
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
    let list = |t: Term| Term::data(p.list, vec![t]);
    let cons = |h: Term, t: Term| Term::ctor(p.list, 1, vec![h, t]);
    let nil = || Term::Ctor(p.list, 0, vec![]);
    // Closed values, built without type checking.
    let value = |t: &Term| eval(&g.ev(), &[], t).unwrap();
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
            !conv(&g.ev(), 0, &value(a), &value(b)).unwrap(),
            "{a:?} should differ from {b:?}"
        );
        assert!(
            !conv(&g.ev(), 0, &value(b), &value(a)).unwrap(),
            "{b:?} should differ from {a:?}"
        );
    }
    for (a, _) in &differ {
        assert!(
            conv(&g.ev(), 0, &value(a), &value(a)).unwrap(),
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
    let value = |t: &Term| eval(&g.ev(), &env, t).unwrap();
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
            !conv(&g.ev(), 2, &value(a), &value(b)).unwrap(),
            "{a:?} should differ from {b:?}"
        );
    }
    assert!(
        conv(
            &g.ev(),
            2,
            &value(&p.plus(x.clone(), y.clone())),
            &value(&p.plus(x, y))
        )
        .unwrap()
    );
}

#[test]
fn conversion_compares_stuck_transports() {
    let p = Prelude::new();
    let g = &p.g;
    let nat = p.nat_ty();
    // J m b h, stuck on a proof variable h (level 0).
    let stuck = |motive: Term, base: Term| {
        eval(
            &g.ev(),
            &[Value::var(0)],
            &Term::J(Rc::new(motive), Rc::new(base), Rc::new(v(0))),
        )
        .unwrap()
    };
    let motive = |t: Term| lam("y", lam("q", t));
    let a = stuck(motive(nat.clone()), p.num(1));
    assert!(conv(&g.ev(), 1, &a, &stuck(motive(nat.clone()), p.num(1))).unwrap());
    assert!(
        !conv(&g.ev(), 1, &a, &stuck(motive(nat.clone()), p.num(2))).unwrap(),
        "different base"
    );
    assert!(
        !conv(&g.ev(), 1, &a, &stuck(motive(ty()), p.num(1))).unwrap(),
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
    let list_of_nat = Term::data(p.list, vec![p.nat_ty()]);
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
        Term::data(p.list, vec![p.nat_ty()]),
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
        vec![("f", pi("_", nat, Term::data(d, vec![v(1)])))]
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
        pi("n", nat.clone(), Term::data(p.list, vec![a_case()])),
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
            Term::ctor(p.list, 1, vec![nat.clone(), a_case()]),
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
        p.g.data(d).ctors()[0].field_erased,
        vec![false, true, true, true, false]
    );
}

#[test]
fn conversion_keeps_nested_binders_apart() {
    let p = Prelude::new();
    let g = &p.g;
    let closed = |t: &Term| eval(&g.ev(), &[], t).unwrap();
    // x y => x  vs  x y => y
    let first = lam("x", lam("y", v(1)));
    let second = lam("x", lam("y", v(0)));
    assert!(!conv(&g.ev(), 0, &closed(&first), &closed(&second)).unwrap());
    // (x : Type) -> (y : Type) -> x  vs  … -> y
    let first = pi("x", ty(), pi("y", ty(), v(1)));
    let second = pi("x", ty(), pi("y", ty(), v(0)));
    assert!(!conv(&g.ev(), 0, &closed(&first), &closed(&second)).unwrap());
    // Eta, twice: with f a variable, x y => f y x is not f.
    let f = Value::var(0);
    let flipped = eval(
        &g.ev(),
        std::slice::from_ref(&f),
        &lam("x", lam("y", app(v(2), [v(0), v(1)]))),
    )
    .unwrap();
    let unflipped = eval(
        &g.ev(),
        std::slice::from_ref(&f),
        &lam("x", lam("y", app(v(2), [v(1), v(0)]))),
    )
    .unwrap();
    assert!(!conv(&g.ev(), 1, &flipped, &f).unwrap());
    assert!(conv(&g.ev(), 1, &unflipped, &f).unwrap());
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

/// A prelude's `Bool`, registered, with its type and `True`.
fn with_bool(p: &mut Prelude) -> (stitchwort_core::DataId, Term, Term) {
    let bool_ = data(&mut p.g, "Bool", vec![], Sort::Type(0));
    stitchwort_core::check::define_ctors(
        &mut p.g,
        bool_,
        vec![ctor("False", vec![]), ctor("True", vec![])],
    )
    .unwrap();
    stitchwort_core::native::register_bool(&mut p.g, bool_).unwrap();
    (
        bool_,
        Term::data(bool_, vec![]),
        Term::ctor(bool_, 1, vec![]),
    )
}

/// A record type with parameters `params` and fields `fields`.
fn record_type(
    p: &mut Prelude,
    name: &str,
    params: Vec<(&str, Term)>,
    fields: Vec<(&str, Term)>,
) -> stitchwort_core::DataId {
    let d = stitchwort_core::check::declare_data_group_as(
        &mut p.g,
        params.into_iter().map(|(x, t)| (x.into(), t)).collect(),
        Sort::Type(0),
        vec![(name.into(), name.into(), span(), true)],
    )
    .unwrap()[0];
    stitchwort_core::check::define_ctors(&mut p.g, d, vec![ctor(&format!("Mk{name}"), fields)])
        .unwrap();
    d
}

/// A prelude with `Decidable`, the record `{ holds: Bool, sound: holds =
/// True → p }`, and a definition `f : (n : Nat) -> [auto ok : n = n] -> Nat`;
/// with `True`.
fn with_decidable() -> (
    Prelude,
    stitchwort_core::DataId,
    stitchwort_core::DefId,
    Term,
) {
    let mut p = Prelude::new();
    let (_, bool_ty, tru) = with_bool(&mut p);
    let decidable = record_type(
        &mut p,
        "Decidable",
        vec![("p", prop())],
        vec![
            ("holds", bool_ty.clone()),
            ("sound", arrow(eq(Some(bool_ty), v(0), tru.clone()), v(1))),
        ],
    );
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
    (p, decidable, f, tru)
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
    let (mut p, decidable, f, tru) = with_decidable();
    // `{ holds = True, sound = h => rfl }`, in the context [n].
    let yes = Term::ctor(decidable, 0, vec![tru, lam("h", Term::Refl)]);
    assert_eq!(validate(&mut p, f, 1, decidable, yes), "ok");
    assert_eq!(p.g.def(f).validators().len(), 1);
}

#[test]
fn rejects_validators_that_do_not_decide_the_precondition() {
    let (mut p, decidable, f, tru) = with_decidable();
    let yes = || Term::ctor(decidable, 0, vec![tru.clone(), lam("h", Term::Refl)]);
    // Not for a proof parameter: `n` is data.
    assert_eq!(validate(&mut p, f, 0, decidable, yes()), "E-MALFORMED");
    // No such parameter.
    assert_eq!(validate(&mut p, f, 5, decidable, yes()), "E-MALFORMED");
    // A decision of something else: one of `0 = 0` has type `Decidable (0
    // = 0)`, not `Decidable (n = n)`.
    let other = Term::Ann(
        Rc::new(yes()),
        Rc::new(Term::data(decidable, vec![eq(None, p.num(0), p.num(0))])),
    );
    assert_eq!(validate(&mut p, f, 1, decidable, other), "E-TYPE-MISMATCH");
    // A `case` isn't allowed in a validator.
    let with_case = case(0, p.nat, vec![(vec![], yes()), (vec!["k"], yes())]);
    assert_eq!(validate(&mut p, f, 1, decidable, with_case), "E-MALFORMED");
}

#[test]
fn rejects_validators_whose_data_type_is_not_shaped_like_decidable() {
    let (mut p, _, f, tru) = with_decidable();
    let bool_ty = match &tru {
        Term::Ctor(b, _, _) => Term::data(*b, vec![]),
        _ => unreachable!(),
    };
    let sound = |p_ix: usize| arrow(eq(Some(bool_ty.clone()), v(0), tru.clone()), v(p_ix));
    // Each of these differs from `Decidable` in one way that matters:
    // extracted JS reads the first field being `True` as "the precondition
    // holds".
    type Shape<'a> = (Vec<(&'a str, Term)>, Vec<(&'a str, Term)>);
    let shapes: Vec<Shape> = vec![
        // A `Type` parameter instead of a `Prop`.
        (
            vec![("p", ty())],
            vec![("holds", bool_ty.clone()), ("sound", sound(1))],
        ),
        // Two parameters.
        (
            vec![("p", prop()), ("q", prop())],
            vec![("holds", bool_ty.clone()), ("sound", sound(2))],
        ),
        // Only the test.
        (vec![("p", prop())], vec![("holds", bool_ty.clone())]),
        // The test isn't a `Bool`.
        (
            vec![("p", prop())],
            vec![
                ("holds", p.nat_ty()),
                ("sound", arrow(eq(None, v(0), p.num(1)), v(1))),
            ],
        ),
        // The second field doesn't say that `True` proves `p`.
        (
            vec![("p", prop())],
            vec![
                ("holds", bool_ty.clone()),
                ("sound", arrow(eq(Some(bool_ty.clone()), v(0), v(0)), v(1))),
            ],
        ),
    ];
    for (i, (params, fields)) in shapes.into_iter().enumerate() {
        let d = record_type(&mut p, &format!("Fake{i}"), params, fields);
        // Whatever the decision term, the shape is refused first.
        assert_eq!(
            validate(&mut p, f, 1, d, Term::Refl),
            "E-MALFORMED",
            "shape {i}"
        );
    }
    // Not a record: `Yes p | No`.
    let two = data(&mut p.g, "TwoCtors", vec![("p", prop())], Sort::Type(0));
    stitchwort_core::check::define_ctors(
        &mut p.g,
        two,
        vec![ctor("Yes", vec![("proof", v(0))]), ctor("No", vec![])],
    )
    .unwrap();
    assert_eq!(validate(&mut p, f, 1, two, Term::Refl), "E-MALFORMED");
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
    // constructor takes a `Neg 0`, which is `Bad -> Nat` in disguise. `Neg`
    // is refused for using `Bad` before it's finished, and `Bad` for using
    // something declared later.
    let mut p = Prelude::new();
    let bad = data(&mut p.g, "Bad", vec![], Sort::Type(0));
    let neg_ty = arrow(p.nat_ty(), ty());
    let neg = declare(&mut p.g, "Neg", neg_ty);
    let neg_body = lam("n", arrow(Term::Data(bad, vec![]), p.nat_ty()));
    let result = stitchwort_core::check::define_def(&mut p.g, neg, &neg_body);
    assert_eq!(result.err().map(|e| e.code), Some("E-MALFORMED"));
    let field = app(Term::Def(neg), [p.num(0)]);
    let result = define_ctors(&mut p.g, bad, vec![ctor("MkBad", vec![("f", field)])]);
    assert_eq!(result.err().map(|e| e.code), Some("E-POSITIVITY"));
}

#[test]
fn a_negative_occurrence_hidden_in_a_later_data_type_is_refused() {
    use stitchwort_core::check::define_ctors;
    // `Wrap = MkWrap (Bad -> Nat)`, declared after `Bad`, then used in `Bad`.
    // `Wrap` is refused for using `Bad` before it's finished, and `Bad` for
    // using something declared later.
    let mut p = Prelude::new();
    let bad = data(&mut p.g, "Bad", vec![], Sort::Type(0));
    let wrap = data(&mut p.g, "Wrap", vec![], Sort::Type(0));
    let neg = arrow(Term::Data(bad, vec![]), p.nat_ty());
    let result = define_ctors(&mut p.g, wrap, vec![ctor("MkWrap", vec![("f", neg)])]);
    assert_eq!(result.err().map(|e| e.code), Some("E-MALFORMED"));
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
    // `succ n = Succ n`, unapplied, equals `n => Succ n`.
    let mut p = Prelude::new();
    let nat = p.nat;
    let ty = arrow(p.nat_ty(), p.nat_ty());
    let succ = define(
        &mut p.g,
        "succ",
        ty,
        lam("n", Term::ctor(nat, 1, vec![v(0)])),
    )
    .unwrap();
    let f = eval(&p.g.ev(), &[], &Term::Def(succ)).unwrap();
    let g = eval(&p.g.ev(), &[], &lam("n", Term::ctor(nat, 1, vec![v(0)]))).unwrap();
    assert!(conv(&p.g.ev(), 0, &f, &g).unwrap());
    assert!(conv(&p.g.ev(), 0, &g, &f).unwrap());
    let other = eval(&p.g.ev(), &[], &lam("n", v(0))).unwrap();
    assert!(!conv(&p.g.ev(), 0, &f, &other).unwrap());
}

// Two different definitions stuck on a `case` (SW-386, D1091)

/// `pred n = case n of Zero -> zero; Succ m -> m`, named `name`.
fn define_pred(p: &mut Prelude, name: &str, zero: Term) -> stitchwort_core::DefId {
    let nat = p.nat;
    let ty = arrow(p.nat_ty(), p.nat_ty());
    let body = lam("n", case(0, nat, vec![(vec![], zero), (vec!["m"], v(0))]));
    define(&mut p.g, name, ty, body).unwrap()
}

/// `f n` for the variable `n` (level 0), as a value.
fn applied(p: &Prelude, f: stitchwort_core::DefId) -> Value {
    eval(&p.g.ev(), &[Value::var(0)], &app(Term::Def(f), [v(0)])).unwrap()
}

/// `(n: Nat) -> f n = g n`.
fn agree(p: &Prelude, f: stitchwort_core::DefId, g: stitchwort_core::DefId) -> Term {
    pi(
        "n",
        p.nat_ty(),
        eq(None, app(Term::Def(f), [v(0)]), app(Term::Def(g), [v(0)])),
    )
}

#[test]
fn two_definitions_with_the_same_case_tree_are_equal_when_stuck() {
    let mut p = Prelude::new();
    let zero = p.num(0);
    let first = define_pred(&mut p, "first", zero.clone());
    let second = define_pred(&mut p, "second", zero);
    assert!(conv(&p.g.ev(), 1, &applied(&p, first), &applied(&p, second)).unwrap());
    // So `rfl` proves it, in the kernel.
    let statement = agree(&p, first, second);
    assert!(define(&mut p.g, "same", statement, lam("n", Term::Refl)).is_ok());
}

#[test]
fn two_definitions_with_different_branches_stay_different() {
    let mut p = Prelude::new();
    let zero = p.num(0);
    let one = p.num(1);
    let first = define_pred(&mut p, "first", zero);
    let second = define_pred(&mut p, "second", one);
    assert!(!conv(&p.g.ev(), 1, &applied(&p, first), &applied(&p, second)).unwrap());
    let statement = agree(&p, first, second);
    assert!(define(&mut p.g, "different", statement, lam("n", Term::Refl)).is_err());
}

#[test]
fn the_same_case_tree_on_different_scrutinees_stays_different() {
    let mut p = Prelude::new();
    let zero = p.num(0);
    let first = define_pred(&mut p, "first", zero.clone());
    let second = define_pred(&mut p, "second", zero);
    let env = [Value::var(0), Value::var(1)];
    let a = eval(&p.g.ev(), &env, &app(Term::Def(first), [v(0)])).unwrap();
    let b = eval(&p.g.ev(), &env, &app(Term::Def(second), [v(1)])).unwrap();
    assert!(!conv(&p.g.ev(), 2, &a, &b).unwrap());
}

#[test]
fn recursive_definitions_are_not_compared_by_their_case_trees() {
    // A copy of `add`: the same tree, but recursive, so it's left alone
    // (comparing it by its tree could unfold forever).
    let mut p = Prelude::new();
    let nat = p.nat;
    let nat_ty = p.nat_ty();
    let copy = declare(
        &mut p.g,
        "copy",
        arrow(nat_ty.clone(), arrow(nat_ty.clone(), nat_ty)),
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
                        Term::ctor(nat, 1, vec![app(Term::Def(copy), [v(0), v(1)])]),
                    ),
                ],
            ),
        ),
    );
    stitchwort_core::check::define_def(&mut p.g, copy, &body).unwrap();
    let env = [Value::var(0)];
    let a = eval(&p.g.ev(), &env, &app(Term::Def(p.add), [v(0), p.num(1)])).unwrap();
    let b = eval(&p.g.ev(), &env, &app(Term::Def(copy), [v(0), p.num(1)])).unwrap();
    assert!(!conv(&p.g.ev(), 1, &a, &b).unwrap());
}

/// A chain of `levels` helpers above `{name}0`, a `pred` answering `zero`:
/// each `{name}k n` is a `case` on `n` calling `{name}(k-1) n` in both
/// branches. Returns the top one.
fn define_chain(p: &mut Prelude, name: &str, zero: Term, levels: usize) -> stitchwort_core::DefId {
    let nat = p.nat;
    let mut below = define_pred(p, &format!("{name}0"), zero);
    for level in 1..=levels {
        let ty = arrow(p.nat_ty(), p.nat_ty());
        let body = lam(
            "n",
            case(
                0,
                nat,
                vec![
                    (vec![], app(Term::Def(below), [v(0)])),
                    (vec!["m"], app(Term::Def(below), [v(1)])),
                ],
            ),
        );
        below = define(&mut p.g, &format!("{name}{level}"), ty, body).unwrap();
    }
    below
}

#[test]
fn chains_of_helpers_calling_the_next_in_both_branches_are_compared_once_per_level() {
    // Comparing `a40 n` with `b40 n` meets each pair `a{k} n`, `b{k} n`
    // 2^(40-k) times. A pair already found equal is answered at once
    // (SW-395), so a small budget is plenty; without that, it runs out.
    use stitchwort_core::Limits;
    let mut p = Prelude::new();
    let zero = p.num(0);
    let one = p.num(1);
    let a = define_chain(&mut p, "a", zero.clone(), 40);
    let b = define_chain(&mut p, "b", zero, 40);
    let c = define_chain(&mut p, "c", one, 40);
    let _op = p.g.machine.budget.operation(Limits {
        work: 1_000_000,
        ..Limits::default()
    });
    assert!(conv(&p.g.ev(), 1, &applied(&p, a), &applied(&p, b)).unwrap());
    // A difference at the bottom is still found.
    assert!(!conv(&p.g.ev(), 1, &applied(&p, a), &applied(&p, c)).unwrap());
}

// Two calls of the same definition, compared by their arguments first (D483,
// docs/proposals/folded-calls.md §7 stage 4): the kernel checks a body with
// calls kept glued, so `f a` against `f b` is equal at once when `a` and `b`
// are, and is compared by unfolding otherwise.

/// `{name} r s`: `r` rounds of `s + s` on `s`. Each round mentions the last
/// one twice, so the value written out doubles with every round: comparing
/// two separately computed copies of `{name} 40 s` part by part takes 2^40
/// steps.
fn define_mix(p: &mut Prelude, name: &str) -> stitchwort_core::DefId {
    let nat = p.nat;
    let nat_ty = p.nat_ty();
    let mix = declare(
        &mut p.g,
        name,
        arrow(nat_ty.clone(), arrow(nat_ty.clone(), nat_ty)),
    );
    let body = lam(
        "r",
        lam(
            "s",
            case(
                1,
                nat,
                vec![
                    (vec![], v(0)),
                    (vec!["r'"], app(Term::Def(mix), [v(0), p.plus(v(1), v(1))])),
                ],
            ),
        ),
    );
    stitchwort_core::check::define_def(&mut p.g, mix, &body).expect("mix");
    mix
}

/// `konst x y = x`.
fn define_konst(p: &mut Prelude) -> stitchwort_core::DefId {
    let nat_ty = p.nat_ty();
    let ty = arrow(nat_ty.clone(), arrow(nat_ty.clone(), nat_ty));
    define(&mut p.g, "konst", ty, lam("x", lam("y", v(1)))).unwrap()
}

/// [`define`], within a budget far too small to compare two copies of
/// `mix 40 s` part by part.
fn define_small(p: &mut Prelude, name: &str, ty: Term, body: Term) -> Result<(), &'static str> {
    let saved = p.g.machine.budget.start(stitchwort_core::Limits {
        work: 100_000,
        ..stitchwort_core::Limits::default()
    });
    let verdict = define(&mut p.g, name, ty, body).map(|_| ());
    p.g.machine.budget.restore(saved);
    verdict
}

#[test]
fn same_call_arguments_first_accepts_equal_arguments_without_unfolding() {
    let mut p = Prelude::new();
    let mix = define_mix(&mut p, "mix");
    let other = define_mix(&mut p, "mixAgain");
    let konst = define_konst(&mut p);
    let rounds = p.num(40);
    let mix_of = |f, s: Term| app(Term::Def(f), [rounds.clone(), s]);
    // `(s: Nat) -> mix 40 s = mix 40 s`.
    let same = pi(
        "s",
        p.nat_ty(),
        eq(None, mix_of(mix, v(0)), mix_of(mix, v(0))),
    );
    assert_eq!(
        define_small(&mut p, "same", same, lam("s", Term::Refl)),
        Ok(())
    );
    // Arguments convertible but not alike: `konst s t` is `s`.
    let convertible = pi(
        "s",
        p.nat_ty(),
        pi(
            "t",
            p.nat_ty(),
            eq(
                None,
                mix_of(mix, app(Term::Def(konst), [v(1), v(0)])),
                mix_of(mix, v(1)),
            ),
        ),
    );
    assert_eq!(
        define_small(
            &mut p,
            "convertible",
            convertible,
            lam("s", lam("t", Term::Refl))
        ),
        Ok(())
    );
    // The control: the same definition under another name has to be
    // unfolded, which the budget doesn't allow.
    let unfolded = pi(
        "s",
        p.nat_ty(),
        eq(None, mix_of(mix, v(0)), mix_of(other, v(0))),
    );
    assert_eq!(
        define_small(&mut p, "unfolded", unfolded, lam("s", Term::Refl)),
        Err("E-RESOURCE")
    );
}

#[test]
fn same_call_different_arguments_with_equal_results_are_still_equal() {
    let mut p = Prelude::new();
    let konst = define_konst(&mut p);
    let mix = define_mix(&mut p, "mix");
    // `(a b: Nat) -> konst 0 a = konst 0 b`: the arguments differ, the
    // unfoldings don't.
    let statement = pi(
        "a",
        p.nat_ty(),
        pi(
            "b",
            p.nat_ty(),
            eq(
                None,
                app(Term::Def(konst), [p.num(0), v(1)]),
                app(Term::Def(konst), [p.num(0), v(0)]),
            ),
        ),
    );
    assert_eq!(
        define_small(&mut p, "ignored", statement, lam("a", lam("b", Term::Refl))),
        Ok(())
    );
    // `mix 2 0 = mix 1 0`: different arguments, both 0.
    let statement = eq(
        None,
        app(Term::Def(mix), [p.num(2), p.num(0)]),
        app(Term::Def(mix), [p.num(1), p.num(0)]),
    );
    assert_eq!(define_small(&mut p, "zeros", statement, Term::Refl), Ok(()));
}

#[test]
fn same_call_different_results_are_still_rejected() {
    let mut p = Prelude::new();
    let konst = define_konst(&mut p);
    let mix = define_mix(&mut p, "mix");
    // `(a b: Nat) -> konst a 0 = konst b 0` is false.
    let statement = pi(
        "a",
        p.nat_ty(),
        pi(
            "b",
            p.nat_ty(),
            eq(
                None,
                app(Term::Def(konst), [v(1), p.num(0)]),
                app(Term::Def(konst), [v(0), p.num(0)]),
            ),
        ),
    );
    assert_eq!(
        define_small(&mut p, "wrong", statement, lam("a", lam("b", Term::Refl))),
        Err("E-REFL")
    );
    // `(s: Nat) -> mix 3 s = mix 3 (Succ s)` is false.
    let statement = pi(
        "s",
        p.nat_ty(),
        eq(
            None,
            app(Term::Def(mix), [p.num(3), v(0)]),
            app(Term::Def(mix), [p.num(3), p.succ(v(0))]),
        ),
    );
    assert_eq!(
        define_small(&mut p, "wrongMix", statement, lam("s", Term::Refl)),
        Err("E-REFL")
    );
}

#[test]
fn same_call_failures_do_not_repeat_work() {
    // `next n = Succ n`, and `next^40 x` against `next^40 y`. The arguments
    // of each pair differ, and so does each pair's unfolding, which holds
    // the pair below again: without remembering the pairs found different,
    // each level would compare the one below twice, 2^40 times in all.
    // It's rejected within a small budget, and takes the same steps each
    // time.
    let run = || {
        let mut p = Prelude::new();
        let nat = p.nat;
        let nat_to_nat = arrow(p.nat_ty(), p.nat_ty());
        let next = define(
            &mut p.g,
            "next",
            nat_to_nat,
            lam("n", Term::ctor(nat, 1, vec![v(0)])),
        )
        .unwrap();
        let tower = |x: Term| (0..40).fold(x, |t, _| app(Term::Def(next), [t]));
        let statement = pi(
            "x",
            p.nat_ty(),
            pi("y", p.nat_ty(), eq(None, tower(v(1)), tower(v(0)))),
        );
        let before = p.g.machine.budget.total_work();
        let verdict = define_small(&mut p, "towers", statement, lam("x", lam("y", Term::Refl)));
        (verdict, p.g.machine.budget.total_work() - before)
    };
    let (verdict, steps) = run();
    assert_eq!(verdict, Err("E-REFL"));
    assert_eq!(run().1, steps, "the steps taken changed between runs");
}

// The kernel's read-backs keep glued calls (D1293, `check.rs`, "Read-backs
// that keep calls"): a case's goal and the values refined on entering a
// branch are read back with `f a` written as the call, not its unfolding.

/// `big s = mix rounds s`: a call that doesn't step at once (its body isn't
/// a `case`), so a read-back keeps it, whose unfolding is `mix rounds s`
/// written out, 2^rounds nodes.
fn define_big(p: &mut Prelude, rounds: usize) -> stitchwort_core::DefId {
    let mix = define_mix(p, &format!("mix{rounds}"));
    let nat_ty = p.nat_ty();
    let body = lam("s", app(Term::Def(mix), [p.num(rounds), v(0)]));
    define(
        &mut p.g,
        &format!("big{rounds}"),
        arrow(nat_ty.clone(), nat_ty),
        body,
    )
    .unwrap()
}

/// `case n { Zero => zero; Succ _ => succ }`, on variable `n`.
fn on_nat(p: &Prelude, n: usize, zero: Term, succ: Term) -> Term {
    case(n, p.nat, vec![(vec![], zero), (vec!["m"], succ)])
}

/// Two definitions, each within `budget` steps: `(n s: Nat) -> big s =
/// big s` by a case on `n` (the goal read back by `check_case`), and `(s:
/// Nat) -> (h: big s = big s) -> (n: Nat) -> Nat` by a case on `n` (`h`'s
/// type read back by `substitute`). Their verdicts, and the steps taken.
fn kept_call_cases(rounds: usize, budget: u64) -> (Vec<Result<(), &'static str>>, u64) {
    let mut p = Prelude::new();
    let big = define_big(&mut p, rounds);
    let big_of = |t: Term| app(Term::Def(big), [t]);
    let before = p.g.machine.budget.total_work();
    let mut verdicts = Vec::new();
    let mut run = |p: &mut Prelude, name: &str, ty: Term, body: Term| {
        let saved = p.g.machine.budget.start(stitchwort_core::Limits {
            work: budget,
            ..stitchwort_core::Limits::default()
        });
        verdicts.push(define(&mut p.g, name, ty, body).map(|_| ()));
        p.g.machine.budget.restore(saved);
    };
    let goal = pi(
        "n",
        p.nat_ty(),
        pi("s", p.nat_ty(), eq(None, big_of(v(0)), big_of(v(0)))),
    );
    let body = lam("n", lam("s", on_nat(&p, 1, Term::Refl, Term::Refl)));
    run(&mut p, "inGoal", goal, body);
    let context = pi(
        "s",
        p.nat_ty(),
        pi(
            "h",
            eq(None, big_of(v(0)), big_of(v(0))),
            pi("n", p.nat_ty(), p.nat_ty()),
        ),
    );
    let body = lam("s", lam("h", lam("n", on_nat(&p, 0, p.num(0), v(1)))));
    run(&mut p, "inContext", context, body);
    (verdicts, p.g.machine.budget.total_work() - before)
}

#[test]
fn kernel_read_backs_keep_calls() {
    // Written out, `big 40 s` is 2^40 nodes; kept, both cases check within
    // 100,000 steps.
    let (verdicts, _) = kept_call_cases(40, 100_000);
    assert_eq!(verdicts, vec![Ok(()), Ok(())]);
    // A timing-free measure: the steps don't grow with the unfolding.
    // Written out, `big 16 s` would be 2^8 times `big 8 s`; kept, the steps
    // grow by a few per round (548 and 836 when written).
    let (verdicts, steps_8) = kept_call_cases(8, u64::MAX);
    assert_eq!(verdicts, vec![Ok(()), Ok(())]);
    let (_, steps_16) = kept_call_cases(16, u64::MAX);
    assert!(
        steps_16 < 2 * steps_8,
        "a read-back unfolded `big`: {steps_8} steps, then {steps_16}"
    );
    // The control: `mix 40 s` steps at once (by its case on 40), so it's
    // read back unfolded, which the budget doesn't allow.
    let mut p = Prelude::new();
    let mix = define_mix(&mut p, "mix");
    let mix_of = |t: Term| app(Term::Def(mix), [p.num(40), t]);
    let goal = pi(
        "n",
        p.nat_ty(),
        pi("s", p.nat_ty(), eq(None, mix_of(v(0)), mix_of(v(0)))),
    );
    let body = lam("n", lam("s", on_nat(&p, 1, Term::Refl, Term::Refl)));
    assert_eq!(
        define_small(&mut p, "control", goal, body),
        Err("E-RESOURCE")
    );
}

#[test]
fn kept_calls_with_different_arguments_are_still_compared_by_unfolding() {
    let mut p = Prelude::new();
    let konst = define_konst(&mut p);
    let konst_of = |a: Term, b: Term| app(Term::Def(konst), [a, b]);
    // `(n a b: Nat) -> konst 0 a = konst 0 b`, by a case on `n`: the goal
    // keeps both calls, whose arguments differ and unfoldings don't.
    let goal = pi(
        "n",
        p.nat_ty(),
        pi(
            "a",
            p.nat_ty(),
            pi(
                "b",
                p.nat_ty(),
                eq(None, konst_of(p.num(0), v(1)), konst_of(p.num(0), v(0))),
            ),
        ),
    );
    let body = lam(
        "n",
        lam("a", lam("b", on_nat(&p, 2, Term::Refl, Term::Refl))),
    );
    assert_eq!(define_small(&mut p, "ignored", goal, body), Ok(()));
    // `(n: Nat) -> konst 0 n = konst 0 (Succ n)`, by a case on `n`: the
    // matched variable is substituted into the kept calls' arguments.
    let goal = pi(
        "n",
        p.nat_ty(),
        eq(
            None,
            konst_of(p.num(0), v(0)),
            konst_of(p.num(0), p.succ(v(0))),
        ),
    );
    let body = lam("n", on_nat(&p, 0, Term::Refl, Term::Refl));
    assert_eq!(define_small(&mut p, "substituted", goal, body), Ok(()));
}

#[test]
fn kept_calls_still_refuse_false_goals() {
    let mut p = Prelude::new();
    let konst = define_konst(&mut p);
    let konst_of = |a: Term, b: Term| app(Term::Def(konst), [a, b]);
    // `(n a b: Nat) -> konst a 0 = konst b 0`, by a case on `n`, is false.
    let goal = pi(
        "n",
        p.nat_ty(),
        pi(
            "a",
            p.nat_ty(),
            pi(
                "b",
                p.nat_ty(),
                eq(None, konst_of(v(1), p.num(0)), konst_of(v(0), p.num(0))),
            ),
        ),
    );
    let body = lam(
        "n",
        lam("a", lam("b", on_nat(&p, 2, Term::Refl, Term::Refl))),
    );
    assert_eq!(define_small(&mut p, "wrong", goal, body), Err("E-REFL"));
    // `(n: Nat) -> big n = big (Succ n)`, by a case on `n`, is false in
    // both branches once `n` is substituted into the kept calls.
    let big = define_big(&mut p, 3);
    let big_of = |t: Term| app(Term::Def(big), [t]);
    let goal = pi(
        "n",
        p.nat_ty(),
        eq(None, big_of(v(0)), big_of(p.succ(v(0)))),
    );
    let body = lam("n", on_nat(&p, 0, Term::Refl, Term::Refl));
    assert_eq!(define_small(&mut p, "wrongBig", goal, body), Err("E-REFL"));
}

/// The erased placeholder reads back as the elision `…`, alone, applied and
/// inside a constructor, not as a variable outside the context, whose index
/// `level - 1 - l` would wrap (a debug assertion, a wrong variable in a
/// release build). An error message's counterexample reads back values that
/// hold it for a hypothesis's proof (SW-2757: `MkChar 98 h` with `h`
/// erased). A real variable still reads back as itself.
#[test]
fn the_erased_placeholder_reads_back_as_the_elision() {
    let p = Prelude::new();
    let g = p.g.ev();
    let env = [stitchwort_core::erase::erased()];
    let read = |t: Term| format!("{:?}", quote(&g, 0, &eval(&g, &env, &t).unwrap()).unwrap());
    let elided = || Term::Meta(stitchwort_core::value::ELIDED);
    assert_eq!(read(v(0)), format!("{:?}", elided()));
    assert_eq!(read(app(v(0), [p.num(1)])), format!("{:?}", elided()));
    assert_eq!(
        read(Term::ctor(p.nat, 1, vec![v(0)])),
        format!("{:?}", Term::ctor(p.nat, 1, vec![elided()]))
    );
    assert_eq!(
        format!("{:?}", quote(&g, 1, &Value::var(0)).unwrap()),
        format!("{:?}", Term::Var(0))
    );
}

/// `Args : Nat -> Type`, where `Args 0 = Nat` and `Args (m + 1) = Nat ->
/// `Args m`: the type of a function of `n` numbers.
fn args_family(p: &mut Prelude) -> stitchwort_core::DefId {
    let nat = p.nat_ty();
    let args_ty = declare(&mut p.g, "Args", arrow(nat.clone(), ty()));
    let body = lam(
        "n",
        case(
            0,
            p.nat,
            vec![
                (vec![], nat.clone()),
                (
                    vec!["m"],
                    arrow(nat.clone(), app(Term::Def(args_ty), [v(0)])),
                ),
            ],
        ),
    );
    stitchwort_core::check::define_def(&mut p.g, args_ty, &body).expect("Args");
    args_ty
}

/// An application's spine is checked in one loop, not a level of the Rust
/// stack per argument: `f n 0 0 … 0`, with `f : (n: Nat) → Args n` and
/// `Args n` the type of a function of `n` numbers, applied to 20,000 of
/// them (SW-3133).
#[test]
fn a_long_spine_is_inferred_in_a_loop() {
    let mut p = Prelude::new();
    stitchwort_core::native::register_nat(&mut p.g, p.nat).expect("Nat");
    let nat = p.nat_ty();
    let args_ty = args_family(&mut p);
    let f = declare(
        &mut p.g,
        "f",
        pi("n", nat.clone(), app(Term::Def(args_ty), [v(0)])),
    );
    let n = 20_000;
    let term = app(
        Term::Def(f),
        std::iter::once(Term::Nat(Rc::new(n.into()))).chain((0..n).map(|_| p.num(0))),
    );
    let (checked, ty) = infer_closed(&p.g.ev(), &term, span()).expect("checks");
    assert_eq!(checked.spine().1.len(), n + 1);
    assert!(matches!(ty, Value::Data(d, _) if d == p.nat), "{ty:?}");
}

/// A loop that checked the arguments but kept the first argument's type for
/// every position would accept this; the bad argument is half-way down the
/// spine (SW-3133).
#[test]
fn a_bad_argument_in_the_middle_of_a_long_spine_is_rejected() {
    let mut p = Prelude::new();
    stitchwort_core::native::register_nat(&mut p.g, p.nat).expect("Nat");
    let nat = p.nat_ty();
    let args_ty = args_family(&mut p);
    let f = declare(
        &mut p.g,
        "f",
        pi("n", nat.clone(), app(Term::Def(args_ty), [v(0)])),
    );
    let (_, _, tru) = with_bool(&mut p);
    let n: usize = 1_000;
    let term = app(
        Term::Def(f),
        std::iter::once(Term::Nat(Rc::new(n.into())))
            .chain((0..n).map(|i| if i == 500 { tru.clone() } else { p.num(0) })),
    );
    assert_eq!(infer_code(&p.g, &term), "E-TYPE-MISMATCH");
}

/// The same with the ill-typed argument last (SW-3133).
#[test]
fn a_bad_argument_at_the_end_of_a_long_spine_is_rejected() {
    let mut p = Prelude::new();
    stitchwort_core::native::register_nat(&mut p.g, p.nat).expect("Nat");
    let nat = p.nat_ty();
    let args_ty = args_family(&mut p);
    let f = declare(
        &mut p.g,
        "f",
        pi("n", nat.clone(), app(Term::Def(args_ty), [v(0)])),
    );
    let (_, _, tru) = with_bool(&mut p);
    let n: usize = 1_000;
    let term = app(
        Term::Def(f),
        std::iter::once(Term::Nat(Rc::new(n.into())))
            .chain((0..n).map(|i| if i == n - 1 { tru.clone() } else { p.num(0) })),
    );
    assert_eq!(infer_code(&p.g, &term), "E-TYPE-MISMATCH");
}

/// A later argument's type is the codomain applied to the earlier argument:
/// `g : (n: Nat) → Args n → Nat` accepts a function of three numbers where it
/// expects `Args 3`, but not where it expects `Args 2` (SW-3133).
#[test]
fn a_later_domain_is_instantiated_with_the_earlier_argument() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let args_ty = args_family(&mut p);
    let g = declare(
        &mut p.g,
        "g",
        pi(
            "n",
            nat.clone(),
            arrow(app(Term::Def(args_ty), [v(0)]), nat.clone()),
        ),
    );
    // `Args 3 = Nat → Nat → Nat → Nat`, so three lambdas have type `Args 3`.
    let three = lam("a", lam("b", lam("c", p.num(0))));
    let applied_to_three = app(Term::Def(g), [p.num(3), three.clone()]);
    let (_, ty) = infer_closed(&p.g.ev(), &applied_to_three, span()).expect("checks");
    assert!(matches!(ty, Value::Data(d, _) if d == p.nat), "{ty:?}");
    let applied_to_two = app(Term::Def(g), [p.num(2), three]);
    assert_eq!(infer_code(&p.g, &applied_to_two), "E-TYPE-MISMATCH");
}

/// Past the last domain the type is `Nat`, not `Args 0`, and the message says
/// so (SW-3133).
#[test]
fn an_argument_too_many_is_not_a_function() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let args_ty = args_family(&mut p);
    let f = declare(
        &mut p.g,
        "f",
        pi("n", nat.clone(), app(Term::Def(args_ty), [v(0)])),
    );
    let zero = p.num(0);
    let term = app(
        Term::Def(f),
        [p.num(3), zero.clone(), zero.clone(), zero.clone(), zero],
    );
    let d = infer_closed(&p.g.ev(), &term, span()).expect_err("refused");
    assert_eq!(d.code, "E-NOT-A-FUNCTION");
    assert!(
        d.labels[0].message.contains("its type is `Nat`"),
        "{}",
        d.labels[0].message
    );
    assert!(
        !d.labels[0].message.contains("Args"),
        "{}",
        d.labels[0].message
    );
}

/// `check` infers a long spine and compares its type with the expected one
/// (`check_app`), not only `infer` (SW-3133).
#[test]
fn checking_a_long_spine_against_the_wrong_type_is_rejected() {
    let mut p = Prelude::new();
    stitchwort_core::native::register_nat(&mut p.g, p.nat).expect("Nat");
    let nat = p.nat_ty();
    let args_ty = args_family(&mut p);
    let f = declare(
        &mut p.g,
        "f",
        pi("n", nat.clone(), app(Term::Def(args_ty), [v(0)])),
    );
    // A function of `n` numbers, recursively: `f 0 = 0` and
    // `f (m + 1) = λ_. f m` (so `f` is a definition the body may refer to).
    let f_body = lam(
        "n",
        case(
            0,
            p.nat,
            vec![
                (vec![], p.num(0)),
                (vec!["m"], lam("x", app(Term::Def(f), [v(1)]))),
            ],
        ),
    );
    stitchwort_core::check::define_def(&mut p.g, f, &f_body).expect("f");
    let (_, bool_ty, _) = with_bool(&mut p);
    let n: usize = 1_000;
    let term = app(
        Term::Def(f),
        std::iter::once(Term::Nat(Rc::new(n.into()))).chain((0..n).map(|_| p.num(0))),
    );
    assert_eq!(
        define(&mut p.g, "bad", bool_ty, term),
        Err("E-TYPE-MISMATCH")
    );
}
