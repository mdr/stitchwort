//! The pretty-printer, used in error messages and the REPL.

use std::rc::Rc;

use crate::common::*;
use stitchwort_core::registry;
use stitchwort_core::{Icit, Sort, Term, pretty};

fn show(p: &Prelude, names: &[&str], term: &Term) -> String {
    let names: Vec<_> = names.iter().map(|n| (*n).into()).collect();
    pretty::term(&p.g.ev(), &names, term)
}

#[test]
fn prints_numbers_and_lists_as_literals() {
    let p = Prelude::new();
    assert_eq!(show(&p, &[], &p.num(3)), "3");
    let list = |items: Vec<Term>| {
        items
            .into_iter()
            .rev()
            .fold(Term::Ctor(p.list, 0, vec![]), |tail, head| {
                Term::ctor(p.list, 1, vec![head, tail])
            })
    };
    assert_eq!(show(&p, &[], &list(vec![p.num(1), p.num(2)])), "[1, 2]");
    assert_eq!(show(&p, &[], &list(vec![])), "[]");
    // An open chain, when the end isn't a constructor, prints with a spread.
    let open = Term::ctor(p.list, 1, vec![p.num(1), v(0)]);
    assert_eq!(show(&p, &["xs"], &open), "[1, ..xs]");
    let succ_of_var = Term::ctor(p.nat, 1, vec![v(0)]);
    assert_eq!(show(&p, &["n"], &succ_of_var), "Succ n");
}

#[test]
fn prints_unapplied_constructors_as_their_names() {
    let p = Prelude::new();
    assert_eq!(show(&p, &[], &Term::Ctor(p.nat, 1, vec![])), "Succ");
    assert_eq!(show(&p, &[], &Term::Ctor(p.list, 1, vec![])), "Cons");
}

#[test]
fn prints_other_data_types_by_constructor_name() {
    let mut p = Prelude::new();
    let tree = data(&mut p.g, "Tree", vec![], Sort::Type(0));
    stitchwort_core::check::define_ctors(
        &mut p.g,
        tree,
        vec![
            ctor("Leaf", vec![]),
            ctor(
                "Node",
                vec![
                    ("left", Term::Data(tree, vec![])),
                    ("right", Term::Data(tree, vec![])),
                ],
            ),
        ],
    )
    .expect("Tree");
    let leaf = || Term::Ctor(tree, 0, vec![]);
    assert_eq!(show(&p, &[], &leaf()), "Leaf");
    assert_eq!(
        show(&p, &[], &Term::ctor(tree, 1, vec![leaf(), leaf()])),
        "Node Leaf Leaf"
    );
}

fn nested_dependent_pis(depth: usize, implicit: bool) -> Term {
    let last = depth - 1;
    let mut term = if implicit {
        ipi(&format!("x{last}"), ty(), v(0))
    } else {
        pi(&format!("x{last}"), ty(), v(0))
    };
    for i in (0..last).rev() {
        term = if implicit {
            ipi(&format!("x{i}"), term, v(0))
        } else {
            pi(&format!("x{i}"), term, v(0))
        };
    }
    term
}

fn nested_dependent_pis_text(depth: usize, implicit: bool) -> String {
    let last = depth - 1;
    let mut text = if implicit {
        format!("[x{last}: Type] → x{last}")
    } else {
        format!("(x{last}: Type) → x{last}")
    };
    for i in (0..last).rev() {
        text = if implicit {
            format!("[x{i}: {text}] → x{i}")
        } else {
            format!("(x{i}: {text}) → x{i}")
        };
    }
    text
}

#[test]
fn prints_function_types_with_the_right_binders_and_brackets() {
    let p = Prelude::new();
    let nat = p.nat_ty();
    assert_eq!(show(&p, &[], &arrow(nat.clone(), nat.clone())), "Nat → Nat");
    assert_eq!(
        show(
            &p,
            &[],
            &arrow(arrow(nat.clone(), nat.clone()), nat.clone())
        ),
        "(Nat → Nat) → Nat"
    );
    assert_eq!(show(&p, &[], &pi("a", ty(), v(0))), "(a: Type) → a");
    assert_eq!(
        show(&p, &[], &ipi("a", ty(), arrow(v(0), v(0)))),
        "[a: Type] → a → a"
    );
    assert_eq!(show(&p, &[], &ty_n(1)), "Type 1");
    assert_eq!(show(&p, &[], &prop()), "Prop");
}

#[test]
fn prints_addition_and_equations_with_the_right_brackets() {
    let p = Prelude::new();
    let (x, y) = (v(1), v(0));
    let names = ["x", "y"];
    assert_eq!(show(&p, &names, &p.plus(x.clone(), y.clone())), "x + y");
    assert_eq!(
        show(&p, &names, &p.plus(p.plus(x.clone(), y.clone()), y.clone())),
        "x + y + y"
    );
    assert_eq!(
        show(&p, &names, &p.plus(x.clone(), p.plus(y.clone(), y.clone()))),
        "x + (y + y)"
    );
    assert_eq!(
        show(
            &p,
            &names,
            &eq(None, p.plus(x.clone(), p.num(0)), x.clone())
        ),
        "x + 0 = x"
    );
    // A partially applied `add` is an ordinary application.
    assert_eq!(show(&p, &names, &app(Term::Def(p.add), [x])), "Nat.add x");
}

#[test]
fn hides_implicit_arguments() {
    let p = Prelude::new();
    let call = Term::App(
        Rc::new(Term::App(
            Rc::new(Term::Def(p.add)),
            Rc::new(p.nat_ty()),
            Icit::Implicit,
        )),
        Rc::new(p.num(1)),
        Icit::Explicit,
    );
    assert_eq!(show(&p, &[], &call), "Nat.add 1");
    assert_eq!(show(&p, &[], &Term::Meta(4)), "?4");
}

#[test]
fn prints_negations_the_way_they_are_written() {
    let mut p = Prelude::new();
    let void = data(&mut p.g, "Void", vec![], Sort::Prop);
    stitchwort_core::check::define_ctors(&mut p.g, void, vec![]).expect("Void");
    registry::bind_data(&mut p.g, void);
    let not_equal = arrow(eq(None, v(0), p.num(0)), Term::Data(void, vec![]));
    assert_eq!(show(&p, &["d"], &not_equal), "d ≠ 0");
    let not_prop = arrow(prop(), Term::Data(void, vec![]));
    assert_eq!(show(&p, &[], &not_prop), "¬Prop");
}

#[test]
fn prints_the_prelude_operators_infix() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let binary = |p: &mut Prelude, name: &str| {
        let ty = arrow(nat.clone(), arrow(nat.clone(), nat.clone()));
        let id = define(&mut p.g, name, ty, lam("x", lam("y", v(1)))).unwrap();
        registry::bind_def(&mut p.g, id);
        id
    };
    let sub = binary(&mut p, "Nat.sub");
    let less = binary(&mut p, "Nat.LessThan");
    let less_eq = binary(&mut p, "Nat.LessEq");
    let names = ["x", "y"];
    assert_eq!(
        show(&p, &names, &app(Term::Def(sub), [v(1), v(0)])),
        "x - y"
    );
    assert_eq!(
        show(&p, &names, &app(Term::Def(less), [v(1), v(0)])),
        "x < y"
    );
    assert_eq!(
        show(&p, &names, &app(Term::Def(less_eq), [v(1), v(0)])),
        "x ≤ y"
    );
    // Subtraction associates to the left, like addition.
    let nested = app(Term::Def(sub), [app(Term::Def(sub), [v(1), v(0)]), v(0)]);
    assert_eq!(show(&p, &names, &nested), "x - y - y");
}

#[test]
fn prints_float_operators_infix() {
    let mut p = Prelude::new();
    let float = data(&mut p.g, "Float", vec![], Sort::Type(0));
    stitchwort_core::check::define_ctors(&mut p.g, float, vec![]).expect("Float");
    registry::bind_data(&mut p.g, float);
    let float_ty = Term::Data(float, vec![]);
    let ty = arrow(float_ty.clone(), arrow(float_ty.clone(), float_ty.clone()));
    let names = ["x", "y"];
    for (name, op) in [
        ("Float.add", "+"),
        ("Float.sub", "-"),
        ("Float.mul", "*"),
        ("Float.div", "/"),
        ("Float.rem", "%"),
    ] {
        let id = define(&mut p.g, name, ty.clone(), lam("x", lam("y", v(1)))).unwrap();
        registry::bind_def(&mut p.g, id);
        assert_eq!(
            show(&p, &names, &app(Term::Def(id), [v(1), v(0)])),
            format!("x {op} y")
        );
    }
}

/// Declares an `Int` (`OfNat n | NegSucc n`), bound as the prelude's if `bind`.
fn int_type(p: &mut Prelude, bind: bool) -> stitchwort_core::DataId {
    let nat = p.nat_ty();
    let int = data(&mut p.g, "Int", vec![], Sort::Type(0));
    stitchwort_core::check::define_ctors(
        &mut p.g,
        int,
        vec![
            ctor("OfNat", vec![("n", nat.clone())]),
            ctor("NegSucc", vec![("n", nat.clone())]),
        ],
    )
    .expect("Int");
    if bind {
        registry::bind_data(&mut p.g, int);
    }
    int
}

#[test]
fn prints_integers_as_signed_literals() {
    let mut p = Prelude::new();
    let int = int_type(&mut p, true);
    let neg_succ = |n: Term| Term::ctor(int, 1, vec![n]);
    assert_eq!(show(&p, &[], &Term::ctor(int, 0, vec![p.num(0)])), "0");
    assert_eq!(show(&p, &[], &Term::ctor(int, 0, vec![p.num(5)])), "5");
    assert_eq!(show(&p, &[], &neg_succ(p.num(0))), "-1");
    assert_eq!(show(&p, &[], &neg_succ(p.num(4))), "-5");
    // -(2^70) is `NegSucc (2^70 - 1)`, with the number as a big literal.
    let big = (stitchwort_core::BigUint::from(1u8) << 70) - 1u8;
    assert_eq!(
        show(&p, &[], &neg_succ(Term::Nat(Rc::new(big)))),
        "-1180591620717411303424"
    );
    // Not a literal when the number isn't closed.
    assert_eq!(show(&p, &["n"], &neg_succ(v(0))), "NegSucc n");
}

#[test]
fn brackets_a_negative_where_an_argument_needs_it() {
    let mut p = Prelude::new();
    let int = int_type(&mut p, true);
    let maybe = data(&mut p.g, "Option", vec![("a", ty())], Sort::Type(0));
    stitchwort_core::check::define_ctors(
        &mut p.g,
        maybe,
        vec![ctor("None", vec![]), ctor("Some", vec![("value", v(0))])],
    )
    .expect("Option");
    let neg = Term::ctor(int, 1, vec![p.num(4)]);
    let pos = Term::ctor(int, 0, vec![p.num(5)]);
    assert_eq!(
        show(&p, &[], &Term::ctor(maybe, 1, vec![neg.clone()])),
        "Some (-5)"
    );
    assert_eq!(show(&p, &[], &Term::ctor(maybe, 1, vec![pos])), "Some 5");
    // Looser than application, tighter than `+`'s right operand.
    let sum = p.plus(neg.clone(), neg);
    assert_eq!(show(&p, &[], &sum), "-5 + (-5)");
}

#[test]
fn a_users_own_int_prints_as_written() {
    let mut p = Prelude::new();
    let _prelude_int = int_type(&mut p, true);
    let mine = int_type(&mut p, false);
    assert_eq!(
        show(&p, &[], &Term::ctor(mine, 0, vec![p.num(5)])),
        "OfNat 5"
    );
    assert_eq!(
        show(&p, &[], &Term::ctor(mine, 1, vec![p.num(4)])),
        "NegSucc 4"
    );
}

#[test]
fn prints_deeply_nested_dependent_domains_without_exponential_work() {
    let p = Prelude::new();
    assert_eq!(
        show(&p, &[], &nested_dependent_pis(3, false)),
        nested_dependent_pis_text(3, false)
    );
    assert_eq!(
        show(&p, &[], &nested_dependent_pis(40, false)),
        nested_dependent_pis_text(40, false)
    );
}

#[test]
fn prints_deeply_nested_implicit_domains_without_exponential_work() {
    let p = Prelude::new();
    assert_eq!(
        show(&p, &[], &nested_dependent_pis(3, true)),
        nested_dependent_pis_text(3, true)
    );
    assert_eq!(
        show(&p, &[], &nested_dependent_pis(40, true)),
        nested_dependent_pis_text(40, true)
    );
}

#[test]
fn brackets_a_function_domain_of_a_nondependent_arrow() {
    let p = Prelude::new();
    let nat = p.nat_ty();
    assert_eq!(
        show(&p, &[], &arrow(arrow(nat.clone(), nat.clone()), nat)),
        "(Nat → Nat) → Nat"
    );
}

/// docs/proposals/lambda-syntax.md §4.3: implicit and auto parameters are
/// printed as such, with their types left out (a lambda doesn't keep them).
#[test]
fn prints_implicit_and_auto_lambda_parameters() {
    let p = Prelude::new();
    let lam = |x: &str, icit, body| Term::Lam(x.into(), icit, Rc::new(body));
    let id = lam("a", Icit::Implicit, lam("x", Icit::Explicit, v(0)));
    assert_eq!(show(&p, &[], &id), "[a: _] x => x");
    let with_auto = lam(
        "a",
        Icit::Implicit,
        lam("h", Icit::Auto, lam("x", Icit::Explicit, v(0))),
    );
    assert_eq!(show(&p, &[], &with_auto), "[a: _] [auto h: _] x => x");
    // Explicit ones are unchanged.
    let k = lam("x", Icit::Explicit, lam("y", Icit::Explicit, v(1)));
    assert_eq!(show(&p, &[], &k), "x y => x");
}

/// SW-1000: a binder whose name is a variable its body mentions is
/// renamed, so that the variable isn't captured: `List.Mem y ys` unfolds to
/// `List.Any (y => y = y) ys`, which read as if every item equalled itself.
#[test]
fn a_binder_never_captures_a_variable_its_body_mentions() {
    let p = Prelude::new();
    // `y => y = <outer y>`, with the outer variable also called `y`.
    let pred = lam("y", eq(None, v(0), v(1)));
    assert_eq!(show(&p, &["y"], &pred), "y1 => y1 = y");
    // Not renamed when the body doesn't mention the outer one.
    let own = lam("y", eq(None, v(0), v(0)));
    assert_eq!(show(&p, &["y"], &own), "y => y = y");
    // Fresh against every name in scope, not only the one captured.
    assert_eq!(show(&p, &["y1", "y"], &pred), "y2 => y2 = y");
    // A run of lambdas: the inner one would capture the outer one.
    let run = lam("x", lam("x", eq(None, v(0), v(1))));
    assert_eq!(show(&p, &[], &run), "x x1 => x1 = x");
    // A dependent function type and a `let` alike.
    let dependent = pi("n", ty(), eq(None, v(0), v(1)));
    assert_eq!(show(&p, &["n"], &dependent), "∀ (n1: Type) => n1 = n");
    let let_ = Term::let_("c".into(), p.nat_ty(), p.num(1), eq(None, v(0), v(1)));
    assert_eq!(show(&p, &["c"], &let_), "let c1 := 1; c1 = c");
}

/// A function type whose result is evidently a proposition, binding a
/// variable the result uses, prints as `∀` (D3458): one `∀` for the run, a
/// group for neighbours of the same kind and type, and an unused binder left
/// as an implication. One into data, or into a variable's call, stays an
/// arrow.
#[test]
fn a_function_type_into_a_proposition_prints_as_forall() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let small = declare(&mut p.g, "Small", arrow(nat.clone(), prop()));
    let even = data(&mut p.g, "Even", vec![("n", nat.clone())], Sort::Prop);
    // `(a b: Nat) → [c: Nat] → a = c → b = c`.
    let run = pi(
        "a",
        nat.clone(),
        pi(
            "b",
            nat.clone(),
            ipi(
                "c",
                nat.clone(),
                arrow(eq(None, v(2), v(0)), eq(None, v(1), v(0))),
            ),
        ),
    );
    assert_eq!(
        show(&p, &[], &run),
        "∀ (a b: Nat) [c: Nat] => a = c → b = c"
    );
    let ascii = pretty::term_ascii(&p.g.ev(), &[], &run);
    assert_eq!(ascii, "forall (a b: Nat) [c: Nat] => a = c -> b = c");
    // A type that mentions the name before it starts a new group.
    let typed = pi("a", ty(), pi("x", v(0), eq(None, v(0), v(0))));
    assert_eq!(show(&p, &[], &typed), "∀ (a: Type) (x: a) => x = x");
    // A definition whose type ends in `Prop`, and a data type in `Prop`.
    let call = pi("n", nat.clone(), app(Term::Def(small), [v(0)]));
    assert_eq!(show(&p, &[], &call), "∀ (n: Nat) => Small n");
    let held = pi("n", nat.clone(), Term::Data(even, vec![v(0).into()]));
    assert_eq!(show(&p, &[], &held), "∀ (n: Nat) => Even n");
    // Under a non-dependent binder, the `∀` is the arrow's result.
    let implied = arrow(prop(), pi("n", nat.clone(), eq(None, v(0), v(0))));
    assert_eq!(show(&p, &[], &implied), "Prop → ∀ (n: Nat) => n = n");
    // As an argument or an arrow's domain, it's bracketed.
    let domain = arrow(pi("n", nat.clone(), eq(None, v(0), v(0))), prop());
    assert_eq!(show(&p, &[], &domain), "(∀ (n: Nat) => n = n) → Prop");
    // A variable's call isn't evidently a proposition, nor is data.
    let variable = pi("n", nat.clone(), app(v(1), [v(0)]));
    assert_eq!(show(&p, &["p"], &variable), "(n: Nat) → p n");
    assert_eq!(show(&p, &[], &pi("a", ty(), v(0))), "(a: Type) → a");
}

fn difference(p: &Prelude, names: &[&str], a: &Term, b: &Term) -> Option<pretty::Difference> {
    let names: Vec<_> = names.iter().map(|n| (*n).into()).collect();
    pretty::first_difference(&p.g.ev(), &names, a, b)
}

/// `f`, a function of two numbers that nothing unfolds.
fn opaque_function(p: &mut Prelude) -> Term {
    let nat = p.nat_ty();
    Term::Def(declare(
        &mut p.g,
        "f",
        arrow(nat.clone(), arrow(nat.clone(), nat)),
    ))
}

#[test]
fn finds_where_two_terms_first_differ() {
    let mut p = Prelude::new();
    let f = opaque_function(&mut p);
    let (x, y) = (v(1), v(0));
    let side = |last: Term| {
        p.plus(
            app(f.clone(), [p.plus(x.clone(), p.num(1)), last]),
            y.clone(),
        )
    };
    let a = side(p.plus(x.clone(), p.num(2)));
    let b = side(p.plus(p.num(2), x.clone()));
    // A variable against a number is shown with the `+` around each, and
    // the call they're in.
    assert_eq!(
        difference(&p, &["x", "y"], &a, &b),
        Some(pretty::Difference {
            left: "x + 2".into(),
            right: "2 + x".into(),
            within: Some("f (x + 1) (x + 2)".into()),
        })
    );
    // Under a binder, by the binder's name.
    let a = lam("z", p.plus(v(0), app(f.clone(), [v(0), p.num(1)])));
    let b = lam("z", p.plus(v(0), app(f.clone(), [v(0), v(1)])));
    let found = difference(&p, &["x", "y"], &a, &b).expect("a difference");
    assert_eq!(
        (found.left.as_str(), found.right.as_str()),
        ("f z 1", "f z y")
    );
    assert_eq!(found.within, None);
}

#[test]
fn a_succ_in_a_comparisons_operand_is_reported_as_the_whole_comparisons() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let ty = arrow(nat.clone(), arrow(nat.clone(), nat.clone()));
    let leq = define(&mut p.g, "Nat.leq", ty, lam("x", lam("y", v(1)))).expect("Nat.leq");
    registry::bind_def(&mut p.g, leq);
    let call = |a: Term, b: Term| app(Term::Def(leq), [a, b]);
    // `x + y < y` against `x + y <= y` differ only in the `Succ` that the
    // printed comparisons hide, so the note gives the comparisons whole.
    let plain = p.plus(v(1), v(0));
    let less = call(Term::ctor(p.nat, 1, vec![plain.clone()]), v(0));
    let less_eq = call(plain, v(0));
    // Under an outer `=`, so the comparisons aren't the whole terms compared.
    let a = eq(None, less, v(0));
    let b = eq(None, less_eq, v(0));
    assert_eq!(
        difference(&p, &["x", "y"], &a, &b),
        Some(pretty::Difference {
            left: "x + y < y".into(),
            right: "x + y <= y".into(),
            within: None,
        })
    );
}

#[test]
fn reports_no_difference_where_the_terms_differ_at_the_top_or_not_at_all() {
    let mut p = Prelude::new();
    let f = opaque_function(&mut p);
    let call = |a: Term| app(f.clone(), [a, p.num(0)]);
    // Different heads: what any printing shows.
    assert_eq!(
        difference(&p, &["x"], &call(v(0)), &p.plus(v(0), p.num(0))),
        None
    );
    // A number and the `Succ`s it stands for are alike.
    let three = Term::Nat(Rc::new(3u32.into()));
    assert_eq!(difference(&p, &["x"], &call(three), &call(p.num(3))), None);
}

#[test]
fn tells_apart_terms_that_differ_only_in_implicit_arguments() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let g = Term::Def(declare(
        &mut p.g,
        "g",
        ipi("n", nat.clone(), arrow(nat.clone(), nat)),
    ));
    let call = |hidden: Term, shown: Term| {
        Term::App(
            Rc::new(Term::App(
                Rc::new(g.clone()),
                Rc::new(hidden),
                Icit::Implicit,
            )),
            Rc::new(shown),
            Icit::Explicit,
        )
    };
    let only_hidden = |a: &Term, b: &Term| pretty::differ_only_in_hidden(&p.g.ev(), a, b);
    assert!(only_hidden(&call(p.num(1), v(0)), &call(p.num(2), v(0))));
    // Also differing in an explicit argument.
    assert!(!only_hidden(
        &call(p.num(1), v(0)),
        &call(p.num(2), p.num(0))
    ));
    // Not differing at all.
    assert!(!only_hidden(&call(p.num(1), v(0)), &call(p.num(1), v(0))));
    // The explicit difference is found past the implicit one.
    let a = p.plus(call(p.num(1), v(0)), v(0));
    let b = p.plus(call(p.num(2), p.plus(v(0), p.num(1))), v(0));
    let found = difference(&p, &["x"], &a, &b).expect("a difference");
    assert_eq!((found.left.as_str(), found.right.as_str()), ("x", "x + 1"));
}

/// A call of `Tree.size` shows as a dot call when the receiver can be
/// written before a dot, and as a plain call when a bare global name would
/// read as a path (`Tip.size`, SW-1696).
#[test]
fn dot_calls_keep_the_call_form_for_a_bare_global_receiver() {
    let mut p = Prelude::new();
    let tree = data(&mut p.g, "Tree", vec![], Sort::Type(0));
    stitchwort_core::check::define_ctors(
        &mut p.g,
        tree,
        vec![
            ctor("Tip", vec![]),
            ctor(
                "Bin",
                vec![
                    ("left", Term::Data(tree, vec![])),
                    ("right", Term::Data(tree, vec![])),
                ],
            ),
        ],
    )
    .expect("Tree");
    let tree_ty = Term::Data(tree, vec![]);
    let size = define(
        &mut p.g,
        "Tree.size",
        arrow(tree_ty.clone(), tree_ty.clone()),
        lam("t", v(0)),
    )
    .unwrap();
    let origin = define(
        &mut p.g,
        "origin",
        tree_ty.clone(),
        Term::Ctor(tree, 0, vec![]),
    )
    .unwrap();
    let call = |receiver: Term| app(Term::Def(size), [receiver]);
    let tip = || Term::Ctor(tree, 0, vec![]);

    // A bare constructor: `Tip.size` would be a name path.
    assert_eq!(show(&p, &[], &call(tip())), "Tree.size Tip");
    // A bare constant, likewise.
    assert_eq!(show(&p, &[], &call(Term::Def(origin))), "Tree.size origin");
    // A constructor with arguments is bracketed, so it reads as a call.
    let bin = Term::ctor(tree, 1, vec![tip(), tip()]);
    assert_eq!(show(&p, &[], &call(bin)), "(Bin Tip Tip).size");
    // A local variable is a fine receiver.
    assert_eq!(show(&p, &["t"], &call(v(0))), "t.size");
}

/// A receiver that can't go before a dot (`x✝`) keeps the call form at
/// every level of a chain of calls, and is printed once per level: the
/// dot form's test of it isn't repeated by the plain call (SW-1708, where
/// printing a goal after `cases` took minutes).
#[test]
fn a_chain_of_calls_on_an_anonymous_receiver_prints_without_exponential_work() {
    let mut p = Prelude::new();
    let tree = data(&mut p.g, "Tree", vec![], Sort::Type(0));
    stitchwort_core::check::define_ctors(&mut p.g, tree, vec![ctor("Tip", vec![])]).expect("Tree");
    let tree_ty = Term::Data(tree, vec![]);
    let size = define(
        &mut p.g,
        "Tree.size",
        arrow(tree_ty.clone(), tree_ty.clone()),
        lam("t", v(0)),
    )
    .unwrap();
    let chain =
        |depth: usize| (0..depth).fold(v(0), |receiver, _| app(Term::Def(size), [receiver]));
    let text = |depth: usize| {
        (0..depth).fold("x✝".to_string(), |receiver, i| match i {
            0 => format!("Tree.size {receiver}"),
            _ => format!("Tree.size ({receiver})"),
        })
    };
    assert_eq!(
        show(&p, &["x✝"], &chain(3)),
        "Tree.size (Tree.size (Tree.size x✝))"
    );
    assert_eq!(show(&p, &["x✝"], &chain(40)), text(40));
}

/// A term of many nested nodes (the closed list of 130,000 sequences of
/// AoC 2024 day 22, SW-2591) is cut off without printing it whole: the
/// full print, built from the inside out, took a goal's search over an hour.
#[test]
fn a_huge_nested_term_is_cut_off_without_printing_it_whole() {
    std::thread::Builder::new()
        .stack_size(1024 * 1024 * 1024)
        .spawn(|| {
            let mut p = Prelude::new();
            let tree = data(&mut p.g, "Tree", vec![], Sort::Type(0));
            stitchwort_core::check::define_ctors(
                &mut p.g,
                tree,
                vec![
                    ctor("Leaf", vec![]),
                    ctor(
                        "Node",
                        vec![
                            ("left", Term::Data(tree, vec![])),
                            ("right", Term::Data(tree, vec![])),
                        ],
                    ),
                ],
            )
            .expect("Tree");
            let leaf = || Term::Ctor(tree, 0, vec![]);
            let nested =
                (0..300_000).fold(leaf(), |inner, _| Term::ctor(tree, 1, vec![inner, leaf()]));
            let started = std::time::Instant::now();
            let text = pretty::term_for_message(&p.g.ev(), &[], &nested);
            assert!(text.chars().count() <= 400, "{} characters", text.len());
            assert!(text.starts_with("Node"), "{text}");
            assert!(
                started.elapsed() < std::time::Duration::from_secs(10),
                "took {:?}",
                started.elapsed()
            );
            std::mem::forget(nested);
        })
        .expect("spawn")
        .join()
        .expect("the thread ran");
}

/// A deep term through the forms the printer recurses on most, an operator
/// and an application, prints in full: `x + f (x + f (… y))`, 300 deep
/// (SW-3133, where each form went into a method of its own).
#[test]
fn prints_a_deep_chain_of_operators_and_applications() {
    let p = Prelude::new();
    let names = ["x", "f", "y"];
    let depth = 300;
    let term = (0..depth).fold(v(0), |t, _| p.plus(v(2), app(v(1), [t])));
    let text = (0..depth).fold("y".to_string(), |s, k| {
        if k == 0 {
            format!("x + f {s}")
        } else {
            format!("x + f ({s})")
        }
    });
    assert_eq!(show(&p, &names, &term), text);
}
