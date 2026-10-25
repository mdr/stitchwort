//! The pretty-printer, used in error messages and the REPL.

mod common;

use std::rc::Rc;

use common::*;
use stitchwort_core::registry;
use stitchwort_core::{Icit, Sort, Term, pretty};

fn show(p: &Prelude, names: &[&str], term: &Term) -> String {
    let names: Vec<_> = names.iter().map(|n| (*n).into()).collect();
    pretty::term(&p.g, &names, term)
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
    // Not a literal when the end isn't a constructor.
    let open = Term::ctor(p.list, 1, vec![p.num(1), v(0)]);
    assert_eq!(show(&p, &["xs"], &open), "Cons 1 xs");
    let succ_of_var = Term::ctor(p.nat, 1, vec![v(0)]);
    assert_eq!(show(&p, &["n"], &succ_of_var), "Succ n");
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
        format!("[x{last}: Type] -> x{last}")
    } else {
        format!("(x{last}: Type) -> x{last}")
    };
    for i in (0..last).rev() {
        text = if implicit {
            format!("[x{i}: {text}] -> x{i}")
        } else {
            format!("(x{i}: {text}) -> x{i}")
        };
    }
    text
}

#[test]
fn prints_function_types_with_the_right_binders_and_brackets() {
    let p = Prelude::new();
    let nat = p.nat_ty();
    assert_eq!(
        show(&p, &[], &arrow(nat.clone(), nat.clone())),
        "Nat -> Nat"
    );
    assert_eq!(
        show(
            &p,
            &[],
            &arrow(arrow(nat.clone(), nat.clone()), nat.clone())
        ),
        "(Nat -> Nat) -> Nat"
    );
    assert_eq!(show(&p, &[], &pi("a", ty(), v(0))), "(a: Type) -> a");
    assert_eq!(
        show(&p, &[], &ipi("a", ty(), arrow(v(0), v(0)))),
        "[a: Type] -> a -> a"
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
        "(Nat -> Nat) -> Nat"
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
