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
    assert_eq!(show(&p, &[], &pi("a", ty(), v(0))), "(a : Type) -> a");
    assert_eq!(
        show(&p, &[], &ipi("a", ty(), arrow(v(0), v(0)))),
        "[a : Type] -> a -> a"
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
    assert_eq!(show(&p, &names, &app(Term::Def(p.add), [x])), "add x");
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
    assert_eq!(show(&p, &[], &call), "add 1");
    assert_eq!(show(&p, &[], &Term::Meta(4)), "?4");
}

#[test]
fn prints_negations_the_way_they_are_written() {
    let mut p = Prelude::new();
    let void = data(&mut p.g, "Void", vec![], Sort::Prop);
    stitchwort_core::check::define_ctors(&mut p.g, void, vec![]).expect("Void");
    registry::bind_data(&mut p.g, void);
    let not_equal = arrow(eq(None, v(0), p.num(0)), Term::Data(void, vec![]));
    assert_eq!(show(&p, &["d"], &not_equal), "d != 0");
    let not_prop = arrow(prop(), Term::Data(void, vec![]));
    assert_eq!(show(&p, &[], &not_prop), "Not Prop");
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
    let sub = binary(&mut p, "sub");
    let less = binary(&mut p, "LessThan");
    let less_eq = binary(&mut p, "LessEq");
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
        "x <= y"
    );
    // Subtraction associates to the left, like addition.
    let nested = app(Term::Def(sub), [app(Term::Def(sub), [v(1), v(0)]), v(0)]);
    assert_eq!(show(&p, &names, &nested), "x - y - y");
}
