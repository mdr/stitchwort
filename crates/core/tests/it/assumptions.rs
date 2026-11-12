//! Open goals' assumptions in the kernel (docs/core.md "Assumptions (open
//! goals)"; docs/proposals/using-unfinished-proofs.md, option A, stage 1):
//! `check::assume` adds a constant with a type and no body, final at once;
//! it never unfolds, conversion treats it as a neutral head, index
//! unification is stuck on it, nothing can give it a body afterwards, the
//! reliance walk finds it through any chain of users, and its label and type
//! are part of every user's hash. Terms are built by hand: the elaborator
//! makes `?` into assumptions in stage 2.

use std::rc::Rc;

use crate::common::*;
use stitchwort_core::assumption::{Decl, relied_on, relied_on_skipping, relies_on};
use stitchwort_core::check;
use stitchwort_core::globals::{Assumption, State};
use stitchwort_core::hash::{ContentHash, def_hash};
use stitchwort_core::native::{self, Native};
use stitchwort_core::term::Term;
use stitchwort_core::value::{Head, Value, eval};
use stitchwort_core::{DefId, Icit, Kernel, Limits, Sort};

fn label(owner: &str, hole: u32) -> Assumption {
    Assumption::goal(owner.into(), hole)
}

/// Assumes `name: ty` for hole `hole` of `owner`, or the error code.
fn assume_as(
    g: &mut Kernel,
    name: &str,
    ty: Term,
    owner: &str,
    hole: u32,
) -> Result<DefId, &'static str> {
    check::assume(
        g,
        &name.into(),
        &name.into(),
        &ty,
        label(owner, hole),
        false,
        span(),
    )
    .map_err(|d| d.code)
}

/// `(n m: Nat) -> n + m = m + n`.
fn comm(p: &Prelude) -> Term {
    let nat = p.nat_ty();
    pi(
        "n",
        nat.clone(),
        pi(
            "m",
            nat.clone(),
            eq(Some(nat), p.plus(v(1), v(0)), p.plus(v(0), v(1))),
        ),
    )
}

/// `addComm.?1: (n m: Nat) -> n + m = m + n`, the goal of `addComm := ?`.
fn add_comm_goal(p: &mut Prelude) -> DefId {
    let ty = comm(p);
    assume_as(&mut p.g, "addComm.?1", ty, "Main.addComm", 1).expect("a type")
}

fn theorem(g: &mut Kernel, name: &str, ty: Term, body: Term) -> Result<DefId, &'static str> {
    let id = check::declare_def(g, &name.into(), &name.into(), &ty, true, false, span())
        .map_err(|d| d.code)?;
    check::define_def(g, id, &body).map_err(|d| d.code)?;
    Ok(id)
}

fn hash_of(g: &Kernel, id: DefId) -> ContentHash {
    let _op = g.machine.budget.operation(Limits::default());
    def_hash(&g.ev(), id).unwrap().expect("final")
}

fn relies(g: &Kernel, root: impl Into<Decl>) -> Vec<DefId> {
    relied_on(&g.ev(), &[root.into()]).into_iter().collect()
}

// The form

#[test]
fn an_assumption_is_final_with_no_body() {
    let mut p = Prelude::new();
    let goal = add_comm_goal(&mut p);
    let def = p.g.def(goal);
    assert_eq!(def.state(), State::Final);
    assert!(def.body().is_none() && def.run_body().is_none());
    assert_eq!(def.arity(), 0);
    assert!(!def.theorem() && !def.opaque() && !def.export());
    assert_eq!(def.assumption(), Some(&label("Main.addComm", 1)));
}

#[test]
fn users_are_checked_against_it() {
    // theorem rearrange: 1 + 2 = 2 + 1 := addComm.?1 1 2
    let mut p = Prelude::new();
    let goal = add_comm_goal(&mut p);
    let nat = p.nat_ty();
    let (one, two) = (p.num(1), p.num(2));
    let statement = eq(
        Some(nat.clone()),
        p.plus(one.clone(), two.clone()),
        p.plus(two.clone(), one.clone()),
    );
    let proof = app(Term::Def(goal), [one.clone(), two.clone()]);
    assert!(theorem(&mut p.g, "rearrange", statement, proof.clone()).is_ok());
    // A user is still checked: the assumption proves its own statement
    // only, so `1 + 2 = 2 + 2` isn't proved by it.
    let wrong = eq(
        Some(nat),
        p.plus(one, two.clone()),
        p.plus(two.clone(), two),
    );
    assert_eq!(
        theorem(&mut p.g, "wrong", wrong, proof),
        Err("E-TYPE-MISMATCH")
    );
}

#[test]
fn a_value_assumption_never_unfolds() {
    // `half.?1: Nat`, the goal of a `?` in a `def`.
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let hole = assume_as(&mut p.g, "half.?1", nat.clone(), "Main.half", 1).unwrap();
    // It's a neutral head, whatever it's applied to or compared with.
    {
        let _op = p.g.machine.budget.operation(Limits::default());
        let value = eval(&p.g.ev(), &[], &Term::Def(hole)).unwrap();
        assert!(
            matches!(&value, Value::Neutral(Head::Def(id), spine) if *id == hole && spine.is_empty())
        );
    }
    let zero = p.num(0);
    let is = |p: &mut Prelude, name: &str, a: Term, b: Term| {
        let statement = eq(Some(p.nat_ty()), a, b);
        theorem(&mut p.g, name, statement, Term::Refl)
    };
    assert_eq!(
        is(&mut p, "a", Term::Def(hole), zero.clone()),
        Err("E-REFL")
    );
    // Paired: it equals itself, and `0 + h` computes to `h`.
    assert!(is(&mut p, "b", Term::Def(hole), Term::Def(hole)).is_ok());
    let sum = p.plus(zero, Term::Def(hole));
    assert!(is(&mut p, "c", sum, Term::Def(hole)).is_ok());
    // `h + 0` is stuck on it, as on a variable.
    let sum = p.plus(Term::Def(hole), p.num(0));
    assert_eq!(is(&mut p, "d", sum, Term::Def(hole)), Err("E-REFL"));
}

#[test]
fn two_holes_with_the_same_goal_are_different() {
    // As Lean's unique `sorry`s: `f.?1 = f.?2` isn't provable by `rfl`.
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let one = assume_as(&mut p.g, "f.?1", nat.clone(), "Main.f", 1).unwrap();
    let two = assume_as(&mut p.g, "f.?2", nat.clone(), "Main.f", 2).unwrap();
    let statement = eq(Some(nat.clone()), Term::Def(one), Term::Def(two));
    assert_eq!(
        theorem(&mut p.g, "same", statement, Term::Refl),
        Err("E-REFL")
    );
    // A function-typed one: compared by its arguments.
    let to_nat = arrow(nat.clone(), nat.clone());
    let g = assume_as(&mut p.g, "g.?1", to_nat, "Main.g", 1).unwrap();
    let call = |n| app(Term::Def(g), [n]);
    let statement = eq(Some(nat.clone()), call(p.num(0)), call(p.num(0)));
    assert!(theorem(&mut p.g, "g0", statement, Term::Refl).is_ok());
    let statement = eq(Some(nat), call(p.num(0)), call(p.num(1)));
    assert_eq!(
        theorem(&mut p.g, "g01", statement, Term::Refl),
        Err("E-REFL")
    );
}

#[test]
fn index_unification_is_stuck_on_one() {
    // type IsZero: Nat -> Type = | MkZ: IsZero 0. With `k: Nat` assumed, an
    // empty match on `IsZero k` needs `k = 0` to be a conflict, which it
    // mustn't be: `k`'s goal may be filled with `0`.
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let is_zero = family(
        &mut p.g,
        "IsZero",
        vec![],
        vec![("n", nat.clone())],
        Sort::Type(0),
    );
    let zero = p.num(0);
    check::define_ctors(&mut p.g, is_zero, vec![ictor("MkZ", vec![], vec![zero])]).unwrap();
    let k = assume_as(&mut p.g, "k.?1", nat.clone(), "Main.k", 1).unwrap();
    let empty = |p: &mut Prelude, name: &str, index: Term| {
        let ty = pi("x", Term::data(is_zero, vec![index]), p.nat_ty());
        let body = lam("x", icase(0, is_zero, vec![(vec![], None)]));
        define(&mut p.g, name, ty, body)
    };
    assert_eq!(empty(&mut p, "onK", Term::Def(k)), Err("E-INDEX-STUCK"));
    // Paired: on `1`, a conflict.
    let one = p.num(1);
    assert!(empty(&mut p, "onOne", one).is_ok());
}

// What's refused

#[test]
fn a_label_is_used_once() {
    // Two assumptions with one label would be two constants that
    // conversion tells apart and the hasher doesn't.
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    assume_as(&mut p.g, "f.?1", nat.clone(), "Main.f", 1).unwrap();
    let before = p.g.env.defs().len();
    assert_eq!(
        assume_as(&mut p.g, "again", nat, "Main.f", 1),
        Err("E-MALFORMED")
    );
    // With another type too: the label alone names the `?`.
    assert_eq!(
        assume_as(&mut p.g, "again", prop(), "Main.f", 1),
        Err("E-MALFORMED")
    );
    assert_eq!(p.g.env.defs().len(), before, "nothing is added");
    // Paired: another hole, or the same hole of another owner.
    assert!(assume_as(&mut p.g, "f.?2", prop(), "Main.f", 2).is_ok());
    assert!(assume_as(&mut p.g, "g.?1", prop(), "Main.g", 1).is_ok());
}

#[test]
fn its_type_must_be_a_type() {
    let mut p = Prelude::new();
    let before = p.g.env.defs().len();
    let zero = p.num(0);
    assert!(assume_as(&mut p.g, "x.?1", zero, "Main.x", 1).is_err());
    assert_eq!(p.g.env.defs().len(), before, "nothing is added");
    // Paired: any universe will do, `Prop` and `Type` included.
    assert!(assume_as(&mut p.g, "x.?1", prop(), "Main.x", 1).is_ok());
    assert!(assume_as(&mut p.g, "x.?2", ty(), "Main.x", 2).is_ok());
}

#[test]
fn its_type_may_mention_only_final_declarations() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    // Pending: the goal of a `?` that mentions its own group.
    let pending = declare(&mut p.g, "pending", nat.clone());
    let before = p.g.env.defs().len();
    let about = |id| eq(Some(nat.clone()), Term::Def(id), Term::Def(id));
    assert_eq!(
        assume_as(&mut p.g, "pending.?1", about(pending), "Main.pending", 1),
        Err("E-MALFORMED")
    );
    // Failed: there's no later step to find it, so it's refused at once.
    let failed = declare(&mut p.g, "failed", nat.clone());
    assert!(check::define_def(&mut p.g, failed, &ty()).is_err());
    let before_failed = p.g.env.defs().len();
    assert_eq!(
        assume_as(&mut p.g, "failed.?1", about(failed), "Main.failed", 1),
        Err("E-FAILED-DEPENDENCY")
    );
    assert_eq!(p.g.env.defs().len(), before_failed);
    // Unknown.
    assert_eq!(
        assume_as(&mut p.g, "u.?1", about(DefId(10_000)), "Main.u", 1),
        Err("E-MALFORMED")
    );
    assert_eq!(p.g.env.defs().len(), before + 1, "only `failed` was added");
    // Paired: a final one.
    let n2 = p.num(2);
    let two = define(&mut p.g, "two", nat.clone(), n2).unwrap();
    assert!(assume_as(&mut p.g, "two.?1", about(two), "Main.two", 1).is_ok());
}

#[test]
fn nothing_gives_it_a_body_later() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let hole = assume_as(&mut p.g, "h.?1", nat.clone(), "Main.h", 1).unwrap();
    let zero = p.num(0);
    // Not as a definition: it isn't pending.
    assert_eq!(
        check::define_def(&mut p.g, hole, &zero).map_err(|d| d.code),
        Err("E-MALFORMED")
    );
    // Not as a run body.
    assert_eq!(
        check::set_run_body(&mut p.g, hole, &zero).map_err(|d| d.code),
        Err("E-MALFORMED")
    );
    // Not as a native.
    assert!(native::register_native_unpinned(&mut p.g, hole, Native::Add).is_err());
    let float = stitchwort_core::float::register_def(
        &mut p.g,
        hole,
        stitchwort_core::registry::Builtin::FloatNeg,
    )
    .unwrap_err();
    assert!(float.labels[0].message.contains("open goal"));
    // Not a validator: `v.?1 : (n : Nat) -> [auto ok : n = n] -> Nat`. The
    // validator is ill-formed anyway (`Nat` isn't a decision), so the
    // refusal is told apart by its reason.
    let validated = Term::Pi(
        "n".into(),
        Icit::Explicit,
        Rc::new(nat.clone()),
        Rc::new(Term::Pi(
            "ok".into(),
            Icit::Auto,
            Rc::new(eq(None, v(0), v(0))),
            Rc::new(nat.clone()),
        )),
    );
    let validated = assume_as(&mut p.g, "v.?1", validated, "Main.v", 1).unwrap();
    let refused = check::add_validator(&mut p.g, validated, 1, p.nat, &zero).unwrap_err();
    assert_eq!(refused.code, "E-MALFORMED");
    assert!(refused.labels[0].message.contains("open goal"));
    // Marks for pending definitions don't apply.
    check::mark_opaque(&mut p.g, hole);
    check::mark_folded(&mut p.g, hole);
    let def = p.g.def(hole);
    assert!(!def.opaque() && !def.fold() && def.body().is_none());
    assert_eq!(def.state(), State::Final);
    // And no declaration can unfold it: it isn't an opaque definition.
    let statement = eq(Some(nat), Term::Def(hole), zero);
    let t = check::declare_def(
        &mut p.g,
        &"t".into(),
        &"t".into(),
        &statement,
        true,
        false,
        span(),
    )
    .unwrap();
    check::mark_opaque(&mut p.g, t);
    check::set_unfolding(&mut p.g, t, &[hole]);
    assert_eq!(
        check::define_def(&mut p.g, t, &Term::Refl).map_err(|d| d.code),
        Err("E-NOT-OPAQUE")
    );
}

// Reliance

#[test]
fn reliance_is_read_off_the_checked_terms() {
    let mut p = Prelude::new();
    let goal = add_comm_goal(&mut p);
    let nat = p.nat_ty();
    let (one, two) = (p.num(1), p.num(2));
    let statement = eq(
        Some(nat.clone()),
        p.plus(one.clone(), two.clone()),
        p.plus(two.clone(), one.clone()),
    );
    let proof = app(Term::Def(goal), [one, two]);
    let direct = theorem(&mut p.g, "direct", statement.clone(), proof).unwrap();
    // A user of a user, through its body.
    let chained = theorem(&mut p.g, "chained", statement.clone(), Term::Def(direct)).unwrap();
    // Not relying: proved by `rfl`.
    let by_rfl = theorem(&mut p.g, "byRfl", statement, Term::Refl).unwrap();

    assert_eq!(
        relies(&p.g, goal),
        vec![goal],
        "an assumption relies on itself"
    );
    assert_eq!(relies(&p.g, direct), vec![goal]);
    assert_eq!(relies(&p.g, chained), vec![goal]);
    assert_eq!(relies(&p.g, by_rfl), Vec::<DefId>::new());
    assert_eq!(
        relied_on(&p.g.ev(), &[by_rfl.into(), chained.into()])
            .into_iter()
            .collect::<Vec<_>>(),
        vec![goal]
    );
}

#[test]
fn a_skipped_declaration_is_not_walked() {
    let mut p = Prelude::new();
    let goal = add_comm_goal(&mut p);
    let nat = p.nat_ty();
    let (one, two) = (p.num(1), p.num(2));
    let statement = eq(
        Some(nat.clone()),
        p.plus(one.clone(), two.clone()),
        p.plus(two.clone(), one.clone()),
    );
    let direct = theorem(
        &mut p.g,
        "direct",
        statement.clone(),
        app(Term::Def(goal), [one, two]),
    )
    .unwrap();
    let chained = theorem(&mut p.g, "chained", statement, Term::Def(direct)).unwrap();
    let walk = |skip: &dyn Fn(Decl) -> bool| -> Vec<DefId> {
        relied_on_skipping(&p.g.ev(), &[chained.into()], skip)
            .into_iter()
            .collect()
    };
    assert_eq!(walk(&|_| false), vec![goal]);
    // The caller vouches for `direct`, so what it uses isn't looked at.
    assert_eq!(walk(&|d| d == Decl::Def(direct)), Vec::<DefId>::new());
    assert_eq!(walk(&|d| d == Decl::Def(goal)), Vec::<DefId>::new());
}

#[test]
fn reliance_through_a_type() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let k = assume_as(&mut p.g, "k.?1", nat.clone(), "Main.k", 1).unwrap();
    // `t: k.?1 = k.?1 := rfl` mentions it only in its statement.
    let statement = eq(Some(nat.clone()), Term::Def(k), Term::Def(k));
    let t = theorem(&mut p.g, "t", statement, Term::Refl).unwrap();
    assert_eq!(relies(&p.g, t), vec![k]);
    // type Witness = | MkWitness (h: k.?1 = k.?1), and `w: Witness -> Nat`:
    // `w` mentions only `Witness`, whose field mentions the assumption.
    let witness = data(&mut p.g, "Witness", vec![], Sort::Type(0));
    let field = eq(Some(nat.clone()), Term::Def(k), Term::Def(k));
    check::define_ctors(
        &mut p.g,
        witness,
        vec![ctor("MkWitness", vec![("h", field)])],
    )
    .unwrap();
    let body = lam("x", p.num(0));
    let w = define(&mut p.g, "w", arrow(Term::data(witness, vec![]), nat), body).unwrap();
    assert_eq!(relies(&p.g, w), vec![k]);
    // The data type itself, as a root.
    assert_eq!(relies(&p.g, witness), vec![k]);
}

#[test]
fn reliance_through_a_validator() {
    let mut p = Prelude::new();
    let bool_ = data(&mut p.g, "Bool", vec![], Sort::Type(0));
    check::define_ctors(
        &mut p.g,
        bool_,
        vec![ctor("False", vec![]), ctor("True", vec![])],
    )
    .unwrap();
    native::register_bool(&mut p.g, bool_).unwrap();
    let bool_ty = Term::data(bool_, vec![]);
    let tru = Term::ctor(bool_, 1, vec![]);
    // `type Decidable (p: Prop) = { holds: Bool, sound: holds = True → p }`.
    let decidable = check::declare_data_group_as(
        &mut p.g,
        vec![("p".into(), prop())],
        Sort::Type(0),
        vec![("Decidable".into(), "Decidable".into(), span(), true)],
    )
    .unwrap()[0];
    check::define_ctors(
        &mut p.g,
        decidable,
        vec![ctor(
            "MkDecidable",
            vec![
                ("holds", bool_ty.clone()),
                ("sound", arrow(eq(Some(bool_ty), v(0), tru), v(1))),
            ],
        )],
    )
    .unwrap();
    // f : (n : Nat) -> [auto ok : n = n] -> Nat, validated by an assumed
    // `dec.?1 : (n : Nat) -> Decidable (n = n)`.
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
    let dec_ty = pi(
        "n",
        p.nat_ty(),
        Term::data(decidable, vec![eq(None, v(0), v(0))]),
    );
    let dec = assume_as(&mut p.g, "dec.?1", dec_ty, "Main.dec", 1).unwrap();
    assert_eq!(relies(&p.g, f), Vec::<DefId>::new());
    let decision = app(Term::Def(dec), [v(0)]);
    check::add_validator(&mut p.g, f, 1, decidable, &decision).unwrap();
    assert_eq!(relies(&p.g, f), vec![dec]);
}

#[test]
fn reliance_through_a_run_body() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let k = assume_as(&mut p.g, "k.?1", nat.clone(), "Main.k", 1).unwrap();
    let zero = p.num(0);
    let g = define(&mut p.g, "g", nat, zero).unwrap();
    assert_eq!(relies(&p.g, g), Vec::<DefId>::new());
    check::set_run_body(&mut p.g, g, &Term::Def(k)).unwrap();
    assert_eq!(relies(&p.g, g), vec![k]);
}

#[test]
fn reliance_through_an_unfolding_list() {
    // `opaque def o: Nat := k.?1`, and opaque `t: 0 = 0 := rfl` with
    // `unfolding o`: `t` mentions neither, but is checked with `o`'s body
    // in view.
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let k = assume_as(&mut p.g, "k.?1", nat.clone(), "Main.k", 1).unwrap();
    let o = check::declare_def(
        &mut p.g,
        &"o".into(),
        &"o".into(),
        &nat,
        false,
        false,
        span(),
    )
    .unwrap();
    check::mark_opaque(&mut p.g, o);
    check::define_def(&mut p.g, o, &Term::Def(k)).unwrap();
    let zero = p.num(0);
    let statement = eq(Some(nat), zero.clone(), zero);
    let t = check::declare_def(
        &mut p.g,
        &"t".into(),
        &"t".into(),
        &statement,
        true,
        false,
        span(),
    )
    .unwrap();
    check::mark_opaque(&mut p.g, t);
    check::set_unfolding(&mut p.g, t, &[o]);
    check::define_def(&mut p.g, t, &Term::Refl).unwrap();
    assert_eq!(relies(&p.g, t), vec![k]);
}

// Hashing

#[test]
fn its_hash_is_its_label_and_type() {
    let hash = |name: &str, ty: fn(&Prelude) -> Term, owner: &str, hole: u32| {
        let mut p = Prelude::new();
        let ty = ty(&p);
        let id = assume_as(&mut p.g, name, ty, owner, hole).unwrap();
        hash_of(&p.g, id)
    };
    let nat: fn(&Prelude) -> Term = Prelude::nat_ty;
    let base = hash("f.?1", nat, "Main.f", 1);
    // Not its name, which no declaration's hash includes.
    assert_eq!(hash("renamed", nat, "Main.f", 1), base);
    // Its owner, its hole and its type are.
    assert_ne!(hash("f.?1", nat, "Main.g", 1), base);
    assert_ne!(hash("f.?1", nat, "Main.f", 2), base);
    assert_ne!(hash("f.?1", comm, "Main.f", 1), base);
}

/// An error's stand-in (docs/proposals/tests-with-errors.md §3.3) is told
/// apart from every goal by its label: a user relying on it never shares a
/// hash with one relying on a `?` of the same statement in the same
/// declaration, so no result made under one is reused under the other.
#[test]
fn an_error_stand_in_hashes_apart_from_a_goal() {
    let user_of = |label: Assumption| {
        let mut p = Prelude::new();
        let ty = comm(&p);
        let gap = check::assume(
            &mut p.g,
            &"c".into(),
            &"c".into(),
            &ty,
            label,
            false,
            span(),
        )
        .expect("a type");
        let proof = app(Term::Def(gap), [p.num(1), p.num(2)]);
        let (one, two) = (p.num(1), p.num(2));
        let ty = eq(
            Some(p.nat_ty()),
            p.plus(one.clone(), two.clone()),
            p.plus(two, one),
        );
        let user = theorem(&mut p.g, "rearrange", ty, proof).unwrap();
        (hash_of(&p.g, gap), hash_of(&p.g, user))
    };
    let (goal, goal_user) = user_of(Assumption::goal("Main.addComm".into(), 1));
    let (error, error_user) = user_of(Assumption::error("Main.addComm".into()));
    assert_ne!(goal, error);
    assert_ne!(goal_user, error_user);
    // Its owner is part of it, as a goal's is.
    let (other, _) = user_of(Assumption::error("Main.addSwap".into()));
    assert_ne!(other, error);
}

/// One stand-in per declaration: a second with the owner's label is
/// refused, whatever its type, while a goal of the same owner is another
/// label.
#[test]
fn a_stand_in_s_label_is_used_once() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let owner: stitchwort_core::Name = "Main.f".into();
    let first = check::assume(
        &mut p.g,
        &"f".into(),
        &"f".into(),
        &nat,
        Assumption::error(owner.clone()),
        false,
        span(),
    );
    assert!(first.is_ok());
    let other = comm(&p);
    let again = check::assume(
        &mut p.g,
        &"f".into(),
        &"f".into(),
        &other,
        Assumption::error(owner.clone()),
        false,
        span(),
    );
    assert_eq!(again.map_err(|d| d.code), Err("E-MALFORMED"));
    assert!(assume_as(&mut p.g, "f.?1", nat, "Main.f", 1).is_ok());
}

#[test]
fn a_user_s_hash_covers_the_assumption() {
    // `rearrange` proved from hole 1 of `addComm`, from hole 2, from a goal
    // with a different statement, and with `addComm` proved: four hashes.
    let statement = |p: &Prelude| {
        let (one, two) = (p.num(1), p.num(2));
        eq(
            Some(p.nat_ty()),
            p.plus(one.clone(), two.clone()),
            p.plus(two, one),
        )
    };
    let with_goal = |owner: &str, hole: u32, goal_ty: fn(&Prelude) -> Term| {
        let mut p = Prelude::new();
        let ty = goal_ty(&p);
        let goal = assume_as(&mut p.g, "addComm.?1", ty, owner, hole).unwrap();
        let proof = app(Term::Def(goal), [p.num(1), p.num(2)]);
        let ty = statement(&p);
        let user = theorem(&mut p.g, "rearrange", ty, proof).unwrap();
        hash_of(&p.g, user)
    };
    // A goal that says the same with an extra `0 +`: a different type.
    let other: fn(&Prelude) -> Term = |p| {
        let nat = p.nat_ty();
        pi(
            "n",
            nat.clone(),
            pi(
                "m",
                nat.clone(),
                eq(
                    Some(nat),
                    p.plus(p.num(0), p.plus(v(1), v(0))),
                    p.plus(v(0), v(1)),
                ),
            ),
        )
    };
    let base = with_goal("Main.addComm", 1, comm);
    assert_ne!(with_goal("Main.addComm", 2, comm), base);
    assert_ne!(with_goal("Main.addComm", 1, other), base);
    // Filled: `addComm` a definition with a body, so nothing cached under
    // the assumption is reused.
    let mut p = Prelude::new();
    let ty = comm(&p);
    let filled = check::declare_def(
        &mut p.g,
        &"addComm".into(),
        &"addComm".into(),
        &ty,
        true,
        false,
        span(),
    )
    .unwrap();
    // The body stands for any proof: it's another owner's assumption.
    let lemma = comm(&p);
    let inner = assume_as(&mut p.g, "lemma.?1", lemma, "Main.lemma", 1).unwrap();
    check::define_def(&mut p.g, filled, &Term::Def(inner)).unwrap();
    let proof = app(Term::Def(filled), [p.num(1), p.num(2)]);
    let ty = statement(&p);
    let user = theorem(&mut p.g, "rearrange", ty, proof).unwrap();
    assert_ne!(hash_of(&p.g, user), base);
}

// Running

#[test]
fn running_erases_a_proof_assumption_and_keeps_a_value_one_stuck() {
    let mut p = Prelude::new();
    let goal = add_comm_goal(&mut p);
    let nat = p.nat_ty();
    let hole = assume_as(&mut p.g, "half.?1", nat, "Main.half", 1).unwrap();
    let _op = p.g.machine.budget.operation(Limits::default());
    let _running = p.g.machine.erasure.running();
    let ev = p.g.ev();
    let proof = eval(&ev, &[], &app(Term::Def(goal), [p.num(1), p.num(2)])).unwrap();
    assert!(
        stitchwort_core::erase::is_erased(&proof),
        "a proof is erased"
    );
    let value = eval(&ev, &[], &Term::Def(hole)).unwrap();
    assert!(matches!(value, Value::Neutral(Head::Def(id), _) if id == hole));
}

/// The memoised walk (`relies_on`) agrees with the full one, and a rewind
/// forgets what it remembered of the declarations it removes: an id reused
/// by a declaration that relies on nothing isn't reported as relying.
#[test]
fn remembered_reliance_agrees_and_is_forgotten_by_a_rewind() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let (one, two) = (p.num(1), p.num(2));
    let statement = eq(
        Some(nat),
        p.plus(one.clone(), two.clone()),
        p.plus(two.clone(), one.clone()),
    );
    let by_rfl = theorem(&mut p.g, "byRfl", statement.clone(), Term::Refl).unwrap();
    let mark = p.g.mark();
    let goal = add_comm_goal(&mut p);
    let direct = theorem(
        &mut p.g,
        "direct",
        statement.clone(),
        app(Term::Def(goal), [one, two]),
    )
    .unwrap();
    let chained = theorem(&mut p.g, "chained", statement.clone(), Term::Def(direct)).unwrap();
    let remembered = |g: &Kernel, d: DefId| relies_on(&g.ev(), d.into(), &|_| false);
    for _ in 0..2 {
        assert_eq!(remembered(&p.g, chained), Some(goal));
        assert_eq!(remembered(&p.g, direct), Some(goal));
        assert_eq!(remembered(&p.g, by_rfl), None);
    }
    p.g.forget_since(&mark);
    assert_eq!(p.g.derived_state_since(&mark), None);
    let again = theorem(&mut p.g, "again", statement, Term::Refl).unwrap();
    assert_eq!(again, goal, "the id is reused");
    assert_eq!(remembered(&p.g, again), None);
}
