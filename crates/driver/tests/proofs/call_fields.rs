//! Fields of calls in the machine (docs/proposals/match-call-field.md):
//! a stuck field of a call, `(f x).i`, eliminated by an application or `J`
//! computes the call first, while gluing (stages 1 and 2, review SW-2108);
//! and the elaborator keeps a field of a folded call as the call's field,
//! where the kernel projects its unfolding. The stuck forms are built by
//! hand, as the machine makes them when a call was stuck and later can step
//! (a metavariable since solved, or a narrower transparency set).

use std::rc::Rc;

use stitchwort_core::term::Term;
use stitchwort_core::value::{Elim, Head, Value, eval, force, quote};
use stitchwort_core::{DataId, DefId, Ev, Icit};
use stitchwort_driver::driver::Session;

const PROGRAM: &str = r#"
import Std (Nat)

type Fn = { at: Nat → Nat }

type Proved = { k: Nat, same: k = k }

def fieldOf (x: Nat): Fn :=
  match x with
    | Zero => { at = y => y }
    | Succ m => { at = y => m }

def reflAt (x: Nat): x = x := rfl

def proved (x: Nat): Proved :=
  match x with
    | Zero => { k = 0, same = reflAt 0 }
    | Succ m => { k = x, same = reflAt x }

opaque def hiddenFn (x: Nat): Fn := fieldOf x

def NatEq (a: Nat) (b: Nat): Prop := a = b

def liftFn (q: Quot Nat NatEq): Fn := Quot.lift (b => { at = y => b }) (x y h => rewrite h in rfl) q

def countDown (x: Nat): Box
  decreasing x
:=
  match x with
    | Zero => { value = 0 }
    | Succ m => countDown m [decreasing := omega]

type Box = { value: Nat }
"#;

fn def(g: &Ev, name: &str) -> DefId {
    let id = g.env.defs().iter().position(|d| &**d.name() == name);
    DefId(id.unwrap_or_else(|| panic!("no `{name}`")))
}

fn data(g: &Ev, name: &str) -> DataId {
    let id = g.env.datas().iter().position(|d| &**d.name() == name);
    DataId(id.unwrap_or_else(|| panic!("no `{name}`")))
}

fn zero(g: &Ev) -> Value {
    Value::Ctor(data(g, "Nat"), 0, Vec::new().into())
}

/// The stuck field `(f arg).i` of record type `d`.
fn stuck_field(f: DefId, arg: Value, d: DataId, i: usize) -> Value {
    Value::Neutral(
        Head::Def(f),
        vec![Elim::App(arg, Icit::Explicit), Elim::Proj(d, i)].into(),
    )
}

/// `field` applied to the variable at level 0, evaluated.
fn applied(g: &Ev, field: Value) -> Value {
    let term = Term::App(Term::Var(0).into(), Term::Var(1).into(), Icit::Explicit);
    let v = eval(g, &[Value::var(0), field], &term).unwrap();
    force(g, v).unwrap()
}

fn loaded() -> Session {
    let mut session = Session::eager();
    session.load("fields.sw", PROGRAM).expect("loads");
    session
}

#[test]
fn an_applied_stuck_field_computes_only_while_gluing() {
    let session = loaded();
    let g = &session.elab.ev();
    let field = stuck_field(def(g, "fieldOf"), zero(g), data(g, "Fn"), 0);
    g.machine.glue.set(false);
    let off = applied(g, field.clone());
    assert!(
        matches!(&off, Value::Neutral(Head::Def(_), spine) if spine.len() == 3),
        "unglued, the argument is pushed on: {off:?}"
    );
    g.machine.glue.set(true);
    let on = applied(g, field);
    g.machine.glue.set(false);
    assert!(
        matches!(on, Value::Neutral(Head::Var(0, _), ref spine) if spine.is_empty()),
        "glued, `(fieldOf 0).at y` is `y`: {on:?}"
    );
}

#[test]
fn an_opaque_calls_field_computes_only_where_its_body_is_seen() {
    let session = loaded();
    let g = &session.elab.ev();
    let hidden = def(g, "hiddenFn");
    let field = stuck_field(hidden, zero(g), data(g, "Fn"), 0);
    g.machine.glue.set(true);
    let stuck = applied(g, field.clone());
    assert!(
        matches!(&stuck, Value::Neutral(Head::Def(id), spine) if *id == hidden && spine.len() == 3),
        "hidden, it stays stuck: {stuck:?}"
    );
    let seen = {
        let _set = g.machine.transparent.set(Rc::from(vec![hidden]));
        applied(g, field)
    };
    g.machine.glue.set(false);
    assert!(
        matches!(seen, Value::Neutral(Head::Var(0, _), ref spine) if spine.is_empty()),
        "seen, it computes: {seen:?}"
    );
}

/// `J (x e => Nat) 0 proof` in an environment holding `proof`.
fn transported(g: &Ev, proof: Value) -> Value {
    let nat = Term::Data(data(g, "Nat"), vec![]);
    let motive = Term::Lam(
        "x".into(),
        Icit::Explicit,
        Term::Lam("e".into(), Icit::Explicit, nat.into()).into(),
    );
    let base = Term::Ctor(data(g, "Nat"), 0, vec![]);
    let term = Term::J(motive.into(), base.into(), Term::Var(0).into());
    g.machine.glue.set(true);
    let v = eval(g, &[proof], &term).and_then(|v| force(g, v));
    g.machine.glue.set(false);
    v.unwrap()
}

#[test]
fn j_on_a_stuck_field_computes_the_call_first() {
    let session = loaded();
    let g = &session.elab.ev();
    // `(proved 0).same` is `reflAt 0`, a call: `J` forces it to `rfl`.
    let field = stuck_field(def(g, "proved"), zero(g), data(g, "Proved"), 1);
    let v = transported(g, field);
    assert!(
        matches!(v, Value::Ctor(_, 0, _) | Value::Nat(_)),
        "`J` on `rfl` is its base: {v:?}"
    );
    // Stuck in its own case tree, the field is eliminated as it is.
    let field = stuck_field(def(g, "proved"), Value::var(1), data(g, "Proved"), 1);
    let v = transported(g, field);
    assert!(
        matches!(&v, Value::Neutral(Head::Def(_), spine)
            if matches!(spine.iter().last(), Some(Elim::J { .. }))),
        "stuck: {v:?}"
    );
}

/// `term`'s read-back under the variable `n` (level 0) and `q` (level 1),
/// glued or not, as the kernel or the elaborator.
fn read(g: &Ev, term: &Term, glue: bool, kernel: bool) -> Term {
    g.machine.glue.set(glue);
    g.machine.kernel.set(kernel);
    let v = eval(g, &[Value::var(0), Value::var(1)], term).unwrap();
    let t = quote(g, 2, &v).unwrap();
    g.machine.glue.set(false);
    g.machine.kernel.set(false);
    t
}

fn mentions(term: &Term, id: DefId) -> bool {
    format!("{term:?}").contains(&format!("Def(DefId({}))", id.0))
}

#[test]
fn a_folded_calls_field_stays_the_calls_in_the_elaborator_only() {
    let session = loaded();
    let g = &session.elab.ev();
    let count_down = def(g, "countDown");
    // `(countDown n).value`, with `n` at index 1.
    let term = Term::Proj(
        data(g, "Box"),
        0,
        Term::App(
            Term::Def(count_down).into(),
            Term::Var(1).into(),
            Icit::Explicit,
        )
        .into(),
    );
    let shown = read(g, &term, true, false);
    let Term::Proj(_, 0, call) = &shown else {
        panic!("a field: {shown:?}")
    };
    assert!(
        matches!(&**call, Term::App(f, _, _) if matches!(**f, Term::Def(id) if id == count_down)),
        "the elaborator keeps the call: {shown:?}"
    );
    // The kernel, glued or not, projects the unfolding, the fuelled helper.
    for glue in [true, false] {
        let checked = read(g, &term, glue, true);
        assert!(
            !mentions(&checked, count_down),
            "the kernel (glue {glue}) projects the unfolding: {checked:?}"
        );
    }
}

/// A field of a call with a `Quot.lift` leaf, `(liftFn q).at` (`q` at index
/// 0), is shown as the call's while gluing: such a call is glued (only
/// unglued is it left folded), so this is rule 2's glued case.
#[test]
fn a_lift_leaf_calls_field_stays_the_call_while_gluing() {
    let session = loaded();
    let g = &session.elab.ev();
    let lift_fn = def(g, "liftFn");
    let field = Term::Proj(
        data(g, "Fn"),
        0,
        Term::App(
            Term::Def(lift_fn).into(),
            Term::Var(0).into(),
            Icit::Explicit,
        )
        .into(),
    );
    let shown = read(g, &field, true, false);
    assert!(
        mentions(&shown, lift_fn),
        "glued, the call stays: {shown:?}"
    );
}

/// Applied, the same field computes through the lift while gluing, as it
/// does unglued and in the reference evaluator (D3030; review SW-2108 F3
/// proposed leaving it folded, which made glued evaluation's value a rigid
/// term unequal to theirs).
#[test]
fn a_lift_leaf_calls_applied_field_is_the_same_glued_and_unglued() {
    let session = loaded();
    let g = &session.elab.ev();
    let lift_fn = def(g, "liftFn");
    let field = Term::Proj(
        data(g, "Fn"),
        0,
        Term::App(
            Term::Def(lift_fn).into(),
            Term::Var(0).into(),
            Icit::Explicit,
        )
        .into(),
    );
    let term = Term::App(field.into(), Term::Var(1).into(), Icit::Explicit);
    let env = [Value::var(0), Value::var(1)];
    g.machine.glue.set(true);
    let glued = eval(g, &env, &term).unwrap();
    g.machine.glue.set(false);
    let unglued = eval(g, &env, &term).unwrap();
    let reference = stitchwort_core::reference::eval(g, &env, &term).unwrap();
    for (name, other) in [("unglued", &unglued), ("the reference", &reference)] {
        g.machine.glue.set(true);
        let same = stitchwort_core::value::conv(g, 2, &glued, other).unwrap();
        g.machine.glue.set(false);
        let same_unglued = stitchwort_core::value::conv(g, 2, other, &glued).unwrap();
        assert!(
            same && same_unglued,
            "glued and {name} agree: {glued:?} against {other:?}"
        );
    }
}
