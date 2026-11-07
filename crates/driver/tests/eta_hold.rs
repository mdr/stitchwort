//! Record eta's native hold (D2551, `value::eta_held`): a definition with a
//! native implementation keeps its record patterns stuck on unknowns, so
//! rule 2 never opens it. The machine and the reference evaluator must hold
//! the same definitions, and which ones are held is pinned, so a new native
//! that matches on a record is a decision, not a surprise.

use stitchwort_core::term::Term;
use stitchwort_core::value::{Value, conv, eval};
use stitchwort_core::{DefId, Ev, reference};
use stitchwort_driver::driver::Session;

const PROGRAM: &str = r#"
import Std (Float)

def sum (x: Float) (y: Float): Float := Float.add x y

def sumUnfolded (x: Float) (y: Float): Float :=
  Float.ofBits (Float.Model.addBits x.bits y.bits)

def sumRebuilt (x: Float) (y: Float): Float :=
  Float.add { bits = x.bits, valid = x.valid } y
"#;

fn find(g: &Ev, name: &str) -> DefId {
    DefId(
        g.env
            .defs()
            .iter()
            .position(|d| &**d.name() == name)
            .unwrap_or_else(|| panic!("no `{name}`")),
    )
}

/// The body of `name` with fresh variables for its parameters, by the
/// machine or the reference evaluator.
fn applied(g: &Ev, name: &str, reference: bool) -> (usize, Value) {
    let def = g.def(find(g, name));
    let arity = def.arity();
    let body = def.body().expect("a body").peel_lams(arity);
    let env: Vec<Value> = (0..arity).map(Value::var).collect();
    let value = if reference {
        reference::eval(g, &env, body).unwrap()
    } else {
        eval(g, &env, body).unwrap()
    };
    (arity, value)
}

/// Whether `a` and `b` are convertible, by the machine and by the reference
/// evaluator.
fn answers(g: &Ev, a: &str, b: &str) -> [bool; 2] {
    let both = |reference: bool| {
        let (level, x) = applied(g, a, reference);
        let (_, y) = applied(g, b, reference);
        if reference {
            reference::conv(g, level, &x, &y).unwrap()
        } else {
            conv(g, level, &x, &y).unwrap()
        }
    };
    [both(false), both(true)]
}

#[test]
fn a_held_definition_stays_stuck_in_both_evaluators() {
    let mut session = Session::eager();
    if let Err(e) = session.load("hold.sw", PROGRAM) {
        panic!("{e:?}");
    }
    let g = &session.elab.ev();
    // Opened by rule 2 on unknowns these would be equal; held, they aren't.
    assert_eq!(answers(g, "sum", "sumUnfolded"), [false, false]);
    // Held calls still compare argument by argument, then by rule 1.
    assert_eq!(answers(g, "sum", "sumRebuilt"), [true, true]);
}

/// The definitions whose case tree matches on a type with eta and that
/// have a native: those [`stitchwort_core::value::eta_held`] holds.
#[test]
fn only_float_add_is_held() {
    let session = Session::eager();
    let g = &session.elab.ev();
    let held: Vec<String> = (0..g.env.defs().len())
        .map(DefId)
        .filter(|&id| g.env.builtins().has_native(id))
        .filter(|&id| {
            g.def(id).body().is_some_and(|body| {
                body.subterms()
                    .any(|(t, _)| matches!(t, Term::Case(_, d, _) if g.data(*d).eta()))
            })
        })
        .map(|id| g.def(id).name().to_string())
        .collect();
    assert_eq!(held, ["Float.add"]);
}
