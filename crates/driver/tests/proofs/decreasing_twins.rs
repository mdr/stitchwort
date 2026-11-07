//! The twins `decreasing` makes of the `match`es lifted from a body, for
//! `f.unfold`'s plain form (`decreasing/plain.rs`): which helpers get one,
//! and what is left in them.

use stitchwort_core::Term;
use stitchwort_driver::driver::Session;

fn load(source: &str) -> Session {
    let mut session = Session::new();
    if let Err(errors) = session.load("test.sw", source) {
        panic!("doesn't check: {errors:#?}");
    }
    assert!(
        !(session.warnings.iter()).any(|w| w.code == "W-DECREASING-UNFOLD"),
        "{:#?}",
        session.warnings
    );
    session
}

fn plain_names(session: &Session) -> Vec<String> {
    (session.elab.kernel.env.defs().iter())
        .map(|d| d.name().to_string())
        .filter(|n| n.ends_with("%plain"))
        .collect()
}

/// A nested `match`: a `let` in the outer arm that only the inner call's
/// proof mentions is passed to the inner helper, whose twin drops it with
/// the proof, so the outer twin's `let` has no use left. No plain form
/// keeps a `let` nothing uses.
#[test]
fn a_let_only_an_inner_twin_dropped_is_gone() {
    let session = load(
        "\
import Std (Bool, Nat)

theorem nestedBelow (n: Nat) (k: Nat) (j: Nat) (bound: Nat) (found: n - k = Succ j): n - (k + 1) < Succ j :=
  omega [found]

def countNested (n: Nat) (k: Nat): Nat
    decreasing n - k
:=
  match found: n - k with
    | Zero => k
    | Succ j =>
      let bound := j + 1
      match k == 3 with
        | True => countNested n (k + 1) [decreasing := nestedBelow n k j bound found]
        | False => countNested n (k + 1)

theorem countNestedUnfolds (n: Nat) (k: Nat):
    countNested n k
      = (match n - k with
        | Zero => k
        | Succ j => (match k == 3 with
          | True => countNested n (k + 1)
          | False => countNested n (k + 1))) :=
  countNested.unfold n k

test \"countNested\" := countNested 5 0 == 5
",
    );
    let names = plain_names(&session);
    assert!(names.len() >= 3, "the view and both twins: {names:?}");
    for d in session.elab.kernel.env.defs() {
        if !d.name().ends_with("%plain") {
            continue;
        }
        let body = d.body().expect("a plain form has a body");
        for (t, _) in body.subterms() {
            if let Term::Let(x, _, _, b, _) = t {
                assert!(
                    x.starts_with('%') || b.mentions(0),
                    "`{}` keeps a dead `let {x}`",
                    d.name()
                );
            }
        }
    }
}

/// A call to the definition in a pattern guard only: the `match` still
/// gets its equation, which the guard's call needs to decrease.
#[test]
fn a_call_in_a_guard_gets_the_equation() {
    load(
        "\
import Std (Bool, Nat)

def countGuard (n: Nat) (k: Nat): Nat
    decreasing n - k
:=
  match n - k with
    | Zero => k
    | Succ j if countGuard n (k + 1) == n => n
    | Succ _ => k

test \"countGuard\" := countGuard 4 0 == 4
",
    );
}

/// A local definition that calls the outer one gets no twin: `f.unfold`
/// shows it by its own name, which its local equations are about.
#[test]
fn a_local_definition_gets_no_twin() {
    let session = load(
        "\
import Std (Bool, Nat)

def walk (n: Nat) (k: Nat): Nat
    decreasing n - k
:=
  def go (below: k < n): Nat := walk n (k + 1) [decreasing := omega [below]]
  if h: k < n then go h else k

test \"walk\" := walk 4 0 == 4
",
    );
    let names = plain_names(&session);
    assert!(
        !names.iter().any(|n| n.contains("go")),
        "a twin of `go`: {names:?}"
    );
}
