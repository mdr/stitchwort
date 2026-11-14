//! Division of a number with an unknown part (SW-922,
//! docs/proposals/division.md).
//!
//! Since `+` computes on its second argument (R4), `x * 3 + 12345` is 12345
//! `Succ`s around `x * 3`, so `Nat.divFuel` has 12345 known steps of fuel on
//! it. When each step was `if Nat.leq d n then Succ (next step) else 0`, a
//! step stuck on `x` held the next one in its branch, and the normal form
//! grew with the square of the constant: 27 MB at 2,048, too large to show
//! at 4,096. Now a step is `Nat.divStep (Nat.leq d n) …`, one call stuck on
//! its comparison, and goals show it as the `/` it comes from.

use stitchwort_core::reference;
use stitchwort_core::value::{self, Value, set_shortcuts_disabled};
use stitchwort_core::{DefId, Name, Term};
use stitchwort_driver::driver::{Session, with_session};

const STACK: usize = 64 * 1024 * 1024;

/// The `partial-handlers.sw` generator (and SW-920's): a dividend with an
/// unknown part and a constant on the right.
const LCG: &str = "def lcg (seed: Nat): Nat := (seed * 1103515245 + 12345) % 2147483648\n\
                   def quotient (seed: Nat): Nat := (seed * 3 + 12345) / 2147483648\n\
                   def later (x: Nat): Nat := (x + 5) / 3\n\
                   def bothOpen (x: Nat) (d: Nat): Nat := (x + 5) / (d + 2)\n";

fn def(g: &stitchwort_core::Ev, name: &str) -> DefId {
    DefId(
        g.env
            .defs()
            .iter()
            .position(|d| &**d.name() == name)
            .unwrap_or_else(|| panic!("`{name}` is defined")),
    )
}

/// `name` applied to `arity` variables, evaluated by the machine.
fn applied(g: &stitchwort_core::Ev, name: &str, arity: usize) -> Value {
    let mut term = Term::Def(def(g, name));
    for i in (0..arity).rev() {
        term = Term::app(term, Term::Var(i));
    }
    let env: Vec<Value> = (0..arity).map(Value::var).collect();
    value::eval(g, &env, &term).expect("no limits")
}

/// The normal form of `lcg seed`, by both evaluators, stays small: it was
/// too large to write out (over 4 GB) when each stuck step held the next.
#[test]
fn an_open_dividend_has_a_small_normal_form() {
    with_session(STACK, Session::for_stack, |session| {
        assert!(session.load("lcg.sw", LCG).is_ok());
        let g = &session.elab.ev();
        for name in ["lcg", "quotient"] {
            let machine = applied(g, name, 1);
            let term = value::quote(g, 1, &machine).expect("no limits");
            let size = format!("{term:?}").len();
            assert!(
                size < 2_000,
                "{name}: the machine's normal form is {size} characters"
            );
            let slow = reference::eval(
                g,
                &[Value::var(0)],
                &Term::app(Term::Def(def(g, name)), Term::Var(0)),
            )
            .expect("no limits");
            let term = reference::quote(g, 1, &slow).expect("no limits");
            let size = format!("{term:?}").len();
            assert!(
                size < 2_000,
                "{name}: the reference's normal form is {size} characters"
            );
        }
    });
}

/// A step of division stuck on an unknown is shown as the `/` (or `%`) it
/// comes from, where `n / d` reads back to the same value; a later step,
/// whose fuel isn't one less than the number, is shown as it is.
#[test]
fn a_stuck_step_of_division_is_shown_as_division() {
    with_session(STACK, Session::for_stack, |session| {
        assert!(session.load("lcg.sw", LCG).is_ok());
        let g = &session.elab.ev();
        let x: Vec<Name> = vec!["x".into()];
        let xd: Vec<Name> = vec!["x".into(), "d".into()];
        let shown = |names: &[Name], name: &str| {
            let v = applied(g, name, names.len());
            let printed = stitchwort_core::pretty::value(g, names, &v);
            assert_eq!(
                printed,
                stitchwort_core::pretty::value_for_message(g, names, &v),
                "{name}"
            );
            printed
        };
        assert_eq!(shown(&x, "lcg"), "(x * 1103515245 + 12345) % 2147483648");
        assert_eq!(shown(&x, "quotient"), "(x * 3 + 12345) / 2147483648");
        // `Nat.leq (d + 2) (x + 5)` computes to `Nat.leq d (x + 3)`.
        assert_eq!(shown(&xd, "bothOpen"), "(x + 5) / (d + 2)");
        // `(x + 5) / 3` takes a step (3 fits into `x + 5`), then sticks on
        // `Nat.leq 3 (x + 2)` with fuel `x + 4`: not `(x + 2) / 3`. The steps
        // taken are counted as a compact `rest + q`, as any sum with an
        // unknown is shown.
        assert_eq!(
            shown(&x, "later"),
            "Nat.divStep (1 <= x) (x + 3) (x + 2) 3 + 1"
        );
    });
}

/// SW-920's proof, `Std.Nat.modLt` applied to the dividend with `_` for the
/// seed, checks in few steps, also with the conversion shortcuts off (the
/// unifier's identity shortcut is what made it quick before division
/// changed: without it, comparing the two sides unfolded both 12345 levels
/// deep, about 154 million steps, 30 s). Its type prints in full (`lcg` and
/// `<` unfolded) as the division it is, where it couldn't be built before.
#[test]
fn the_sw920_proof_and_its_goal_are_quick() {
    for shortcuts in [true, false] {
        with_session(STACK, Session::for_stack, |session| {
            set_shortcuts_disabled(!shortcuts);
            let before = session.elab.kernel.machine.budget.total_work();
            let loaded = session.load(
                "sw920.sw",
                &format!(
                    "{LCG}\ntheorem t (seed: Nat): lcg seed < 2147483648 :=\n  \
                     Std.Nat.modLt (_ * 1103515245 + 12345) 2147483648\n"
                ),
            );
            set_shortcuts_disabled(false);
            assert!(loaded.is_ok(), "{loaded:?}");
            let g = &session.elab.ev();
            let work = g.machine.budget.total_work() - before;
            eprintln!("shortcuts {shortcuts}: work {work}");
            assert!(
                work < 2_000_000,
                "shortcuts {shortcuts}: checking took {work} steps"
            );
            let ty = &g.def(def(g, "t")).ty_value();
            assert_eq!(
                stitchwort_core::pretty::value(g, &[], ty),
                "∀ (seed: Nat) => (seed * 1103515245 + 12345) % 2147483648 ≤ 2147483647"
            );
        });
    }
}
