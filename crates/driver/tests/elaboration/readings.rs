//! A test's reading is found by its function as written
//! (docs/proposals/bool-as-proposition.md §5.4), so it doesn't depend on
//! whether evaluation keeps calls folded: with gluing off, a fact's type
//! has `inRange lo x hi` unfolded to `lo <= x && x <= hi`, which `&&`
//! would read as `∧`; the reader looks at the type as written instead.

use stitchwort_driver::driver::Session;

const PROGRAM: &str = "import Std (Bool, Nat, Iff)

type InRange (lo x hi: Nat): Prop = { low: lo ≤ x, high: x ≤ hi }

def inRange (lo x hi: Nat): Bool := lo <= x && x <= hi

@[reading]
theorem inRangeReads (lo x hi: Nat): inRange lo x hi ↔ InRange lo x hi := {
  forward = h => { low = h.left, high = h.right },
  backward = r => Both r.low r.high
}

def both (x: Nat): Bool := inRange 1 x 9 && inRange 2 x 8

theorem read (x: Nat) (h: inRange 1 x 9): InRange 1 x 9 := h.read

theorem field (x: Nat) (h: inRange 1 x 9): x ≤ 9 := h.high

theorem pattern (x: Nat) (h: inRange 1 x 9): x ≤ 9 :=
  match h with
    | { low, high } => high

theorem letPattern (x: Nat) (h: inRange 1 x 9): x ≤ 9 :=
  let { low, high } := h
  high

theorem nested (x: Nat) (h: both x): x ≤ 8 :=
  match h with
    | Both _ { low, high } => high

theorem built (x: Nat) (low: 1 ≤ x) (high: x ≤ 9): inRange 1 x 9 := { low, high }

def use (x: Nat) (h: inRange 1 x 9): Nat := x

def argument (x: Nat) (low: 1 ≤ x) (high: x ≤ 9): Nat := use x { low, high }

theorem annotated (x: Nat) (low: 1 ≤ x) (high: x ≤ 9): x ≤ 9 :=
  ({ low, high }: inRange 1 x 9).high
";

fn load(glue: bool) {
    let mut session = Session::new();
    session.elab.options.glue = glue;
    if let Err(errors) = session.load("readings.sw", PROGRAM) {
        panic!("glue {glue}: {errors:#?}");
    }
}

#[test]
fn a_user_reading_is_found_glued() {
    load(true);
}

#[test]
fn a_user_reading_is_found_unglued() {
    load(false);
}
