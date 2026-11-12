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

-- The second argument's type is the result's first parameter, not the
-- first's: each argument is read against its own parameter.
theorem t (x: Nat) (h: inRange 1 x 9): inRange 0 x 100 → x ≤ 9 := _ => h.high

theorem callsT (x: Nat) (low: 1 ≤ x) (high: x ≤ 9) (zero: 0 ≤ x) (wide: x ≤ 100): x ≤ 9 :=
  t x { low, high } { low = zero, high = wide }

-- `h2`'s type as written is in terms of `x`, which each branch refines.
theorem refined (x: Nat) (h: inRange 1 x 9): 1 ≤ x :=
  let h2 := h
  match x with
    | 0 => h2.low
    | Succ n => h2.low
";

fn load(glue: bool) {
    let mut session = Session::new();
    session.elab.options.glue = glue;
    if let Err(errors) = session.load("readings.sw", PROGRAM) {
        panic!("glue {glue}: {errors:#?}");
    }
}

/// The errors of loading `source`, as `CODE: message` lines.
fn errors(source: &str) -> Vec<String> {
    let mut session = Session::new();
    match session.load("readings.sw", source) {
        Ok(_) => Vec::new(),
        Err(errors) => errors
            .iter()
            .map(|d| format!("{}: {}", d.code, d.message))
            .collect(),
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

const IN_RANGE: &str = "import Std (Bool, Nat, Iff)

type InRange (lo x hi: Nat): Prop = { low: lo ≤ x, high: x ≤ hi }

def inRange (lo x hi: Nat): Bool := lo <= x && x <= hi
";

/// A reading written as `Iff (…) (…)` is known to be one before it is
/// checked, so a use above it says the reading is declared below.
#[test]
fn a_reading_written_with_iff_below_its_use_is_found() {
    let source = format!(
        "{IN_RANGE}
theorem below (x: Nat) (h: inRange 1 x 9): x ≤ 9 := h.read.high

@[reading]
theorem inRangeReads (lo x hi: Nat): Iff (inRange lo x hi) (InRange lo x hi) := {{
  forward = h => {{ low = h.left, high = h.right }},
  backward = r => Both r.low r.high
}}
"
    );
    let errors = errors(&source);
    assert!(
        errors.len() == 1 && errors[0].starts_with("E-NO-READING") && errors[0].ends_with("yet"),
        "{errors:#?}"
    );
}

/// So is one whose test is written with a dot, `b.ok`.
#[test]
fn a_reading_written_with_a_dot_below_its_use_is_found() {
    let source = "import Std (Bool, Nat, Iff)

type Box = { n: Nat }

def Box.ok (b: Box): Bool := b.n <= 3

theorem below (b: Box) (h: b.ok): b.n ≤ 3 := h.read

@[reading]
theorem Box.okReads (b: Box): b.ok ↔ b.n ≤ 3 := { forward = h => h, backward = h => h }
";
    let errors = errors(source);
    assert!(
        errors.len() == 1 && errors[0].starts_with("E-NO-READING") && errors[0].ends_with("yet"),
        "{errors:#?}"
    );
}

/// A lemma the reading's proof uses, about the test, declared above the
/// reading, can't be checked through the reading, which isn't there yet;
/// today it is refused as a use above the reading. Whether checking order
/// should put such uses after the reading is Matt's call (SW-2992 review
/// M1).
#[test]
#[ignore = "SW-2992 review M1: waiting on the checking-order decision"]
fn a_helper_above_the_reading_that_it_uses_checks() {
    let source = format!(
        "{IN_RANGE}
theorem bwd (lo x hi: Nat) (r: InRange lo x hi): inRange lo x hi := Both r.low r.high

@[reading]
theorem inRangeReads (lo x hi: Nat): inRange lo x hi ↔ InRange lo x hi := {{
  forward = h => {{ low = h.left, high = h.right }},
  backward = bwd lo x hi
}}
"
    );
    assert_eq!(errors(&source), Vec::<String>::new());
}
