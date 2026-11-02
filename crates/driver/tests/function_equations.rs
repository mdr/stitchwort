//! Generated equations (docs/proposals/function-equations.md, stage 1a):
//! the statements generated for the note's worked examples (§3.2) are the
//! ones it shows, binder names included, and what isn't generated is
//! recorded with its reason.

use stitchwort_core::{Name, Term};
use stitchwort_driver::driver::Session;

/// The note's worked examples. `explode` is 2021 day 18's as first
/// written; `ex` is its cut-down form from the prototypes (`p1.sw`), whose
/// third arm has no lifted `match`.
const SOURCE: &str = r#"
import Std (Bool, Char, List, Nat, Option, Void)

type Number =
  | Regular (value: Nat)
  | Pair (left: Number) (right: Number)

def addLeftmost (amount: Nat): Number → Number
  | Regular value => Regular (value + amount)
  | Pair left right => Pair (addLeftmost amount left) right

def explode (depth: Nat): Number → Option Nat
  | Regular _ => None
  | Pair (Regular a) (Regular b) => if 4 ≤ depth then Some (a + b) else None
  | Pair left right =>
    match explode (depth + 1) left with
      | Some n => Some n
      | None => explode (depth + 1) right

def ex (depth: Nat): Number → Nat
  | Regular _ => 0
  | Pair (Regular a) (Regular b) => if 4 ≤ depth then a + b else 0
  | Pair left right => ex (depth + 1) left + ex (depth + 1) right

def kind: Nat → Nat
  | 3 => 1
  | 7 => 2
  | n => 0

def kindUnnamed: Nat → Nat
  | 3 => 1
  | 7 => 2
  | _ => 0

type Command = | Up | Down

def commandOf (char: Char): Option Command :=
  match char with
    | 'k' => Some Up
    | 'j' => Some Down
    | _ => None

def keyed: Char → List Char → Nat
  | 'k', [] => 1
  | c, xs => 2

def orp: Number → Nat
  | Regular 0 | Regular 1 => 5
  | _ => 6
"#;

/// `ty`, a closed `Π` type, with every binder's name shown:
/// `(x: A) → (h: P) → body`.
fn statement(g: &stitchwort_core::Globals, ty: &Term) -> String {
    let mut names: Vec<Name> = Vec::new();
    let mut out = String::new();
    let mut t = ty.strip_loc();
    while let Term::Pi(x, icit, dom, cod) = t {
        let shown = stitchwort_core::pretty::term(g, &names, dom);
        let (open, close) = if icit.is_implicit() {
            ("[", "]")
        } else {
            ("(", ")")
        };
        out += &format!("{open}{x}: {shown}{close} → ");
        names.push(x.clone());
        t = cod.strip_loc();
    }
    out + &stitchwort_core::pretty::term(g, &names, t)
}

fn with_session(f: impl FnOnce(&Session) + Send + 'static) {
    with_source(SOURCE.to_string(), f);
}

fn with_source(source: String, f: impl FnOnce(&Session) + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            let mut session = Session::new();
            if let Err(errors) = session.load("equations.sw", &source) {
                panic!("doesn't load: {errors:#?}");
            }
            f(&session);
        })
        .unwrap()
        .join()
        .unwrap();
}

fn generated(session: &Session, name: &str) -> String {
    let g = &session.elab.globals;
    let def = g
        .defs
        .iter()
        .rev()
        .find(|d| &*d.name == name)
        .unwrap_or_else(|| panic!("`{name}` isn't generated"));
    assert!(def.theorem, "`{name}` is a theorem");
    statement(g, &def.ty)
}

fn skipped(session: &Session, name: &str) -> String {
    let g = &session.elab.globals;
    session
        .elab
        .equation_skips()
        .iter()
        .find(|(id, s, _)| format!("{}.{s}", g.defs[id.0].name) == name)
        .map(|(_, _, why)| why.clone())
        .unwrap_or_else(|| panic!("`{name}` isn't recorded as skipped"))
}

#[test]
fn the_notes_worked_examples() {
    with_session(|s| {
        // §3.2, "Plain constructor arms".
        assert_eq!(
            generated(s, "addLeftmost.eq1"),
            "(amount: Nat) → (value: Nat) → addLeftmost amount (Regular value) = Regular (value + amount)"
        );
        assert_eq!(
            generated(s, "addLeftmost.eq2"),
            "(amount: Nat) → (left: Number) → (right: Number) → \
             addLeftmost amount (Pair left right) = Pair (addLeftmost amount left) right"
        );
        // §3.2, "Overlapping and wildcard arms": `explode.eq3`'s hypothesis,
        // on the prototype `ex`, whose third arm is an expression (the
        // printer shows `right = Regular b → Void` as `≠`).
        assert_eq!(
            generated(s, "ex.eq3"),
            "(depth: Nat) → (left: Number) → (right: Number) → \
             (notArm2: (a: Nat) → (b: Nat) → left = Regular a → right ≠ Regular b) → \
             ex depth (Pair left right) = ex (depth + 1) left + ex (depth + 1) right"
        );
        // §3.2, "Literal patterns".
        assert_eq!(
            generated(s, "kind.eq3"),
            "(n: Nat) → (notArm1: n ≠ 3) → (notArm2: n ≠ 7) → kind n = 0"
        );
        // A `_` with no field to name it after is `x1` (§3.1).
        assert_eq!(
            generated(s, "kindUnnamed.eq3"),
            "(x1: Nat) → (notArm1: x1 ≠ 3) → (notArm2: x1 ≠ 7) → kindUnnamed x1 = 0"
        );
        assert_eq!(
            generated(s, "commandOf.eq3"),
            "(char: Char) → (notListed: char ∉ ['k', 'j']) → commandOf char = None"
        );
        assert_eq!(generated(s, "commandOf.eq1"), "commandOf 'k' = Some Up");
        // An earlier arm that also constrains another column keeps Lean's
        // form.
        assert_eq!(
            generated(s, "keyed.eq2"),
            "(c: Char) → (xs: List Char) → (notArm1: c = 'k' → xs ≠ []) → keyed c xs = 2"
        );
        // §3.1, or-patterns: one equation for each alternative.
        assert_eq!(generated(s, "orp.eq1.or1"), "orp (Regular 0) = 5");
        assert_eq!(generated(s, "orp.eq1.or2"), "orp (Regular 1) = 5");
        assert_eq!(
            generated(s, "orp.eq2"),
            "(x1: Number) → (notArm1or1: x1 ≠ Regular 0) → (notArm1or2: x1 ≠ Regular 1) → orp x1 = 6"
        );
    });
}

/// `explode.eq3`, as first written (its third arm a lifted `match`), has no
/// one right side: the arm is elaborated once for each case of arm 2's
/// patterns, and each copy of the `match` captures the refined variables.
#[test]
fn an_overlapped_arm_with_a_lifted_match_is_skipped_with_its_reason() {
    with_session(|s| {
        generated(s, "explode.eq1");
        generated(s, "explode.eq2");
        let why = skipped(s, "explode.eq3");
        assert!(why.contains("refined"), "{why}");
    });
}

/// D2189: an equation that would take more than 64 hypotheses `x ≠ k`, one
/// per earlier number arm, isn't generated (its proof costs their count
/// squared), and says so; one with 64 is.
#[test]
fn a_catch_all_after_more_than_64_number_arms_is_skipped_with_its_reason() {
    let table = |name: &str, arms: usize| -> String {
        let rows: String = (0..arms).map(|i| format!("  | {i} => {i}\n")).collect();
        format!("def {name}: Nat → Nat\n{rows}  | _ => 0\n\n")
    };
    let source = format!(
        "import Std (Nat)\n\n{}{}",
        table("at64", 64),
        table("at65", 65)
    );
    with_source(source, |s| {
        let at64 = generated(s, "at64.eq65");
        assert!(at64.contains("(notArm64: x1 ≠ 63) → at64 x1 = 0"), "{at64}");
        generated(s, "at65.eq65");
        let why = skipped(s, "at65.eq66");
        assert!(why.contains("65 hypotheses") && why.contains("64"), "{why}");
    });
}

/// Every equation of the library, made (as `search` makes them): how many,
/// and why the others weren't. None is refused by the kernel but those
/// listed here (a library file's names the on-demand probe can't see).
/// Slow (every library file is loaded): `--run-ignored`.
#[test]
#[ignore]
fn the_librarys_equations() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let mut session = Session::eager();
            session.elab.generate_deferred_equations().unwrap();
            let g = &session.elab.globals;
            let made: Vec<&str> = g
                .defs
                .iter()
                .filter(|d| d.theorem && stitchwort_elab::is_equation_name(&d.name))
                .filter(|d| !d.name.contains('%'))
                .map(|d| &*d.name)
                .collect();
            let branches = made
                .iter()
                .filter(|n| {
                    let last = n.rsplit('.').next().unwrap_or("");
                    !(last.starts_with("eq") || last.starts_with("or"))
                })
                .count();
            eprintln!("made {} ({} branches)", made.len(), branches);
            let mut reasons: std::collections::BTreeMap<String, Vec<String>> = Default::default();
            for (id, s, why) in session.elab.equation_skips() {
                reasons
                    .entry(why.clone())
                    .or_default()
                    .push(format!("{}.{s}", g.defs[id.0].name));
            }
            for (why, names) in &reasons {
                eprintln!("{} skipped: {why}\n    {}", names.len(), names.join(" "));
            }
            let refused: Vec<&String> = reasons
                .iter()
                .filter(|(why, _)| why.contains("kernel refused") && !why.contains("unknown name"))
                .flat_map(|(_, n)| n)
                .collect();
            assert!(refused.is_empty(), "refused by the kernel: {refused:?}");
        })
        .unwrap()
        .join()
        .unwrap();
}

/// Stage 1b's constructs (§3.2): a branch of each kind of split in tail
/// position, under an arm or a `:=` body.
const BRANCHES: &str = r#"
import Std (Bool, Eq, Fin, List, Nat, Option, Void)

-- `if h: p` below a `:=` body, `decreasing`: `gcd.eq.ifTrue`. Its `else`
-- uses `h` (`%` takes a proof that `b ≠ 0`): skipped (D2180).
def gcd (a: Nat) (b: Nat): Nat
    decreasing b
:=
  if h: b = 0 then a else gcd b (a % b) [decreasing := Nat.modLess a b h]

-- D2186: the `else` of `fresh: b = False` is `notFresh: b = True`.
def countFresh: List Bool → Nat
  | Nil => 0
  | Cons b rest => if fresh: b = False then 1 + countFresh rest else countFresh rest

-- A `Bool` `if`: `h1: c = True`, `h1: c = False`.
def big: List Nat → Nat
  | Nil => 0
  | Cons x rest => if 4 ≤ x then x else big rest

-- §1.2's wall: a named `match` on a `Bool`, its branch using the equation.
type Big = { value: Nat, isBig: Nat.leq 10 value = True }

def firstBig: List Nat → Option Big
  | Nil => None
  | Cons x rest =>
    match big: Nat.leq 10 x with
      | True => Some ({ value = x, isBig = big })
      | False => firstBig rest

-- §3.5: the branch uses `h`, a comparison: one `J` along `Bool.uniqueEq`.
def check (n: Nat) (i: Nat): Option (Fin n) := if h: i < n then Some (Fin.ofNatLt n i h) else None

-- A `match` on a variable, compiled into the case tree: its patterns are
-- the left side's (the 1a leftover).
def takeFirst [a: Type] (xs: List a): Nat → List a
  | Zero => Nil
  | Succ k =>
    match xs with
      | Nil => Nil
      | Cons x rest => Cons x (takeFirst rest k)

-- A lifted `match` on an expression: `isSome`, `isNone`.
def headOr (d: Nat) (xs: List Nat): Nat :=
  match List.head xs with
    | Some x => x
    | None => d

-- A catch-all after an overlapping alternative: `notAlt1`; and a `match`
-- on the alternative's variable, compiled into the helper's tree.
def both (a: Option Nat) (b: Option Nat): Nat :=
  match (a, b) with
    | (Some x, Some y) => x + y
    | _ => 0

def firstTwo (xs: List Nat): Nat :=
  match List.head xs with
    | Some x =>
      match x with
        | 0 => 1
        | Succ n => n
    | None => 0
"#;

#[test]
fn branch_equations() {
    with_source(BRANCHES.to_string(), |s| {
        let cases = [
            (
                "gcd.eq.ifTrue",
                "(a: Nat) → (b: Nat) → (h: b = 0) → gcd a b = a",
            ),
            (
                "countFresh.eq2.ifTrue",
                "(b: Bool) → (rest: List Bool) → (fresh: b = False) → \
                 countFresh (Cons b rest) = 1 + countFresh rest",
            ),
            (
                "countFresh.eq2.ifFalse",
                "(b: Bool) → (rest: List Bool) → (notFresh: b = True) → \
                 countFresh (Cons b rest) = countFresh rest",
            ),
            // The printer shows `Nat.leq 4 x = True` as `3 < x`.
            (
                "big.eq2.ifTrue",
                "(x: Nat) → (rest: List Nat) → (h1: 3 < x) → big (Cons x rest) = x",
            ),
            (
                "big.eq2.ifFalse",
                "(x: Nat) → (rest: List Nat) → (h1: (3 < x) = False) → \
                 big (Cons x rest) = big rest",
            ),
            (
                "firstBig.eq2.true",
                "(x: Nat) → (rest: List Nat) → (big: 10 ≤ x) → \
                 firstBig (Cons x rest) = Some ({ value = x, isBig = big })",
            ),
            (
                "firstBig.eq2.false",
                "(x: Nat) → (rest: List Nat) → (big: (10 <= x) = False) → \
                 firstBig (Cons x rest) = firstBig rest",
            ),
            (
                "check.eq.ifTrue",
                "(n: Nat) → (i: Nat) → (h: i < n) → check n i = Some (Fin.ofNatLt n i h)",
            ),
            (
                "check.eq.ifFalse",
                "(n: Nat) → (i: Nat) → (notH: ¬(i < n)) → check n i = None",
            ),
            (
                "takeFirst.eq2.nil",
                "[a: Type] → (k: Nat) → takeFirst [] (Succ k) = []",
            ),
            (
                "takeFirst.eq2.cons",
                "[a: Type] → (k: Nat) → (x: a) → (rest: List a) → \
                 takeFirst (Cons x rest) (Succ k) = Cons x (takeFirst rest k)",
            ),
            (
                "headOr.eq.some",
                "(d: Nat) → (xs: List Nat) → (x: Nat) → (isSome: List.head xs = Some x) → \
                 headOr d xs = x",
            ),
            (
                "headOr.eq.none",
                "(d: Nat) → (xs: List Nat) → (isNone: List.head xs = None) → headOr d xs = d",
            ),
            (
                "both.eq.alt1",
                "(a: Option Nat) → (b: Option Nat) → (x: Nat) → (y: Nat) → \
                 (isAlt1: (a, b) = (Some x, Some y)) → both a b = x + y",
            ),
            (
                "both.eq.alt2",
                "(a: Option Nat) → (b: Option Nat) → \
                 (notAlt1: (x: Nat) → (y: Nat) → (a, b) ≠ (Some x, Some y)) → both a b = 0",
            ),
            (
                "firstTwo.eq.some.alt1",
                "(xs: List Nat) → (isSome: List.head xs = Some 0) → firstTwo xs = 1",
            ),
            (
                "firstTwo.eq.some.succ",
                "(xs: List Nat) → (n: Nat) → (isSome: List.head xs = Some (Succ n)) → \
                 firstTwo xs = n",
            ),
            (
                "firstTwo.eq.none",
                "(xs: List Nat) → (isNone: List.head xs = None) → firstTwo xs = 0",
            ),
        ];
        let mut wrong = Vec::new();
        for (name, want) in cases {
            let got = generated(s, name);
            if got != want {
                wrong.push(format!("{name}:\n  {got}"));
            }
        }
        assert!(wrong.is_empty(), "{}", wrong.join("\n"));
        let why = skipped(s, "gcd.eq.ifFalse");
        assert!(why.contains("D2180"), "{why}");
        let why = skipped(s, "takeFirst.eq2");
        assert!(why.contains("compiled into the case tree"), "{why}");
    });
}
