//! Generated equations (docs/proposals/function-equations.md, stage 1a):
//! the statements generated for the note's worked examples (§3.2) are the
//! ones it shows, binder names included, and what isn't generated is
//! recorded with its reason.

use crate::common::{BIG_STACK, STACK};
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
fn statement(g: &stitchwort_core::Ev, ty: &Term) -> String {
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
        .stack_size(STACK)
        .spawn(move || {
            let mut session = Session::for_stack(STACK);
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
    let g = &session.elab.ev();
    let def = g
        .env
        .defs()
        .iter()
        .rev()
        .find(|d| &**d.name() == name)
        .unwrap_or_else(|| panic!("`{name}` isn't generated"));
    assert!(def.theorem(), "`{name}` is a theorem");
    statement(g, def.ty())
}

fn skipped(session: &Session, name: &str) -> String {
    let g = &session.elab.ev();
    session
        .elab
        .equation_skips()
        .iter()
        .find(|(id, s, _)| format!("{}.{s}", g.env.defs()[id.0].name()) == name)
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
             (notArm2: ∀ (a b: Nat) => left = Regular a → right ≠ Regular b) → \
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
/// Its branches are read from every case and stated in the arm's variables
/// (SW-1071), as §3.2 states them.
#[test]
fn an_overlapped_arms_branches_are_read_from_each_case() {
    with_session(|s| {
        generated(s, "explode.eq1");
        generated(s, "explode.eq2");
        let why = skipped(s, "explode.eq3");
        assert!(why.contains("refined") && why.contains("branches"), "{why}");
        let not_arm2 = "(notArm2: ∀ (a b: Nat) => left = Regular a → right ≠ Regular b)";
        assert_eq!(
            generated(s, "explode.eq3.some"),
            format!(
                "(depth: Nat) → (left: Number) → (right: Number) → {not_arm2} → (n: Nat) → \
                 (isSome: explode (depth + 1) left = Some n) → explode depth (Pair left right) = Some n"
            )
        );
        assert_eq!(
            generated(s, "explode.eq3.none"),
            format!(
                "(depth: Nat) → (left: Number) → (right: Number) → {not_arm2} → \
                 (isNone: explode (depth + 1) left = None) → \
                 explode depth (Pair left right) = explode (depth + 1) right"
            )
        );
    });
}

/// SW-1069: a `match` below a lifted `match`'s alternative, compiled into
/// its helper's tree, on a variable bound further up is stated where that
/// variable is bound: a header parameter in the left side, an earlier
/// alternative's variable in that alternative's pattern.
#[test]
fn a_match_below_a_lifted_alternative_refines_where_its_variable_is_bound() {
    let source = r#"
import Std (Bool, Char, List, Nat, Option, Void)

def repair (budget: Nat) (bits: Nat): Option Nat :=
  match List.head [bits] with
    | Some b =>
      match budget with
        | Zero => None
        | Succ fewer => Some (fewer + b)
    | None => None

def deeper: List Nat → Nat
  | Nil => 0
  | Cons x rest =>
    match List.head rest with
      | Some y =>
        match rest with
          | Nil => x
          | Cons z more => y + z
      | None => 1

def ofName (name: List Char): Nat :=
  match List.head name with
    | Some first =>
      match List.length name with
        | 3 =>
          match first with
            | 'x' => 1
            | _ => 2
        | _ => 3
    | None => 4
"#;
    with_source(source.to_string(), |s| {
        let cases = [
            (
                "repair.eq.some.zero",
                "(bits: Nat) → (b: Nat) → (isSome: [bits].head = Some b) → repair 0 bits = None",
            ),
            (
                "repair.eq.some.succ",
                "(bits: Nat) → (fewer: Nat) → (b: Nat) → (isSome: [bits].head = Some b) → \
                 repair (Succ fewer) bits = Some (fewer + b)",
            ),
            (
                "deeper.eq2.some.cons",
                "(x: Nat) → (z: Nat) → (more: List Nat) → (y: Nat) → \
                 (isSome: [z, ..more].head = Some y) → deeper [x, z, ..more] = y + z",
            ),
            (
                "deeper.eq2.some.nil",
                "(x: Nat) → (y: Nat) → (isSome: [].head = Some y) → deeper [x] = x",
            ),
            (
                "ofName.eq.some.alt1.alt1",
                "(name: List Char) → (isSome: name.head = Some 'x') → \
                 (isAlt1: name.length = 3) → ofName name = 1",
            ),
            (
                "ofName.eq.some.alt1.alt2",
                "(name: List Char) → (first: Char) → (isSome: name.head = Some first) → \
                 (isAlt1: name.length = 3) → (notListed: first ∉ ['x']) → ofName name = 2",
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
/// and why the others weren't. None is refused by the kernel, and none
/// fails to compile again: each is made in its own file's scope (SW-1068).
/// Slow (every library file is loaded): `--run-ignored`.
#[test]
#[ignore]
fn the_librarys_equations() {
    std::thread::Builder::new()
        .stack_size(BIG_STACK)
        .spawn(|| {
            let mut session = Session::eager_for_stack(BIG_STACK);
            session.elab.generate_deferred_equations().unwrap();
            let g = &session.elab.ev();
            let made: Vec<&str> = g
                .env
                .defs()
                .iter()
                .filter(|d| d.theorem() && stitchwort_elab::is_equation_name(d.name()))
                .filter(|d| !d.name().contains('%'))
                .map(|d| &**d.name())
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
                    .push(format!("{}.{s}", g.env.defs()[id.0].name()));
            }
            for (why, names) in &reasons {
                eprintln!("{} skipped: {why}\n    {}", names.len(), names.join(" "));
            }
            let refused: Vec<&String> = reasons
                .iter()
                .filter(|(why, _)| {
                    why.contains("kernel refused") || why.contains("couldn't be compiled again")
                })
                .flat_map(|(_, n)| n)
                .collect();
            assert!(
                refused.is_empty(),
                "refused or not compiled again: {refused:?}"
            );
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
-- uses `h` only where `%` takes a proof that `b ≠ 0`, which nothing computes
-- on, so `gcd.eq.ifFalse` is made too (function-equations.md §3.5).
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
                 countFresh [b, ..rest] = 1 + countFresh rest",
            ),
            (
                "countFresh.eq2.ifFalse",
                "(b: Bool) → (rest: List Bool) → (notFresh: b) → \
                 countFresh [b, ..rest] = countFresh rest",
            ),
            // The printer shows `Nat.leq 4 x = True` as `3 < x`.
            (
                "big.eq2.ifTrue",
                "(x: Nat) → (rest: List Nat) → (h1: 3 < x) → big [x, ..rest] = x",
            ),
            (
                "big.eq2.ifFalse",
                "(x: Nat) → (rest: List Nat) → (h1: (3 < x) = False) → \
                 big [x, ..rest] = big rest",
            ),
            (
                "firstBig.eq2.true",
                "(x: Nat) → (rest: List Nat) → (big: 10 ≤ x) → \
                 firstBig [x, ..rest] = Some { value = x, isBig = big }",
            ),
            (
                "firstBig.eq2.false",
                "(x: Nat) → (rest: List Nat) → (big: (10 <= x) = False) → \
                 firstBig [x, ..rest] = firstBig rest",
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
                 takeFirst [x, ..rest] (Succ k) = [x, ..takeFirst rest k]",
            ),
            (
                "headOr.eq.some",
                "(d: Nat) → (xs: List Nat) → (x: Nat) → (isSome: xs.head = Some x) → \
                 headOr d xs = x",
            ),
            (
                "headOr.eq.none",
                "(d: Nat) → (xs: List Nat) → (isNone: xs.head = None) → headOr d xs = d",
            ),
            (
                "both.eq.alt1",
                "(a: Option Nat) → (b: Option Nat) → (x: Nat) → (y: Nat) → \
                 (isAlt1: (a, b) = (Some x, Some y)) → both a b = x + y",
            ),
            (
                "both.eq.alt2",
                "(a: Option Nat) → (b: Option Nat) → \
                 (notAlt1: ∀ (x y: Nat) => (a, b) ≠ (Some x, Some y)) → both a b = 0",
            ),
            (
                "firstTwo.eq.some.alt1",
                "(xs: List Nat) → (isSome: xs.head = Some 0) → firstTwo xs = 1",
            ),
            (
                "firstTwo.eq.some.succ",
                "(xs: List Nat) → (n: Nat) → (isSome: xs.head = Some (Succ n)) → \
                 firstTwo xs = n",
            ),
            (
                "firstTwo.eq.none",
                "(xs: List Nat) → (isNone: xs.head = None) → firstTwo xs = 0",
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
        let got = generated(s, "gcd.eq.ifFalse");
        assert!(got.contains("gcd a b = gcd b (a % b)"), "{got}");
        let why = skipped(s, "takeFirst.eq2");
        assert!(why.contains("compiled into the case tree"), "{why}");
    });
}

/// A destructuring `let` before a tail `match` or `if` is a `let` for tail
/// position too (§3.1): a record or tuple pattern binds projections, and the
/// splits below it get the branch equations they have after an ordinary
/// `let`. The two theorems use a generated equation by applying it, so the
/// statements are usable in a proof, not just listed.
const DESTRUCTURING_LETS: &str = r#"
import Std (Bool, Nat, Option, Pair)

type Cell = { row: Nat, column: Nat }

def cellAhead (cell: Cell): Option Nat :=
  let { row, column } := cell
  match row with
    | Zero => if column == 0 then None else Some column
    | Succ n => Some (n + column)

def pairAhead (p: (Nat, Nat)): Nat :=
  let (a, b) := p
  match a with
    | Zero => b
    | Succ n => n + b

type Flagged = { flag: Bool, value: Nat }

def flagged (f: Flagged): Nat :=
  let { flag, value } := f
  if flag then value else 0

def ctorAhead (p: Pair Nat Nat): Nat :=
  let MkPair a b := p
  match a with
    | Zero => b
    | Succ n => n + b

theorem pairAheadSucc (a: Nat) (b: Nat): pairAhead (Succ a, b) = a + b :=
  pairAhead.eq.succ (Succ a, b) a rfl

theorem flaggedTrue (n: Nat): flagged { flag = True, value = n } = n :=
  flagged.eq.ifTrue { flag = True, value = n } rfl
"#;

#[test]
fn a_destructuring_let_before_a_tail_split_gets_its_branches() {
    with_source(DESTRUCTURING_LETS.to_string(), |s| {
        let cases = [
            (
                "cellAhead.eq.zero.ifTrue",
                "(cell: Cell) → (isZero: cell.row = 0) → \
                 (h1: (x => (x.decEq 0).holds) cell.column) → \
                 cellAhead cell = None",
            ),
            (
                "cellAhead.eq.zero.ifFalse",
                "(cell: Cell) → (isZero: cell.row = 0) → \
                 (h1: (x => (x.decEq 0).holds) cell.column = False) → \
                 cellAhead cell = Some cell.column",
            ),
            (
                "cellAhead.eq.succ",
                "(cell: Cell) → (n: Nat) → (isSucc: cell.row = Succ n) → \
                 cellAhead cell = Some (n + cell.column)",
            ),
            (
                "pairAhead.eq.zero",
                "(p: (Nat, Nat)) → (isZero: p.fst = 0) → pairAhead p = p.snd",
            ),
            (
                "pairAhead.eq.succ",
                "(p: (Nat, Nat)) → (n: Nat) → (isSucc: p.fst = Succ n) → \
                 pairAhead p = n + p.snd",
            ),
            (
                "flagged.eq.ifTrue",
                "(f: Flagged) → (h1: f.flag) → flagged f = f.value",
            ),
            (
                "flagged.eq.ifFalse",
                "(f: Flagged) → (h1: f.flag = False) → flagged f = 0",
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
        // A constructor pattern `let` is compiled into the case tree, not
        // bound as projections, so it's skipped with a reason that says so.
        let why = skipped(s, "ctorAhead.eq.zero");
        assert!(
            why.contains("destructuring `let`") && why.contains("tuple or record"),
            "{why}"
        );
    });
}

/// SW-1074: a `match` on several expressions, `match a, b with | p, q`,
/// is stated as the same `match` on their tuple is, `match (a, b) with |
/// (p, q)`: one hypothesis `isAlt1: (a, b) = (p, q)` per alternative, a
/// `_` being `fst` or `snd` as the tuple's component is; an alternative of
/// catch-alls only takes the earlier ones' hypotheses, about the
/// expressions themselves. The theorems at the end use them.
const SEVERAL: &str = r#"
import Std (Bool, Fin, Nat, Option)

def two (k: Nat) (a: Option Nat) (b: Option Nat): Nat :=
  if k == 0 then 0 else
  match a, b with
    | Some x, Some y => x + y
    | Some x, None => x
    | None, Some y => y
    | None, None => k

def twoPair (k: Nat) (a: Option Nat) (b: Option Nat): Nat :=
  if k == 0 then 0 else
  match (a, b) with
    | (Some x, Some y) => x + y
    | (Some x, None) => x
    | (None, Some y) => y
    | (None, None) => k

def three (k: Nat) (a: Option Nat) (b: Bool) (c: Nat): Nat :=
  if k == 0 then 0 else
  match a, b, c with
    | Some x, True, _ => x
    | _, False, Zero => 1
    | None, _, Succ n => n
    | _, _, _ => 2

def threePair (k: Nat) (a: Option Nat) (b: Bool) (c: Nat): Nat :=
  if k == 0 then 0 else
  match (a, b, c) with
    | (Some x, True, _) => x
    | (_, False, Zero) => 1
    | (None, _, Succ n) => n
    | _ => 2

def computed (k: Nat) (a: Option Nat): Nat :=
  match a, k + 1 with
    | Some x, Succ y => x + y
    | _, _ => k

-- The columns are the lifter's, not read off names: a parameter called `s`
-- (the name the helper gives an expression it matches) matched second.
def isEven (x: Nat): Bool := x % 2 == 0

def swapped (s: Bool) (x: Nat): Nat :=
  match isEven x, s with
    | True, False => 1
    | False, True => 2
    | _, _ => 0

-- A copied parameter named `s` whose type mentions the expression matched.
def succOf (n: Nat): Nat := n + 1

def dependentCopy (n: Nat) (s: Fin (succOf n)) (b: Bool): Nat :=
  match succOf n, b with
    | Succ k, True => k + Fin.toNat s
    | _, _ => 0

-- A `let` both captured and matched by name.
def letMatched (x: Nat) (b: Bool): Nat :=
  let y := x + 1
  match y, b with
    | Succ k, True => k + y
    | _, _ => y

-- Named equations on several expressions aren't stated.
def namedBoth (a: Nat) (b: Nat): Nat :=
  if a == 0 then 0 else
  match h1: a, h2: b with
    | Succ k, Zero => k
    | _, _ => 1

-- Recursive, with a call in an alternative: `f.induct` isn't made.
def walk (k: Nat): List (Option Nat) → Nat
  | Nil => 0
  | Cons x rest =>
    match x, k + 1 with
      | Some a, Succ b => a + b + walk k rest
      | _, _ => walk k rest

theorem twoBoth (x: Nat) (y: Nat): two 1 (Some x) (Some y) = x + y :=
  two.eq.ifFalse.alt1 1 (Some x) (Some y) rfl x y rfl

theorem threeNone (a: Option Nat) (b: Bool) (c: Nat) (h: three 1 a b c = 7) (n: Nat) (ha: a = None) (hc: c = Succ n): n = 7 :=
  rewrite three.eq.ifFalse.alt3 1 a b c rfl b n (rewrite ha in rewrite hc in rfl) at h in h

theorem threeOther (a: Option Nat) (c: Nat) (ha: a = None) (hc: c = 0): three 1 a True c = 2 :=
  three.eq.ifFalse.alt4 1 a True c rfl (x => e => rewrite ha at e in cases) (e => cases) (n => e => rewrite hc in cases)
"#;

#[test]
fn a_match_on_several_expressions_is_stated_as_on_their_tuple() {
    with_source(SEVERAL.to_string(), |s| {
        let not_zero = "(k: Nat) → (a: Option Nat) → (b: Option Nat) → \
                        (h1: (k.decEq 0).holds = False)";
        let three_not_zero = "(k: Nat) → (a: Option Nat) → (b: Bool) → (c: Nat) → \
                              (h1: (k.decEq 0).holds = False)";
        let cases = [
            (
                "two.eq.ifFalse.alt1",
                format!(
                    "{not_zero} → (x: Nat) → (y: Nat) → (isAlt1: (a, b) = (Some x, Some y)) → \
                     two k a b = x + y"
                ),
            ),
            (
                "two.eq.ifFalse.alt4",
                format!("{not_zero} → (isAlt4: (a, b) = (None, None)) → two k a b = k"),
            ),
            (
                "three.eq.ifFalse.alt1",
                format!(
                    "{three_not_zero} → (x: Nat) → (snd: Nat) → \
                     (isAlt1: (a, b, c) = (Some x, True, snd)) → three k a b c = x"
                ),
            ),
            (
                "three.eq.ifFalse.alt2",
                format!(
                    "{three_not_zero} → (fst: Option Nat) → \
                     (isAlt2: (a, b, c) = (fst, False, 0)) → three k a b c = 1"
                ),
            ),
            (
                "three.eq.ifFalse.alt3",
                format!(
                    "{three_not_zero} → (fst: Bool) → (n: Nat) → \
                     (isAlt3: (a, b, c) = (None, fst, Succ n)) → three k a b c = n"
                ),
            ),
            // Every pattern a catch-all: the earlier alternatives' hypotheses
            // about the expressions, one equation each (`match (a, b, c)
            // with | _` states them on the tuple instead).
            (
                "three.eq.ifFalse.alt4",
                format!(
                    "{three_not_zero} → (notAlt1: ∀ (x: Nat) => a = Some x → ¬b) → \
                     (notAlt2: b = False → c ≠ 0) → (notAlt3: ∀ (n: Nat) => a = None → c ≠ Succ n) → \
                     three k a b c = 2"
                ),
            ),
            (
                "swapped.eq.alt1",
                "(s: Bool) → (x: Nat) → (isAlt1: (isEven x, s) = (True, False)) → swapped s x = 1"
                    .to_string(),
            ),
            (
                "swapped.eq.alt2",
                "(s: Bool) → (x: Nat) → (isAlt2: (isEven x, s) = (False, True)) → swapped s x = 2"
                    .to_string(),
            ),
            (
                "letMatched.eq.alt1",
                "(x: Nat) → (b: Bool) → (k: Nat) → (isAlt1: (x + 1, b) = (Succ k, True)) → \
                 letMatched x b = k + Succ k"
                    .to_string(),
            ),
            (
                "computed.eq.alt1",
                "(k: Nat) → (a: Option Nat) → (x: Nat) → (y: Nat) → \
                 (isAlt1: (a, k + 1) = (Some x, Succ y)) → computed k a = x + y"
                    .to_string(),
            ),
            (
                "computed.eq.alt2",
                "(k: Nat) → (a: Option Nat) → \
                 (notAlt1: ∀ (x y: Nat) => a = Some x → k + 1 ≠ Succ y) → computed k a = k"
                    .to_string(),
            ),
        ];
        let mut wrong = Vec::new();
        for (name, want) in cases {
            let got = generated(s, name);
            if got != want {
                wrong.push(format!("{name}:\n  {got}"));
            }
        }
        let why = skipped(s, "dependentCopy.eq.alt1");
        assert!(why.contains("types mention what it matches"), "{why}");
        let why = skipped(s, "namedBoth.eq.ifFalse.alt1");
        assert!(why.contains("naming one's equation"), "{why}");
        let why = skipped(s, "walk.induct");
        assert!(why.contains("on several expressions"), "{why}");
        // The same statements as the `match` on the tuple's, but where
        // every pattern is a catch-all.
        let same = [("two", "twoPair", 1..=4), ("three", "threePair", 1..=3)];
        for (several, pair, alts) in same {
            for i in alts {
                let got = generated(s, &format!("{several}.eq.ifFalse.alt{i}"));
                let want = generated(s, &format!("{pair}.eq.ifFalse.alt{i}"))
                    .replace(&format!("{pair} k"), &format!("{several} k"));
                if got != want {
                    wrong.push(format!(
                        "{several}.eq.ifFalse.alt{i} isn't {pair}'s:\n  {got}\n  {want}"
                    ));
                }
            }
        }
        assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    });
}

/// §3.4: where stepping through a lifted `match` by hand fails (§1.2), the
/// error names the branch equations that state its steps.
#[test]
fn the_walls_errors_name_the_branch_equations() {
    let source = r#"
import Std (Bool, Eq, List, Nat, Option, Void)

type Big = { value: Nat, isBig: Nat.leq 10 value = True }

def firstBig: List Nat → Option Big
  | Nil => None
  | Cons x rest =>
    match big: Nat.leq 10 x with
      | True => Some ({ value = x, isBig = big })
      | False => firstBig rest

theorem byRewrite (x: Nat) (rest: List Nat) (h: Nat.leq 10 x = True):
    firstBig (Cons x rest) = Some ({ value = x, isBig = h }) :=
  rewrite h in rfl

theorem byMatch (x: Nat) (rest: List Nat) (h: Nat.leq 10 x = True):
    firstBig (Cons x rest) = Some ({ value = x, isBig = h }) :=
  match e: Nat.leq 10 x with
    | True => rfl
    | False => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym e) h))

theorem byRfl (x: Nat) (rest: List Nat) (h: Nat.leq 10 x = True):
    firstBig (Cons x rest) = Some ({ value = x, isBig = h }) :=
  rfl
"#;
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let mut session = Session::for_stack(STACK);
            let errors = session
                .load("wall.sw", source)
                .expect_err("the three proofs fail");
            let mut codes: Vec<&str> = errors.iter().map(|d| d.code).collect();
            codes.sort_unstable();
            assert_eq!(codes, ["E-MATCH-MOTIVE", "E-REFL", "E-REWRITE-MOTIVE"]);
            for d in &errors {
                assert!(
                    d.notes
                        .iter()
                        .any(|n| n.contains("`firstBig.eq2.true`")
                            && n.contains("`firstBig.eq2.false`")),
                    "{}: {:#?}",
                    d.code,
                    d.notes
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A library file whose definitions' constructors only it imports, as
/// std/Map/Raw.sw imports `Map.Tree`'s `Tip` and `Bin` (SW-1068). With
/// `own_proof`, its own proof names `Box.Tree.count.eq1`, so the equations
/// are made while it loads.
fn box_library(own_proof: bool) -> String {
    let proof = if own_proof {
        "\ntheorem Box.Tree.countLeaf: Box.Tree.count Leaf = 0 := Box.Tree.count.eq1\n"
    } else {
        ""
    };
    format!(
        r#"--| Trees.

import Box.Tree (Leaf, Node)

--| A tree.
type Box.Tree: Type =
  | Leaf
  | Node (left: Box.Tree) (right: Box.Tree)

--| Whether it's a leaf.
def Box.Tree.isLeaf: Box.Tree → Bool
  | Leaf => True
  | Node _ _ => False

--| Its leaves, counting a leaf on the left once.
def Box.Tree.count: Box.Tree → Nat
  | Leaf => 0
  | Node l r => if Box.Tree.isLeaf l then 1 + Box.Tree.count r else Box.Tree.count l + Box.Tree.count r
{proof}"#
    )
}

/// `Box.Tree.count`'s equations, each with its statement and hash.
fn box_equations(session: &Session) -> Vec<(String, String, [u8; 32])> {
    let g = &session.elab.ev();
    ["eq1", "eq2.ifTrue", "eq2.ifFalse"]
        .iter()
        .map(|s| {
            let name = format!("Box.Tree.count.{s}");
            let id = (0..g.env.defs().len())
                .map(stitchwort_core::DefId)
                .find(|id| **g.def(*id).name() == *name)
                .unwrap_or_else(|| panic!("`{name}` isn't generated"));
            let hash = stitchwort_core::hash::def_hash(g, id)
                .unwrap()
                .expect("final");
            (name, statement(g, g.def(id).ty()), hash.0)
        })
        .collect()
}

fn in_thread(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

/// SW-1068: a library definition's equations are made in its own file's
/// scope, so they come out the same, statement and hash, whether made
/// while the file loads (its own proof names one), by `search` (every
/// put-off equation), or by a program naming one, though the program
/// doesn't import the constructors the arms name.
#[test]
fn a_library_equation_is_the_same_however_it_is_made() {
    in_thread(|| {
        let program =
            "import Std (Box, Nat)\n\ndef leaves (t: Box.Tree): Nat := Box.Tree.count t\n";
        // While the file loads.
        let library = box_library(true);
        let session =
            Session::with_library_files(&[("Box/Box.sw", &library)], true, false).unwrap();
        let eager = box_equations(&session);
        // By `search`.
        let library = box_library(false);
        let mut session =
            Session::with_library_files(&[("Box/Box.sw", &library)], false, false).unwrap();
        session.load("leaves.sw", program).unwrap();
        session.elab.generate_deferred_equations().unwrap();
        let searched = box_equations(&session);
        // Named by a program.
        let mut session =
            Session::with_library_files(&[("Box/Box.sw", &library)], false, false).unwrap();
        let named = format!(
            "{program}\ntheorem leftLeaf (r: Box.Tree):\n    \
             Box.Tree.count (Box.Tree.Node Box.Tree.Leaf r) = 1 + Box.Tree.count r :=\n  \
             Box.Tree.count.eq2.ifTrue Box.Tree.Leaf r rfl\n"
        );
        if let Err(errors) = session.load("named.sw", &named) {
            panic!("doesn't load: {errors:#?}");
        }
        let by_name = box_equations(&session);
        assert_eq!(eager[0].1, "Box.Tree.count Leaf = 0");
        assert_eq!(eager, searched, "made while loading, and by `search`");
        assert_eq!(
            eager, by_name,
            "made while loading, and by a program naming one"
        );
    });
}

/// SW-1068: `Map.Tree`'s functions, whose arms name `Tip` and `Bin` (which
/// only std/Map/Raw.sw imports), get their equations from `search`, as
/// every other definition of a loaded file does; before, they were
/// skipped ("unknown name `Tip`").
#[test]
fn search_makes_the_equations_of_a_file_with_its_own_constructors() {
    in_thread(|| {
        let mut session = Session::for_stack(STACK);
        let program = "import Std (Map, Nat)\n\ndef one: Map Nat Nat := Map.singleton 1 1\n";
        if let Err(errors) = session.load("map.sw", program) {
            panic!("doesn't load: {errors:#?}");
        }
        session.elab.generate_deferred_equations().unwrap();
        let tip = generated(&session, "Map.Tree.size.eq1");
        assert_eq!(tip, "[k: Type] → [v: Type] → Map.Tree.size Tip = 0");
        generated(&session, "Map.Tree.singleL.eq2");
        let g = &session.elab.ev();
        let unseen: Vec<String> = (session.elab.equation_skips().iter())
            .filter(|(_, _, why)| why.contains("couldn't be compiled again"))
            .map(|(id, s, why)| format!("{}.{s}: {why}", g.env.defs()[id.0].name()))
            .collect();
        assert!(unseen.is_empty(), "{unseen:#?}");
    });
}

/// Every equation of a project (`EQUATIONS_PROJECT`, a directory relative
/// to the repository's root; `aoc` if unset), made as `check` makes them:
/// how many, and why the others weren't. None is refused by the kernel.
/// Slow (the whole project is checked): `--run-ignored`.
#[test]
#[ignore]
fn a_projects_equations() {
    std::thread::Builder::new()
        .stack_size(BIG_STACK)
        .spawn(|| {
            let project = std::env::var("EQUATIONS_PROJECT").unwrap_or_else(|_| "aoc".to_string());
            let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../..")
                .join(&project);
            let name = root.file_name().unwrap().to_string_lossy().to_string();
            let files = stitchwort_driver::project::DiskFiles { root };
            let mut session = Session::eager_for_stack(BIG_STACK);
            let first = session.elab.kernel.env.defs().len();
            if let Err(errors) = session.load_project(
                &files,
                &name,
                &stitchwort_driver::project::Target::Everything,
            ) {
                panic!("{project} doesn't load: {errors:#?}");
            }
            let g = &session.elab.ev();
            let made: Vec<&str> = g.env.defs()[first..]
                .iter()
                .filter(|d| d.theorem() && stitchwort_elab::is_equation_name(d.name()))
                .filter(|d| !d.name().contains('%') && !d.name().starts_with("Std."))
                .map(|d| &**d.name())
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
                if id.0 < first {
                    continue;
                }
                reasons
                    .entry(why.clone())
                    .or_default()
                    .push(format!("{}.{s}", g.env.defs()[id.0].name()));
            }
            for (why, names) in &reasons {
                eprintln!("{} skipped: {why}\n    {}", names.len(), names.join(" "));
            }
            let refused: Vec<&String> = reasons
                .iter()
                .filter(|(why, _)| why.contains("kernel refused"))
                .flat_map(|(_, n)| n)
                .collect();
            assert!(refused.is_empty(), "refused by the kernel: {refused:?}");
        })
        .unwrap()
        .join()
        .unwrap();
}

/// SW-1182: a lifted `match h: e` that generalises `e` in the goal has
/// alternatives whose right sides have the type at their pattern (`Decidable.yes rfl:
/// Decidable (0 = 0)`), not at `e`, so its branch equations are skipped with
/// the reason; they were stated ill-typed and refused by the kernel. One
/// whose result type doesn't mention `e` still gets its equations.
#[test]
fn a_generalising_matchs_branches_are_skipped_not_refused() {
    let source = r#"
import List (length)
import Std (Bool, Decidable, Eq, Nat)

def lenZero (xs: List Nat): Decidable (xs.length = 0) := match h: xs.length with
  | Zero => Decidable.yes rfl
  | Succ k => Decidable.no (e => Nat.equalFalse (Succ k) 0 rfl e)

def keep (p: Prop): p → Bool
  | _ => True

def usesH (xs: List Nat): Bool := match h: xs.length with
  | Zero => keep (xs.length = 0) h
  | Succ k => keep (xs.length = Succ k) h
"#;
    with_source(source.to_string(), |s| {
        let g = &s.elab.ev();
        let refused: Vec<String> = (s.elab.equation_skips().iter())
            .filter(|(_, _, why)| why.contains("kernel refused"))
            .map(|(id, suffix, why)| format!("{}.{suffix}: {why}", g.env.defs()[id.0].name()))
            .collect();
        assert!(refused.is_empty(), "{refused:#?}");
        for name in ["lenZero.eq.zero", "lenZero.eq.succ"] {
            assert!(
                skipped(s, name).contains("result type mentions what it matches"),
                "{name}: {}",
                skipped(s, name)
            );
        }
        generated(s, "usesH.eq.zero");
        generated(s, "usesH.eq.succ");
    });
}

/// Equations of library functions are made on demand, and come out the
/// same whoever asks (SW-1068, SW-2275): from a program that names them
/// (glued, as the default is), or from the driver outside any declaration,
/// as `search` and `doc` do (the machine's switch is off there). Each is
/// compared by content hash. (Today no std equation happens to differ
/// glued and unglued, so this guards the property rather than a known
/// failure.)
#[test]
fn library_equations_come_out_the_same_whoever_asks() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let imports = "import Std (List, Nat)\n\n";
            let mut driven = Session::for_stack(STACK);
            driven.elab.options.glue = false;
            driven
                .load(
                    "driven.sw",
                    &format!("{imports}def one: List Nat := [1].filter (n => n == 0)\n"),
                )
                .unwrap();
            driven.elab.generate_deferred_equations().unwrap();
            let names: Vec<String> = driven
                .elab
                .ev()
                .env
                .defs()
                .iter()
                .map(|d| d.name().to_string())
                .filter(|n| {
                    n.rsplit(".eq").next().is_some_and(|s| {
                        n.contains(".eq") && s.starts_with(|c: char| c.is_ascii_digit())
                    })
                })
                .collect();
            assert!(names.len() > 100, "{} equations", names.len());

            let mut asked = Session::for_stack(STACK);
            for (i, name) in names.iter().enumerate() {
                let source = format!("{imports}def use{i}: _ := {name}\n");
                let _ = asked.load(&format!("asked{i}.sw"), &source);
            }

            let hashed = |s: &Session, name: &str| {
                let g = &s.elab.ev();
                let (i, _) =
                    (g.env.defs().iter().enumerate().rev()).find(|(_, d)| &**d.name() == name)?;
                let hash = stitchwort_core::hash::def_hash(g, stitchwort_core::DefId(i));
                Some(format!("{:?}", hash.unwrap()))
            };
            let mut compared = 0;
            for name in names {
                let Some(theirs) = hashed(&asked, &name) else {
                    continue;
                };
                compared += 1;
                assert_eq!(Some(theirs), hashed(&driven, &name), "{name}");
            }
            assert!(compared > 100, "only {compared} compared");
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A `()` arm has no equation of its own, and the arms around it keep
/// theirs, numbered by their place among all the arms; theorems use them
/// by applying them. A `match` below an arm with an absurd alternative
/// gets the equations of its other alternatives too, and the absurd one
/// is recorded as skipped.
const ABSURD_ARMS: &str = r#"
import Std (Nat)

type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

type Fin: Nat → Type =
  | FZero: Fin (Succ n)
  | FSucc (i: Fin n): Fin (Succ n)

def at: (v: Vec Nat n) → Fin n → Nat
  | VCons x _, FZero => x
  | VNil, ()
  | VCons _ xs, FSucc j => at xs j

def pick (d: Nat): (v: Vec Nat n) → Fin n → Nat
  | VCons x xs, i =>
    match i with
      | FZero => x
      | FSucc j => pick d xs j
  | VNil, i =>
    match i with
      | ()

theorem atZero (x: Nat) (xs: Vec Nat n): at (VCons x xs) FZero = x := at.eq1 n x xs

theorem atSucc (x: Nat) (xs: Vec Nat n) (j: Fin n): at (VCons x xs) (FSucc j) = at xs j :=
  at.eq3 n x xs j
"#;

#[test]
fn an_absurd_arm_leaves_the_equations_around_it_numbered_by_their_place() {
    with_source(ABSURD_ARMS.to_string(), |s| {
        let eq1 = generated(s, "at.eq1");
        assert!(eq1.contains("at (VCons n x xs) (FZero n) = x"), "{eq1}");
        let eq3 = generated(s, "at.eq3");
        assert!(
            eq3.contains("at (VCons n x xs) (FSucc n j) = at xs j"),
            "{eq3}"
        );
        let made = |name: &str| s.elab.ev().env.defs().iter().any(|d| &**d.name() == name);
        assert!(!made("at.eq2"), "an absurd arm has no equation");
        assert!(made("pick.eq1.fZero") && made("pick.eq1.fSucc"));
        let why = skipped(s, "pick.eq2.alt1");
        assert!(why.contains("no right side"), "{why}");
    });
}
