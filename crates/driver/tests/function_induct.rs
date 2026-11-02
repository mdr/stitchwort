//! Functional induction, `f.induct` (docs/proposals/function-equations.md
//! §5, stage 2a): the statements generated for each kind of recursion and
//! split, in the unfolding form with a fixed prefix and cases named after
//! the equations, and what isn't generated, with the reason.

use stitchwort_core::{Name, Term};
use stitchwort_driver::driver::Session;

const SOURCE: &str = r#"
import Std (Bool, Eq, List, Nat, Option, Void)

def len: List Nat → Nat
  | Nil => 0
  | Cons x xs => Succ (len xs)

-- A fixed prefix (`k`) and a `Bool` `if`.
def countAbove (k: Nat): List Nat → Nat
  | Nil => 0
  | Cons x xs => if Nat.leq k x then Succ (countAbove k xs) else countAbove k xs

-- A named `match` on a `Bool`.
def firstBig: List Nat → Option Nat
  | Nil => None
  | Cons x rest =>
    match big: Nat.leq 10 x with
      | True => Some x
      | False => firstBig rest

-- D2186: the `else` of `fresh: b = False` is `notFresh: b = True`.
def countFresh: List Bool → Nat
  | Nil => 0
  | Cons b rest => if fresh: b = False then 1 + countFresh rest else countFresh rest

-- `decreasing`, nested `if h:`.
def down (n: Nat) (acc: Nat): Nat
    decreasing n
:=
  if h: n = 0 then acc
  else if small: n < 5 then down (n - 1) (acc + 1) [decreasing := omega]
  else down (n - 2) (acc + 2) [decreasing := omega]

-- A lifted `match` on an expression, with a field.
def lastOr (d: Nat): List Nat → Nat
  | Nil => d
  | Cons x rest =>
    match List.head rest with
      | Some y => lastOr y rest
      | None => x

-- Two calls, and an overlap hypothesis the proof establishes.
type Number =
  | Regular (value: Nat)
  | Pair (left: Number) (right: Number)

def ex (depth: Nat): Number → Nat
  | Regular _ => 0
  | Pair (Regular a) (Regular b) => if 4 ≤ depth then a + b else 0
  | Pair left right => ex (depth + 1) left + ex (depth + 1) right

-- An overlap that differs below the top (`[number]` against `Cons a (Cons
-- b c)`).
def rating (choose: List Bool → Bool): (columns: Nat) → List (List Bool) → Option (List Bool)
  | _, [number] => Some number
  | Zero, _ => None
  | Succ later, numbers => rating choose later numbers |> Option.map (Cons True)

-- Not generated: a call under a binder whose argument is the bound
-- variable; a case whose equation isn't (`gcd.eq.ifFalse`, D2180).
def lengths: Nat → List Nat → List Nat
  | Zero, xs => xs
  | Succ n, xs => List.map xs (x => List.length (lengths n [x]))

def gcd (a: Nat) (b: Nat): Nat
    decreasing b
:=
  if h: b = 0 then a else gcd b (a % b) [decreasing := Nat.modLess a b h]

-- A nested call: the inner call's `ih` first.
def ack: Nat → Nat → Nat
  | Zero, j => Succ j
  | Succ k, Zero => ack k 1
  | Succ k, Succ j => ack k (ack (Succ k) j)

-- Not recursive: no `induct`.
def double (n: Nat): Nat := n + n
"#;

/// `ty`, a closed `Π` type, with every binder's name shown.
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

fn with_source(source: String, f: impl FnOnce(&Session) + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            let mut session = Session::new();
            if let Err(errors) = session.load("induct.sw", &source) {
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
fn each_kind_of_recursion_and_split() {
    with_source(SOURCE.to_string(), |s| {
        // (The printer leaves out the names of binders inside a binder's
        // type: `notArm2`, `ih`.)
        let cases = [
            (
                "len.induct",
                "(motive: List Nat → Nat → Prop) → (eq1: motive [] 0) → \
                 (eq2: (x: Nat) → (xs: List Nat) → motive xs (len xs) → \
                 motive (Cons x xs) (Succ (len xs))) → (x: List Nat) → motive x (len x)",
            ),
            (
                "countAbove.induct",
                "(k: Nat) → (motive: List Nat → Nat → Prop) → (eq1: motive [] 0) → \
                 (eq2IfTrue: (x: Nat) → (xs: List Nat) → k ≤ x → motive xs (countAbove k xs) → \
                 motive (Cons x xs) (Succ (countAbove k xs))) → \
                 (eq2IfFalse: (x: Nat) → (xs: List Nat) → (k <= x) = False → \
                 motive xs (countAbove k xs) → motive (Cons x xs) (countAbove k xs)) → \
                 (x: List Nat) → motive x (countAbove k x)",
            ),
            (
                "firstBig.induct",
                "(motive: List Nat → Option Nat → Prop) → (eq1: motive [] None) → \
                 (eq2True: (x: Nat) → (rest: List Nat) → 10 ≤ x → motive (Cons x rest) (Some x)) → \
                 (eq2False: (x: Nat) → (rest: List Nat) → (10 <= x) = False → \
                 motive rest (firstBig rest) → motive (Cons x rest) (firstBig rest)) → \
                 (x: List Nat) → motive x (firstBig x)",
            ),
            (
                "countFresh.induct",
                "(motive: List Bool → Nat → Prop) → (eq1: motive [] 0) → \
                 (eq2IfTrue: (b: Bool) → (rest: List Bool) → b = False → \
                 motive rest (countFresh rest) → motive (Cons b rest) (1 + countFresh rest)) → \
                 (eq2IfFalse: (b: Bool) → (rest: List Bool) → b = True → \
                 motive rest (countFresh rest) → motive (Cons b rest) (countFresh rest)) → \
                 (x: List Bool) → motive x (countFresh x)",
            ),
            (
                "down.induct",
                "(motive: Nat → Nat → Nat → Prop) → \
                 (eqIfTrue: (n: Nat) → (acc: Nat) → n = 0 → motive n acc acc) → \
                 (eqIfFalseIfTrue: (n: Nat) → (acc: Nat) → n ≠ 0 → n < 5 → \
                 motive (n - 1) (acc + 1) (down (n - 1) (acc + 1)) → \
                 motive n acc (down (n - 1) (acc + 1))) → \
                 (eqIfFalseIfFalse: (n: Nat) → (acc: Nat) → n ≠ 0 → ¬(n < 5) → \
                 motive (n - 2) (acc + 2) (down (n - 2) (acc + 2)) → \
                 motive n acc (down (n - 2) (acc + 2))) → \
                 (n: Nat) → (acc: Nat) → motive n acc (down n acc)",
            ),
            (
                "lastOr.induct",
                "(motive: Nat → List Nat → Nat → Prop) → (eq1: (d: Nat) → motive d [] d) → \
                 (eq2Some: (d: Nat) → (x: Nat) → (rest: List Nat) → (y: Nat) → \
                 List.head rest = Some y → motive y rest (lastOr y rest) → \
                 motive d (Cons x rest) (lastOr y rest)) → \
                 (eq2None: (d: Nat) → (x: Nat) → (rest: List Nat) → List.head rest = None → \
                 motive d (Cons x rest) x) → \
                 (d: Nat) → (x: List Nat) → motive d x (lastOr d x)",
            ),
            (
                "ex.induct",
                "(motive: Nat → Number → Nat → Prop) → \
                 (eq1: (depth: Nat) → (value: Nat) → motive depth (Regular value) 0) → \
                 (eq2IfTrue: (depth: Nat) → (a: Nat) → (b: Nat) → 3 < depth → \
                 motive depth (Pair (Regular a) (Regular b)) (a + b)) → \
                 (eq2IfFalse: (depth: Nat) → (a: Nat) → (b: Nat) → (3 < depth) = False → \
                 motive depth (Pair (Regular a) (Regular b)) 0) → \
                 (eq3: (depth: Nat) → (left: Number) → (right: Number) → \
                 ((a: Nat) → (b: Nat) → left = Regular a → right ≠ Regular b) → \
                 motive (depth + 1) left (ex (depth + 1) left) → \
                 motive (depth + 1) right (ex (depth + 1) right) → \
                 motive depth (Pair left right) (ex (depth + 1) left + ex (depth + 1) right)) → \
                 (depth: Nat) → (x: Number) → motive depth x (ex depth x)",
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
        // An overlap below the top of the pattern is established too.
        generated(s, "rating.induct");
        let ack = generated(s, "ack.induct");
        assert!(
            ack.contains(
                "(eq3: (k: Nat) → (j: Nat) → motive (Succ k) j (ack (Succ k) j) → \
                 motive k (ack (Succ k) j) (ack k (ack (Succ k) j)) → \
                 motive (Succ k) (Succ j) (ack k (ack (Succ k) j)))"
            ),
            "{ack}"
        );
        let why = skipped(s, "lengths.induct");
        assert!(why.contains("binder"), "{why}");
        let why = skipped(s, "gcd.induct");
        assert!(
            why.contains("gcd.eq.ifFalse") && why.contains("D2180"),
            "{why}"
        );
        // Not recursive: neither made nor recorded.
        let g = &s.elab.globals;
        assert!(!g.defs.iter().any(|d| &*d.name == "double.induct"));
        assert!(
            !s.elab
                .equation_skips()
                .iter()
                .any(|(id, x, _)| x == "induct" && &*g.defs[id.0].name == "double")
        );
    });
}

/// A lifted `match` with a nested pattern (`Some (MkPair v next)`, SW-1073):
/// its alternative's variables are the pattern's, and the equation is
/// `e = Some (MkPair v next)`. The library's `List.unfold` is one.
#[test]
fn a_nested_pattern_in_a_lifted_match() {
    let source = r#"
import Std (Eq, List, Nat, Option, Pair, Void)

def deep: List (Pair (Pair Nat Nat) Nat) → Nat
  | Nil => 0
  | Cons x rest =>
    match List.head rest with
      | None => 0
      | Some (MkPair (MkPair a b) c) => a + b + c + deep rest

theorem unfoldNone (seed: s) (step: s → Option (Pair a s)) (measure: s → Nat)
    (shrinks: (x: s) → (y: s) → (v: a) → step x = Some (MkPair v y) → measure y < measure x):
    step seed = None → List.unfold seed step measure shrinks = [] :=
  List.unfold.induct (seed step measure shrinks result => step seed = None → result = [])
    (seed step measure shrinks found same => rfl)
    (seed step measure shrinks v next found ih same =>
      Void.exfalso (Option.noneNotSome (MkPair v next) (rewrite same at found in found)))
    seed step measure shrinks
"#;
    with_source(source.to_string(), |s| {
        let deep = generated(s, "deep.induct");
        assert!(
            deep.contains(
                "(eq2Alt2: (x: ((Nat, Nat), Nat)) → (rest: List ((Nat, Nat), Nat)) → \
                 (a: Nat) → (b: Nat) → (c: Nat) → List.head rest = Some ((a, b), c) → \
                 motive rest (deep rest) → motive (Cons x rest) (a + b + c + deep rest))"
            ),
            "{deep}"
        );
        let unfold = generated(s, "List.unfold.induct");
        let shrinks =
            "(shrinks: (x: s) → (y: s) → (v: a) → step x = Some (v, y) → measure y < measure x)";
        let want = format!(
            "[s: Type] → [a: Type] → (motive: s → (step: s → Option (a, s)) → \
             (measure: s → Nat) → ((x: s) → (y: s) → (v: a) → step x = Some (v, y) → \
             measure y < measure x) → List a → Prop) → \
             (eqNone: (seed: s) → (step: s → Option (a, s)) → (measure: s → Nat) → {shrinks} → \
             step seed = None → motive seed step measure shrinks []) → \
             (eqAlt2: (seed: s) → (step: s → Option (a, s)) → (measure: s → Nat) → {shrinks} → \
             (v: a) → (next: s) → step seed = Some (v, next) → \
             motive next step measure shrinks (List.unfold next step measure shrinks) → \
             motive seed step measure shrinks (Cons v (List.unfold next step measure shrinks))) → \
             (seed: s) → (step: s → Option (a, s)) → (measure: s → Nat) → {shrinks} → \
             motive seed step measure shrinks (List.unfold seed step measure shrinks)"
        );
        assert_eq!(unfold, want);
    });
}

/// Using them: a theorem by each, the motive written out; `E-NO-EQUATION`
/// with the reason for one that isn't generated, a note for a definition
/// that isn't recursive, and the name reserved.
#[test]
fn using_them_and_their_names() {
    let used = format!(
        "{SOURCE}\n{}",
        r#"
theorem downGe (n: Nat) (acc: Nat): acc ≤ down n acc :=
  down.induct (n acc r => acc ≤ r)
    (n acc h => omega)
    (n acc h small ih => omega)
    (n acc h small ih => omega)
    n acc

theorem countAboveLe (k: Nat) (xs: List Nat): countAbove k xs ≤ List.length xs :=
  countAbove.induct k (xs r => r ≤ List.length xs)
    omega
    (x xs h ih => omega)
    (x xs h ih => omega)
    xs

theorem firstBigBig (xs: List Nat) (y: Nat): firstBig xs = Some y → Nat.leq 10 y = True :=
  firstBig.induct (xs r => r = Some y → Nat.leq 10 y = True)
    (e => cases)
    (x rest big e => cases)
    (x rest big ih e => ih e)
    xs
"#
    );
    with_source(used, |_| {});
    let wrong = format!(
        "{SOURCE}\n{}",
        r#"
theorem a (a: Nat) (b: Nat): gcd a b = gcd a b := gcd.induct (a b r => r = r) _ _ a b

theorem b (n: Nat): double n = double n := double.induct (n r => r = r) n

def Count: List Nat → Nat
  | Nil => 0
  | Cons x xs => Succ (Count xs)

theorem Count.induct: Nat := 0
"#
    );
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            let mut session = Session::new();
            let errors = session.load("induct.sw", &wrong).expect_err("they fail");
            let mut codes: Vec<&str> = errors.iter().map(|d| d.code).collect();
            codes.sort_unstable();
            assert_eq!(
                codes,
                ["E-DUPLICATE", "E-NO-EQUATION", "E-UNKNOWN-NAME"],
                "{errors:#?}"
            );
            let find = |code: &str| errors.iter().find(|d| d.code == code).unwrap();
            let duplicate = find("E-DUPLICATE");
            assert!(
                duplicate.message.contains("functional induction"),
                "{duplicate:#?}"
            );
            let no_eq = find("E-NO-EQUATION");
            assert!(
                no_eq.labels.iter().any(|l| l.message.contains("D2180")),
                "{no_eq:#?}"
            );
            let unknown = find("E-UNKNOWN-NAME");
            assert!(
                unknown
                    .notes
                    .iter()
                    .any(|n| n.contains("doesn't call itself")),
                "{unknown:#?}"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

/// Every `f.induct` of the library, made (as `search` makes them): how
/// many, and why the others weren't. None is refused by the kernel. Slow
/// (every library file is loaded): `--run-ignored`.
#[test]
#[ignore]
fn the_librarys_inducts() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let mut session = Session::eager();
            session.elab.generate_deferred_equations().unwrap();
            report(&session, |_| true);
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A project's `f.induct`s, for the project `INDUCT_PROJECT` names
/// (relative to the repository's root; `aoc` if unset). Slow:
/// `--run-ignored`.
#[test]
#[ignore]
fn a_projects_inducts() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let project = std::env::var("INDUCT_PROJECT").unwrap_or_else(|_| "aoc".to_string());
            let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../..")
                .join(&project);
            let name = root.file_name().unwrap().to_string_lossy().to_string();
            let files = stitchwort_driver::project::DiskFiles { root };
            let mut session = Session::eager_for_stack(256 << 20);
            let target = stitchwort_driver::project::Target::Everything;
            if let Err(errors) = session.load_project(&files, &name, &target) {
                panic!("{project} doesn't load: {errors:#?}");
            }
            report(&session, |d| !d.path.starts_with("Std."));
        })
        .unwrap()
        .join()
        .unwrap();
}

/// How many `f.induct`s of the definitions `own` picks were made, and why
/// the others weren't; none refused by the kernel.
fn report(session: &Session, own: impl Fn(&stitchwort_core::globals::Def) -> bool) {
    let g = &session.elab.globals;
    let made = (g.defs.iter())
        .filter(|d| own(d) && d.theorem && stitchwort_elab::is_function_induct(g, &d.name))
        .count();
    eprintln!("made {made} `f.induct`");
    let mut reasons: std::collections::BTreeMap<String, Vec<String>> = Default::default();
    for (id, s, why) in session.elab.equation_skips() {
        if s == "induct" && own(&g.defs[id.0]) {
            reasons
                .entry(why.clone())
                .or_default()
                .push(g.defs[id.0].name.to_string());
        }
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
}
