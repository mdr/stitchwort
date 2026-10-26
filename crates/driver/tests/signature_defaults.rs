//! Parameter defaults (docs/proposals/signature-defaults.md §9): the
//! stage-1 acceptance invariants, each a test.

use std::collections::{BTreeMap, BTreeSet};

use stitchwort_core::hash::{ContentHash, def_hash};
use stitchwort_core::{DefId, Term};
use stitchwort_driver::driver::Session;

const STACK: usize = 16 * 1024 * 1024;

fn show(h: stitchwort_core::budget::Result<Option<ContentHash>>) -> String {
    match h {
        Ok(Some(h)) => h.hex(),
        _ => "<none>".to_string(),
    }
}

/// Loads `text` in a fresh session, or gives its errors as `CODE: message`
/// lines.
fn load(text: &str) -> Result<Session, String> {
    let mut session = Session::eager_for_stack(STACK);
    match session.load("defaults.sw", text) {
        Ok(_) => Ok(session),
        Err(errors) => Err(errors
            .iter()
            .map(|e| format!("{}: {} {:?}", e.code, e.message, e.notes))
            .collect::<Vec<_>>()
            .join("\n")),
    }
}

/// The definitions `text` adds, by full name, with their hashes.
fn hashes(text: &str) -> BTreeMap<String, String> {
    let mut session = Session::eager_for_stack(STACK);
    let first = session.elab.globals.defs.len();
    if let Err(errors) = session.load("defaults.sw", text) {
        panic!("doesn't load: {errors:#?}");
    }
    let g = &session.elab.globals;
    (first..g.defs.len())
        .map(|i| (g.defs[i].path.to_string(), show(def_hash(g, DefId(i)))))
        .collect()
}

/// The definition called `name` (its short name).
fn def(session: &Session, name: &str) -> DefId {
    let g = &session.elab.globals;
    let i = g
        .defs
        .iter()
        .rposition(|d| d.name.as_ref() == name)
        .unwrap_or_else(|| panic!("`{name}` is defined"));
    DefId(i)
}

/// The errors of `text`, which must not load.
fn refused(text: &str) -> String {
    match load(text) {
        Ok(_) => panic!("loads: {text}"),
        Err(errors) => errors,
    }
}

fn hash_of(session: &Session, name: &str) -> String {
    show(def_hash(&session.elab.globals, def(session, name)))
}

fn body_of(session: &Session, name: &str) -> Term {
    let g = &session.elab.globals;
    (**g.def(def(session, name)).body().expect("checked")).clone()
}

/// `term` without source locations and type annotations, for comparing
/// lambdas and applications.
fn bare_term(term: &Term) -> Term {
    match term.strip_loc() {
        Term::Ann(inner, _) => bare_term(inner),
        Term::Lam(x, icit, body) => Term::Lam(x.clone(), *icit, bare_term(body).into()),
        Term::App(f, a, icit) => Term::App(bare_term(f).into(), bare_term(a).into(), *icit),
        other => other.clone(),
    }
}

/// The body of `name` as [`bare_term`] gives it, printed.
fn shown_body(session: &Session, name: &str) -> String {
    format!("{:?}", bare_term(&body_of(session, name)))
}

/// The names of the lambdas a definition's body starts with, through
/// annotations.
fn lambda_names(session: &Session, name: &str) -> Vec<String> {
    let mut term = body_of(session, name);
    let mut names = Vec::new();
    loop {
        match term.strip_loc() {
            Term::Lam(x, _, body) => {
                names.push(x.to_string());
                term = (**body).clone();
            }
            Term::Ann(inner, _) => term = (**inner).clone(),
            _ => return names,
        }
    }
}

const RANGE: &str = r#"
def range (start: Nat) (stop: Nat) (step: Nat DEFAULT): List Nat := [start, stop, step]
"#;

/// Invariant 1: a call that names every defaulted parameter is the term it
/// was before the defaults were added, with the same hash; so is the
/// definition itself, since its defaults are kept out of its hash.
#[test]
fn naming_every_default_keeps_the_hash() {
    let text = format!(
        "{RANGE}
def named: List Nat := range 0 10 (step := 2)
def partial: Nat -> List Nat := range 0 (step := 2)
def wrapped: List (List Nat) := [1, 2].map (stop => range 0 stop (step := 3))
"
    );
    let plain = hashes(&text.replace("DEFAULT", ""));
    let defaulted = hashes(&text.replace("DEFAULT", ":= 1"));
    for name in ["Main.range", "Main.named", "Main.partial", "Main.wrapped"] {
        assert!(plain.contains_key(name), "{name}: {plain:#?}");
        assert_eq!(plain.get(name), defaulted.get(name), "{name}");
    }
}

/// Invariant 2: adding a default leaves every positional call meaning what
/// it did, or makes it `E-DEFAULT-POSITIONAL`; never a silent change.
#[test]
fn adding_a_default_never_silently_moves_a_positional_argument() {
    let text = "
def add3 (a: Nat) (b: Nat DEFAULT) (c: Nat): Nat := a + 10 * b + 100 * c
def range (start: Nat) (stop: Nat) (step: Nat DEFAULT): List Nat := [start, stop, step]
def first: Nat := add3 1 2 3
def second: List Nat := range 0 10 2
";
    let plain = hashes(&text.replace("DEFAULT", ""));
    assert!(plain.contains_key("Main.first") && plain.contains_key("Main.second"));
    let errors = refused(&text.replace("DEFAULT", ":= 0"));
    let codes: Vec<&str> = errors
        .lines()
        .map(|l| l.split(':').next().unwrap())
        .collect();
    assert_eq!(
        codes,
        ["E-DEFAULT-POSITIONAL", "E-DEFAULT-POSITIONAL"],
        "{errors}"
    );
    // A call giving only required parameters positionally keeps its
    // arguments in their places.
    let text = "
def add3 (a: Nat) (b: Nat DEFAULT) (c: Nat): Nat := a + 10 * b + 100 * c
def onlyRequired: Nat := add3 1 (c := 3) (b := 2)
";
    let plain = hashes(&text.replace("DEFAULT", ""));
    let defaulted = hashes(&text.replace("DEFAULT", ":= 0"));
    assert_eq!(
        plain.get("Main.onlyRequired"),
        defaulted.get("Main.onlyRequired")
    );
}

/// Invariant 3: changing a default changes the hashes of exactly the calls
/// that leave it out, and of its helper.
#[test]
fn changing_a_default_changes_only_the_calls_that_leave_it_out() {
    let text = format!(
        "{RANGE}
def leavesOut: List Nat := range 0 10
def gives: List Nat := range 0 10 (step := 2)
def bare: Nat -> Nat -> List Nat := range
def mapped: List (List Nat) := [1, 2].map (range 0)
"
    );
    let before = hashes(&text.replace("DEFAULT", ":= 1"));
    let after = hashes(&text.replace("DEFAULT", ":= 5"));
    let changed: BTreeSet<&str> = before
        .iter()
        .filter(|(name, hash)| after.get(*name) != Some(hash))
        .map(|(name, _)| name.as_str())
        .collect();
    assert_eq!(
        changed,
        BTreeSet::from([
            "Main.range.step%default",
            "Main.leavesOut",
            "Main.bare",
            "Main.mapped"
        ]),
        "before: {before:#?}\nafter: {after:#?}"
    );
}

/// Invariant 4: a written argument that a default uses is computed once:
/// bound by a `let` unless it's a variable or a literal (§6.5).
#[test]
fn a_written_argument_a_default_uses_runs_once() {
    let text = r#"
def padded (width: Nat) (total: Nat := width + 2): Nat := total
def computed (n: Nat): Nat := padded (n * 3)
def variable (n: Nat): Nat := padded n
def literal: Nat := padded 4
def unused (n: Nat): Nat := padded (n * 3) (total := 1)
"#;
    let session = load(text).unwrap();
    let has_let = |name: &str| {
        body_of(&session, name)
            .subterms()
            .any(|(t, _)| matches!(t, Term::Let(..)))
    };
    assert!(has_let("computed"));
    assert!(!has_let("variable"));
    assert!(!has_let("literal"));
    assert!(!has_let("unused"));
}

/// Invariant 5: a default that assumes an earlier default is refused, and
/// leaving a parameter out commits to its default.
#[test]
fn a_default_must_work_for_any_earlier_values() {
    let assumed = refused("def board (size: Nat := 8) (square: size = 8 := rfl): Nat := size");
    assert!(
        assumed.starts_with("E-REFL") && assumed.contains("must work for any values"),
        "{assumed}"
    );
    let committed = refused(
        "import Std (Vec)
def sized (n: Nat := 3) (xs: Vec Nat n): Nat := n
def two: Vec Nat 2 := Vec.replicate 2 0
def size: Nat := sized two
",
    );
    assert!(committed.starts_with("E-TYPE-MISMATCH"), "{committed}");
}

/// Invariant 6: `xs.map f`, `let g := f`, `x.f`, `.f` and `x |> f` with a
/// defaulted `f` give a function of the required parameters only, with
/// their names.
#[test]
fn function_values_take_only_the_required_parameters() {
    let text = r#"
type Clip = { length: Nat }
def Clip.cut (clip: Clip) (from: Nat) (by: Nat := 1): Nat := clip.length - from - by
def range (start: Nat) (stop: Nat) (step: Nat := 1): List Nat := [start, stop, step]
def clip: Clip := { length = 10 }

def bare: Nat -> Nat -> List Nat := range
def viaLet: Nat -> Nat -> List Nat :=
  let g := range
  g
def dotted: Nat -> Nat := clip.cut
def section: Clip -> Nat -> Nat := .cut
def piped: Nat -> Nat := clip |> Clip.cut
def mapped: List Nat := [1, 2].map clip.cut

test "values" :=
  bare 0 10 == [0, 10, 1] && viaLet 0 10 == [0, 10, 1] && dotted 2 == 7 &&
    section clip 2 == 7 && piped 2 == 7 && mapped == [8, 7]
"#;
    let session = load(text).unwrap();
    assert_eq!(lambda_names(&session, "bare"), ["start", "stop"]);
    assert_eq!(lambda_names(&session, "dotted"), ["from"]);
    assert_eq!(lambda_names(&session, "piped"), ["from"]);
    assert_eq!(
        lambda_names(&session, "section").last().map(String::as_str),
        Some("from")
    );
}

/// Invariant 7: `scaler 5 3` is `E-DEFAULT-POSITIONAL`; `(scaler 5) 3` and
/// `scaler 5 (factor := 3)` check and differ.
#[test]
fn a_bracketed_call_is_finished() {
    let scaler =
        "def scaler (base: Nat) (factor: Nat := 1): Nat -> Nat := x => base * factor + x\n";
    let positional = refused(&format!("{scaler}def bad: Nat := scaler 5 3\n"));
    assert!(
        positional.starts_with("E-DEFAULT-POSITIONAL"),
        "{positional}"
    );
    let session = load(&format!(
        "{scaler}def applied: Nat := (scaler 5) 3
def named: Nat -> Nat := scaler 5 (factor := 3)
test \"they differ\" := applied == 8 && named 0 == 15
"
    ))
    .unwrap();
    assert_ne!(
        shown_body(&session, "applied"),
        shown_body(&session, "named")
    );
    // Without defaults, brackets change nothing.
    let plain = "def add (x: Nat) (y: Nat): Nat := x + 10 * y\n";
    let bracketed = hashes(&format!("{plain}def call: Nat := (add 1) (y := 2)\n"));
    let flat = hashes(&format!("{plain}def call: Nat := add 1 (y := 2)\n"));
    assert_eq!(bracketed.get("Main.call"), flat.get("Main.call"));
}

/// Invariant 9: defaults are committed before the arguments are
/// elaborated.
#[test]
fn defaults_are_committed_before_the_arguments() {
    let header = "import Std (Vec)
def sized (n: Nat := 3) (xs: Vec Nat n): Nat := n
def pair (n: Nat := 3) (xs: Vec Nat n) (ys: Vec Nat n): Nat := n
def two: Vec Nat 2 := Vec.replicate 2 0
def three: Vec Nat 3 := Vec.replicate 3 0
";
    let sized = refused(&format!("{header}def bad: Nat := sized two\n"));
    assert!(
        sized.starts_with("E-TYPE-MISMATCH")
            && sized.contains("`n` is left out, so it is its default value, `3`"),
        "{sized}"
    );
    let paired = refused(&format!(
        "{header}def bad: Vec Nat 3 -> Nat := pair (ys := two)\n"
    ));
    assert!(
        paired.starts_with("E-TYPE-MISMATCH") && paired.contains("`n` is left out"),
        "{paired}"
    );
    let session = load(&format!(
        "{header}def named: Nat := sized (n := 2) two
def defaulted: Nat := sized three
def ofXs: Vec Nat 2 -> Nat := pair (n := 2) (ys := two)
"
    ))
    .unwrap();
    assert_eq!(lambda_names(&session, "ofXs"), ["xs"]);
}

/// Invariant 10: function values. With `def f (a: Nat) (b: Nat := 7)
/// (c: Nat)`, the bare `f` is the call with `b`'s helper filled, of type
/// `(a: Nat) -> (c: Nat) -> Nat`: `a`, left out before `b`, is a lambda,
/// and `c`, after it, stays to currying (§6.1 rule 3), so it is
/// definitionally equal to `(a: Nat) (c: Nat) => f a c` by eta. Giving `b`'s
/// value by name is definitionally equal but another term; keeping `b`
/// open is another type. With `range`, where the left-out parameter comes
/// before the default, `range 0` and `(stop: Nat) => range 0 stop` are one
/// term but for the annotation a call that makes a lambda gets, which the
/// hash sees.
#[test]
fn function_values_with_defaults() {
    let text = r#"
def f (a: Nat) (b: Nat := 7) (c: Nat): Nat := a + 10 * b + 100 * c
def range (start: Nat) (stop: Nat) (step: Nat := 1): List Nat := [start, stop, step]

def bare: (a: Nat) -> (c: Nat) -> Nat := f
def written: (a: Nat) -> (c: Nat) -> Nat := (a: Nat) (c: Nat) => f a c
def givenByName: (a: Nat) -> (c: Nat) -> Nat := (a: Nat) (c: Nat) => f a (b := 7) c
def keptOpen: (a: Nat) -> (b: Nat) -> (c: Nat) -> Nat := (a: Nat) (b: Nat) (c: Nat) => f a (b := b) c

theorem bareIsWritten: bare = written := rfl
theorem bareIsGivenByName: bare = givenByName := rfl

def rangeFrom0: (stop: Nat) -> List Nat := range 0
def rangeWritten: (stop: Nat) -> List Nat := (stop: Nat) => range 0 stop
def rangeOpen: (stop: Nat) -> (step: Nat) -> List Nat := (stop: Nat) (step: Nat) => range 0 stop (step := step)

theorem rangeFrom0IsWritten: rangeFrom0 = rangeWritten := rfl
"#;
    let session = load(text).unwrap();
    assert_eq!(lambda_names(&session, "bare"), ["a"]);
    assert_eq!(lambda_names(&session, "written"), ["a", "c"]);
    assert_ne!(
        hash_of(&session, "written"),
        hash_of(&session, "givenByName")
    );
    assert_eq!(lambda_names(&session, "keptOpen"), ["a", "b", "c"]);
    assert_eq!(
        shown_body(&session, "rangeFrom0"),
        shown_body(&session, "rangeWritten")
    );
    assert!(matches!(
        body_of(&session, "rangeFrom0").strip_loc(),
        Term::Ann(..)
    ));
    assert_ne!(
        hash_of(&session, "rangeFrom0"),
        hash_of(&session, "rangeWritten")
    );
    assert_eq!(lambda_names(&session, "rangeFrom0"), ["stop"]);
    // The bare name's body calls `b`'s helper.
    let g = &session.elab.globals;
    let helper = def(&session, "f.b%default");
    assert!(
        body_of(&session, "bare")
            .subterms()
            .any(|(t, _)| matches!(t, Term::Def(d) if *d == helper)),
        "{:?}",
        g.def(def(&session, "bare")).body()
    );
}
