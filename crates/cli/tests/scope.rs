//! Whole-module scope (docs/proposals/mutual-recursion.md §8.1): every
//! top-level name is visible throughout its module, declarations are checked
//! in dependency order (in source order where that allows), and definitions
//! that refer to each other are checked as a group.

use stitchwort_cli::driver::{Cache, Outcome, Session};
use stitchwort_core::hash::def_hash;
use stitchwort_core::{DefId, Limits};
use stitchwort_syntax::{Diagnostic, Severity};

fn load(text: &str) -> (Session, Result<(), Vec<Diagnostic>>) {
    let mut session = Session::new();
    let result = session.load("test.sw", text).map(|_| ());
    (session, result)
}

fn codes(diagnostics: &[Diagnostic]) -> Vec<&'static str> {
    diagnostics.iter().map(|d| d.code).collect()
}

/// The definitions added after the prelude, in the kernel's order.
fn new_defs(session: &Session) -> Vec<String> {
    let prelude = Session::new().elab.globals.defs.len();
    session.elab.globals.defs[prelude..]
        .iter()
        .map(|d| d.name.to_string())
        .collect()
}

fn def_named(session: &Session, name: &str) -> DefId {
    let defs = &session.elab.globals.defs;
    DefId(defs.iter().rposition(|d| &*d.name == name).expect(name))
}

/// How many definitions are in `name`'s group.
fn group_size(session: &Session, name: &str) -> usize {
    let def = session.elab.globals.def(def_named(session, name));
    def.group.as_ref().map_or(0, |g| g.len())
}

#[test]
fn declarations_are_checked_after_what_they_use() {
    // `a` uses `c`, below it; `b` uses nothing. Of those ready, the earliest
    // in the source goes first: `b`, then `c`, then `a`.
    let (session, result) =
        load("a : Nat\na = c + 1\n\nb : Nat\nb = 2\n\nc : Nat\nc = 3\n\ntest \"a\" = a == 4\n");
    result.unwrap();
    assert_eq!(new_defs(&session), ["b", "c", "a", "test \"a\""]);
    // With no forward references, that's source order.
    let (session, result) = load("x : Nat\nx = 1\n\ny : Nat\ny = x\n\nz : Nat\nz = 0\n");
    result.unwrap();
    assert_eq!(new_defs(&session), ["x", "y", "z"]);
}

#[test]
fn errors_and_tests_are_reported_in_source_order() {
    // `x` is checked after `y`, but its error comes first.
    let (_, result) = load("x : Nat\nx = y + True\n\ny : Nat\ny = Zero Zero\n");
    let errors = result.unwrap_err();
    assert_eq!(errors.len(), 2, "{errors:#?}");
    assert!(
        errors[0].primary_span().unwrap().start < errors[1].primary_span().unwrap().start,
        "{errors:#?}"
    );
    // The first test is checked last (it waits for `f`), but runs first.
    let (session, result) =
        load("test \"uses f\" = f 1 == 2\ntest \"plain\" = True\n\nf : Nat -> Nat\nf n = n + 1\n");
    result.unwrap();
    let names: Vec<String> = session
        .run_tests(&Cache::disabled())
        .into_iter()
        .map(|t| {
            assert_eq!(t.outcome, Outcome::Passed);
            t.name
        })
        .collect();
    assert_eq!(names, ["uses f", "plain"]);
}

#[test]
fn local_names_make_no_dependencies() {
    // Each of `f`'s local variables has the name of a definition that calls
    // `f`. If they counted as references, `f` would be in a group with them.
    let (session, result) = load(
        "f : [g : Type] -> Nat -> Nat\n\
         f n =\n  let k = n\n  applyTo (\\h -> h) k\n\n\
         applyTo : (Nat -> Nat) -> Nat -> Nat\napplyTo f x = f x\n\n\
         g : Nat -> Nat\ng n = f [g := Nat] n\n\n\
         h : Nat -> Nat\nh n = f [g := Nat] n\n\n\
         k : Nat -> Nat\nk n = f [g := Nat] n\n\n\
         m : Nat -> Nat\nm g = g\n\n\
         p : Nat -> Nat\np 0 = m 0\np (Succ m) = f [g := Nat] m\n",
    );
    result.unwrap();
    for name in ["f", "g", "h", "k", "m", "p"] {
        assert_eq!(group_size(&session, name), 1, "{name}");
    }
    // But a real cycle is one group.
    let (session, result) = load(
        "isEven : Nat -> Bool\nisEven 0 = True\nisEven (Succ n) = isOdd n\n\n\
         isOdd : Nat -> Bool\nisOdd 0 = False\nisOdd (Succ n) = isEven n\n",
    );
    result.unwrap();
    assert_eq!(group_size(&session, "isEven"), 2);
}

#[test]
fn a_failed_signature_doesnt_cascade() {
    // `g` uses `f`, whose signature fails: only `f`'s error is reported, not
    // an "unknown name" for `f`.
    let (_, result) = load("g : Nat\ng = f 1\n\nf : Nat -> Nonsense\nf n = n\n");
    assert_eq!(codes(&result.unwrap_err()), ["E-UNKNOWN-NAME"]);
}

#[test]
fn a_duplicate_is_reported_and_the_first_definition_kept() {
    let (session, result) =
        load("use : Nat\nuse = twice\n\ntwice : Nat\ntwice = 2\n\ntwice : Nat\ntwice = 3\n");
    let errors = result.unwrap_err();
    assert_eq!(codes(&errors), ["E-DUPLICATE"]);
    let g = &session.elab.globals;
    let _op = g.budget.operation(Limits::default());
    let use_id = def_named(&session, "use");
    let value = stitchwort_core::value::eval(g, &[], &stitchwort_core::Term::Def(use_id)).unwrap();
    assert_eq!(session.elab.show(&value), "2");
}

#[test]
fn a_module_name_takes_priority_over_a_type_variable_with_a_warning() {
    let size = "size : List a -> Nat\nsize Nil = 0\nsize (Cons _ xs) = Succ (size xs)\n\n";
    let (session, result) = load(&format!("{size}a : Type\na = Nat\n"));
    result.unwrap();
    let [warning] = &session.warnings[..] else {
        panic!("{:#?}", session.warnings);
    };
    assert_eq!(warning.severity, Severity::Warning);
    assert_eq!(warning.code, "W-MODULE-NAME");
    // Both sites: the use in the signature, and the definition.
    assert_eq!(warning.labels.len(), 2);
    assert!(warning.notes[0].contains("[a : Type] ->"), "{warning:?}");
    // With an explicit binder, it's a type variable, and there's no warning.
    let explicit = "size : [a : Type] -> List a -> Nat\nsize Nil = 0\n\
                    size (Cons _ xs) = Succ (size xs)\n\na : Type\na = Nat\n";
    let (session, result) = load(explicit);
    result.unwrap();
    assert!(session.warnings.is_empty(), "{:#?}", session.warnings);
    // If the signature then fails, its error says the same.
    let (_, result) = load(&format!("{size}a : Nat\na = 0\n"));
    let errors = result.unwrap_err();
    let error = errors
        .iter()
        .find(|d| d.severity == Severity::Error)
        .expect("an error");
    assert!(
        error.notes.iter().any(|n| n.contains("[a : Type] ->")),
        "{errors:#?}"
    );
}

#[test]
fn abilities_are_ordered_by_where_they_are_written() {
    // `Foo` uses `Bar`, written below it, so it's checked after `Baz`; but
    // rows still list `Foo` before `Baz`, as they're written, so `f` is the
    // same as in a module where nothing is checked out of order.
    let module = |bar_first: bool| {
        let bar = "type Bar : Type =\n  | MkBar\n\n";
        let rest = "ability Foo where\n  foo : Bar -> {Foo} ()\n\n\
                    ability Baz where\n  baz : () -> {Baz} ()\n\n\
                    f : () -> {Baz, Foo} ()\nf u = foo MkBar\n";
        let text = if bar_first {
            format!("{bar}{rest}")
        } else {
            format!("{rest}\n{bar}")
        };
        let (session, result) = load(&text);
        result.unwrap();
        let g = &session.elab.globals;
        let _op = g.budget.operation(Limits::default());
        def_hash(g, def_named(&session, "f")).unwrap().unwrap()
    };
    assert_eq!(module(true), module(false));
}
