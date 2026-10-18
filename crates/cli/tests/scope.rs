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
    let (session, result) = load(
        "def a : Nat := c + 1\n\ndef b : Nat := 2\n\ndef c : Nat := 3\n\ntest \"a\" := a == 4\n",
    );
    result.unwrap();
    assert_eq!(new_defs(&session), ["b", "c", "a", "test \"a\""]);
    // With no forward references, that's source order.
    let (session, result) = load("def x : Nat := 1\n\ndef y : Nat := x\n\ndef z : Nat := 0\n");
    result.unwrap();
    assert_eq!(new_defs(&session), ["x", "y", "z"]);
}

#[test]
fn errors_and_tests_are_reported_in_source_order() {
    // `x` is checked after `y`, but its error comes first.
    let (_, result) = load("def x : Nat := y + True\n\ndef y : Nat := Zero Zero\n");
    let errors = result.unwrap_err();
    assert_eq!(errors.len(), 2, "{errors:#?}");
    assert!(
        errors[0].primary_span().unwrap().start < errors[1].primary_span().unwrap().start,
        "{errors:#?}"
    );
    // The first test is checked last (it waits for `f`), but runs first.
    let (session, result) = load(
        "test \"uses f\" := f 1 == 2\ntest \"plain\" := True\n\ndef f (n : Nat) : Nat := n + 1\n",
    );
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
        "def f [g : Type] (n : Nat) : Nat :=\n  \
         let k := n\n  \
         applyTo (\\h => h) k\n\n\
         def applyTo (f : Nat -> Nat) (x : Nat) : Nat := f x\n\n\
         def g (n : Nat) : Nat := f [g := Nat] n\n\n\
         def h (n : Nat) : Nat := f [g := Nat] n\n\n\
         def k (n : Nat) : Nat := f [g := Nat] n\n\n\
         def m (g : Nat) : Nat := g\n\n\
         def p : Nat -> Nat\n  \
         | 0 => m 0\n  \
         | Succ m => f [g := Nat] m\n",
    );
    result.unwrap();
    for name in ["f", "g", "h", "k", "m", "p"] {
        assert_eq!(group_size(&session, name), 1, "{name}");
    }
    // But a real cycle is one group.
    let (session, result) = load(
        "def isEven : Nat -> Bool\n  \
         | 0 => True\n  \
         | Succ n => isOdd n\n\n\
         def isOdd : Nat -> Bool\n  \
         | 0 => False\n  \
         | Succ n => isEven n\n",
    );
    result.unwrap();
    assert_eq!(group_size(&session, "isEven"), 2);
}

#[test]
fn a_failed_signature_doesnt_cascade() {
    // `g` uses `f`, whose signature fails: only `f`'s error is reported, not
    // an "unknown name" for `f`.
    let (_, result) = load("def g : Nat := f 1\n\ndef f (n : Nat) : Nonsense := n\n");
    assert_eq!(codes(&result.unwrap_err()), ["E-UNKNOWN-NAME"]);
}

#[test]
fn a_duplicate_is_reported_and_the_first_definition_kept() {
    let (session, result) =
        load("def use : Nat := twice\n\ndef twice : Nat := 2\n\ndef twice : Nat := 3\n");
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
    let size = "def size : List a -> Nat\n  | Nil => 0\n  | Cons _ xs => Succ (size xs)\n\n";
    let (session, result) = load(&format!("{size}def a : Type := Nat\n"));
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
    let explicit = "def size : [a : Type] -> List a -> Nat\n  \
                    | Nil => 0\n  \
                    | Cons _ xs => Succ (size xs)\n\n\
                    def a : Type := Nat\n";
    let (session, result) = load(explicit);
    result.unwrap();
    assert!(session.warnings.is_empty(), "{:#?}", session.warnings);
    // If the signature then fails, its error says the same.
    let (_, result) = load(&format!("{size}def a : Nat := 0\n"));
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
        let rest = "ability Foo where\n  \
                    foo : Bar -> {Foo} ()\n\n\
                    ability Baz where\n  \
                    baz : () -> {Baz} ()\n\n\
                    def f () : {Baz, Foo} () := foo MkBar\n";
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

/// The data types added after the prelude, and the size of each one's group.
fn new_datas(session: &Session) -> Vec<(String, usize)> {
    let prelude = Session::new().elab.globals.datas.len();
    session.elab.globals.datas[prelude..]
        .iter()
        .map(|d| (d.name.to_string(), d.group.len()))
        .collect()
}

#[test]
fn data_types_that_refer_to_each_other_are_one_group() {
    // Written forest first: they're still one group, declared in source
    // order. `Label` is used by both but uses neither, so it's on its own,
    // first.
    let (session, result) = load(
        "type Forest : Type =\n  | FNil\n  | FCons (first : Tree) (rest : Forest)\n\n\
         type Tree : Type =\n  | Node (label : Label) (kids : Forest)\n\n\
         type Label : Type =\n  | MkLabel (n : Nat)\n",
    );
    result.unwrap();
    assert_eq!(
        new_datas(&session),
        [
            ("Label".into(), 1),
            ("Forest".into(), 2),
            ("Tree".into(), 2)
        ]
    );
}

#[test]
fn a_failed_data_group_fails_every_member_without_cascading() {
    // `Forest`'s field has a mistake; `Tree` is fine on its own, but fails
    // with it, and `size`, which uses `Tree`, isn't reported again.
    let (session, result) = load(
        "type Tree : Type =\n  \
         | Node (kids : Forest)\n\n\
         type Forest : Type =\n  \
         | FNil\n  \
         | FCons (first : Tree) (rest : Forst)\n\n\
         def size (t : Tree) : Nat := 0\n",
    );
    let errors = result.unwrap_err();
    assert_eq!(codes(&errors), ["E-UNKNOWN-NAME"], "{errors:#?}");
    let g = &session.elab.globals;
    let prelude = Session::new().elab.globals.datas.len();
    for data in &g.datas[prelude..] {
        assert_eq!(
            data.state,
            stitchwort_core::globals::State::Failed,
            "{}",
            data.name
        );
        assert!(data.ctors.is_empty());
    }
    // Mistakes in both are both reported, in source order.
    let (_, result) = load(
        "type Tree : Type =\n  | Node (kids : Forest) (n : Nat Nat)\n\n\
         type Forest : Type =\n  | FNil\n  | FCons (first : Tree) (rest : Forst)\n",
    );
    let errors = result.unwrap_err();
    assert_eq!(
        codes(&errors),
        ["E-NOT-A-FUNCTION", "E-UNKNOWN-NAME"],
        "{errors:#?}"
    );
}
