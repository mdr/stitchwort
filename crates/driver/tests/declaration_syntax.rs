//! The new declaration syntax through the elaborator
//! (docs/proposals/declaration-syntax.md): definitions written in it have
//! the hashes of their old-syntax equivalents, and the exact-arity rule and
//! the duplicate-parameter check surface from `Session::load`.

use std::collections::BTreeMap;

use stitchwort_core::DefId;
use stitchwort_core::hash::def_hash;
use stitchwort_driver::driver::Session;
use stitchwort_syntax::{Diagnostic, Syntax};

/// Loads `src` into a fresh session, in the new syntax or the old.
fn load(src: &str, new: bool) -> (Session, Result<(), Vec<Diagnostic>>, usize) {
    let mut session = Session::new();
    if new {
        session.syntax = Syntax::New;
    }
    let first = session.elab.globals.defs.len();
    let result = session.load("t.sw", src).map(|_| ());
    (session, result, first)
}

/// The hashes of the definitions `src` adds, by name.
#[track_caller]
fn hashes(src: &str, new: bool) -> BTreeMap<String, String> {
    let (session, result, first) = load(src, new);
    if let Err(ds) = result {
        let shown: Vec<_> = ds
            .iter()
            .map(|d| format!("{}: {}", d.code, d.message))
            .collect();
        panic!(
            "{} failed to load:\n{}\n{src}",
            if new { "new" } else { "old" },
            shown.join("\n")
        );
    }
    let g = &session.elab.globals;
    (first..g.defs.len())
        .map(|i| {
            let hash = def_hash(g, DefId(i))
                .ok()
                .flatten()
                .map_or("<none>".to_string(), |h| h.hex());
            (g.defs[i].path.to_string(), hash)
        })
        .collect()
}

/// Asserts the two sources load and give the same definitions the same hashes.
#[track_caller]
fn same_hashes(new: &str, old: &str) {
    let (n, o) = (hashes(new, true), hashes(old, false));
    assert!(!n.is_empty());
    assert_eq!(n, o, "hashes differ\nnew:\n{new}\nold:\n{old}");
}

/// The error codes and messages `src` fails with in the new syntax.
#[track_caller]
fn new_errors(src: &str) -> Vec<(String, String)> {
    let (_, result, _) = load(src, true);
    match result {
        Ok(()) => panic!("expected an error, but this loaded:\n{src}"),
        Err(ds) => ds
            .into_iter()
            .map(|d| (d.code.to_string(), d.message))
            .collect(),
    }
}

/// Asserts `src` fails in the new syntax with `code` and a message containing `part`.
#[track_caller]
fn assert_error(src: &str, code: &str, part: &str) {
    let errors = new_errors(src);
    assert!(
        errors.iter().any(|(c, m)| c == code && m.contains(part)),
        "expected {code} mentioning {part:?}, got {errors:?}\nfor:\n{src}"
    );
}

/// Asserts `src` loads in the new syntax.
#[track_caller]
fn assert_loads(src: &str) {
    let (_, result, _) = load(src, true);
    if let Err(ds) = result {
        let shown: Vec<_> = ds
            .iter()
            .map(|d| format!("{}: {}", d.code, d.message))
            .collect();
        panic!("expected this to load, but:\n{}\n{src}", shown.join("\n"));
    }
}

// --- Section 2.3's auto-binding table: the same hashes as the old syntax

// An auto-bound `a` first appears in the first parameter's type.
#[test]
fn auto_bind_first_parameter() {
    same_hashes(
        "def f (x : a) (xs : List a) : Nat := List.length xs\n",
        "f : (x : a) -> (xs : List a) -> Nat\nf x xs = List.length xs\n",
    );
}

// An auto-bound `a` first appears in a later parameter's type.
#[test]
fn auto_bind_later_parameter() {
    same_hashes(
        "def f (n : Nat) (xs : List a) : Nat := List.length xs\n",
        "f : (n : Nat) -> (xs : List a) -> Nat\nf n xs = List.length xs\n",
    );
}

// An auto-bound `a` appears only in the result type.
#[test]
fn auto_bind_result_type() {
    same_hashes(
        "def f (n : Nat) : List a := Nil\n",
        "f : (n : Nat) -> List a\nf n = Nil\n",
    );
}

// An auto-bound `a` is used by an auto binder.
#[test]
fn auto_bind_auto_binder() {
    same_hashes(
        "def f (x : a) [auto h : x = x] : Nat := 0\n",
        "f : (x : a) -> [auto h : x = x] -> Nat\nf x = 0\n",
    );
}

// Under another dependent binder (a proof about two names).
#[test]
fn auto_bind_dependent_binder() {
    same_hashes(
        "def f (x : a) (y : a) (p : x = y) : y = x := Eq.sym p\n",
        "f : (x : a) -> (y : a) -> (p : x = y) -> y = x\nf x y p = Eq.sym p\n",
    );
}

// After the colon, with arms.
#[test]
fn auto_bind_with_arms() {
    same_hashes(
        "def f (k : Nat) : List a -> Nat\n  | Nil       => k\n  | Cons x xs => Succ k\n",
        "f : (k : Nat) -> List a -> Nat\nf k Nil = k\nf k (Cons x xs) = Succ k\n",
    );
}

// --- The `()` header

// `()` lowers to `_`, with a `() ->` arrow.
#[test]
fn unit_header_is_wildcard() {
    same_hashes("def f () : Nat := 0\n", "f : () -> Nat\nf _ = 0\n");
}

// --- Exact arity

// An arm with fewer patterns than the arguments after the colon.
#[test]
fn arity_too_few_patterns() {
    let src =
        "def f : Nat -> Nat -> Nat\n  | Zero => \\y => y\n  | Succ x => \\y => Succ (f x y)\n";
    assert_error(src, "E-ARITY", "");
    // The old syntax accepted fewer patterns than arguments.
    let old = "f : Nat -> Nat -> Nat\nf Zero = \\y -> y\nf (Succ x) = \\y -> Succ (f x y)\n";
    let (_, result, _) = load(old, false);
    assert!(result.is_ok(), "{:?}", result.err());
}

// The same arms with a pattern for each argument load.
#[test]
fn arity_exact_loads() {
    assert_loads("def f : Nat -> Nat -> Nat\n  | Zero, y => y\n  | Succ x, y => Succ (f x y)\n");
}

// Arms but no explicit argument after the colon.
#[test]
fn arity_arms_without_argument() {
    assert_error(
        "def f (n : Nat) : Nat\n  | Zero => 0\n  | Succ k => 1\n",
        "E-ARITY",
        "use `:=`",
    );
}

// Arms with different numbers of patterns.
#[test]
fn arity_arms_differ() {
    assert_error(
        "def f : Nat -> Nat -> Nat\n  | Zero, y => y\n  | Succ x => \\y => y\n",
        "E-ARITY",
        "",
    );
}

// Arity counts through a definition that unfolds to a function type.
#[test]
fn arity_unfolds_definitions() {
    let alias = "def BinOp : Type := Nat -> Nat -> Nat\n\n";
    assert_loads(&format!("{alias}def add : BinOp\n  | x, y => x + y\n"));
    assert_error(
        &format!("{alias}def add : BinOp\n  | x => \\y => x + y\n"),
        "E-ARITY",
        "",
    );
}

// An ability row ends the count.
#[test]
fn arity_ends_at_ability_row() {
    assert_loads("def g : Nat -> {IO} (Nat -> Nat)\n  | n => \\m => m\n");
}

// A `:=` body has no arity rule.
#[test]
fn arity_assign_body_is_free() {
    assert_loads("def f (x : Nat) : Nat -> Nat := \\y => x + y\n");
}

// --- Duplicate parameters

// Two header binders with one name.
#[test]
fn duplicate_parameter_from_load() {
    assert_error(
        "def f (x : Nat) (x : Nat) : Nat := x\n",
        "E-DUPLICATE-PARAMETER",
        "`x`",
    );
}

// A header name repeated by an implicit binder after the colon.
#[test]
fn duplicate_parameter_implicit_after_colon() {
    assert_error(
        "def f (x : Nat) : [x : Bool] -> Nat\n  | y => 0\n",
        "E-DUPLICATE-PARAMETER",
        "`x`",
    );
}
