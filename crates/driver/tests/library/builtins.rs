//! The built-in registry (docs/proposals/namespaces.md §4.7, stage 0): the
//! prelude declarations that syntax, natives, the effect machinery, the JS
//! generator, the printer and the runner mean are bound by identity while
//! the prelude loads, and nothing a program's names mean can change them.
//!
//! The programs here declare their own versions of the library's names, which
//! hide the library's (docs/proposals/namespaces.md §4.4).

use stitchwort_core::globals::State;
use stitchwort_core::registry::{Builtin, Kind, check_complete};
use stitchwort_driver::driver::{Cache, Outcome, Session, with_stack};
use stitchwort_elab::prelude;
use stitchwort_syntax::SourceMap;

/// Stack for loading the whole library: this test also runs in the gate's
/// debug build, whose frames are several times larger than release's.
const STACK: usize = 16 * 1024 * 1024;

#[test]
fn the_prelude_binds_every_builtin_to_a_final_declaration() {
    with_stack(STACK, prelude_binds_every_builtin);
}

fn prelude_binds_every_builtin() {
    let session = Session::eager_from_source_for_stack(STACK);
    let g = &session.elab.ev();
    let r = &g.env.registry();
    assert_eq!(r.missing(), Vec::<Builtin>::new());
    assert!(check_complete(g).is_ok());
    for &b in Builtin::ALL {
        match b.kind() {
            Kind::Data => {
                let data = g.data(r.data(b).unwrap());
                assert_eq!(data.state(), State::Final, "{b:?}");
                assert_eq!(&**data.name(), b.name(), "{b:?}");
            }
            Kind::Def => {
                let def = g.def(r.def(b).unwrap());
                assert_eq!(def.state(), State::Final, "{b:?}");
                assert_eq!(&**def.name(), b.name(), "{b:?}");
            }
            Kind::Ctor(parent) => {
                let (d, c) = r.ctor(b).unwrap();
                assert_eq!(Some(d), r.data(parent), "{b:?}");
                assert_eq!(&*g.data(d).ctors()[c].name, b.name(), "{b:?}");
            }
        }
    }
    // The natives and the compact text representation are attached to the
    // registry's declarations.
    assert_eq!(g.env.builtins().nat, r.data(Builtin::Nat));
    assert_eq!(g.env.builtins().bool, r.data(Builtin::Bool));
    assert_eq!(g.env.builtins().decidable, r.data(Builtin::Decidable));
    assert_eq!(g.env.builtins().nat_neq, r.def(Builtin::NatNeq));
    let text = g
        .env
        .builtins()
        .text
        .as_ref()
        .expect("compact text is bound");
    assert_eq!(Some(text.list), r.data(Builtin::List));
    assert_eq!(Some(text.char), r.data(Builtin::Char));
}

/// Every library declaration hashes as `hash_stability`'s prelude snapshot
/// (checked in the release build) says. In the gate's debug build this
/// catches elaboration that depends on the build profile: before SW-962, a
/// cheap attempt inside the elaborator had a budget in bytes of stack, gave
/// up in a debug build only, and `Std.Nat.partitionPointBounds`
/// elaborated to a different term, with 40 other library declarations.
#[test]
fn the_library_hashes_as_in_the_release_build() {
    with_stack(STACK, library_hashes_as_in_the_release_build);
}

fn library_hashes_as_in_the_release_build() {
    use stitchwort_core::hash::{data_hash, def_hash};
    use stitchwort_core::{DataId, DefId};
    let snapshot = include_str!("snapshots/library__hash_stability__prelude.snap");
    let pinned: stitchwort_core::collections::HashMap<&str, &str> = snapshot
        .lines()
        .filter_map(|line| line.rsplit_once(' '))
        .filter(|(_, hash)| hash.len() == 64)
        .collect();
    let session = Session::eager_from_source_for_stack(STACK);
    let g = &session.elab.ev();
    let show = |h: stitchwort_core::budget::Result<Option<stitchwort_core::hash::ContentHash>>| {
        h.ok().flatten().map(|h| h.hex())
    };
    let mut lines: Vec<(String, Option<String>)> = Vec::new();
    for i in 0..g.env.datas().len() {
        lines.push((
            format!("data {}", g.env.datas()[i].path()),
            show(data_hash(g, DataId(i))),
        ));
    }
    for i in 0..g.env.defs().len() {
        lines.push((
            g.env.defs()[i].path().to_string(),
            show(def_hash(g, DefId(i))),
        ));
    }
    assert_eq!(
        lines.len(),
        pinned.len(),
        "the snapshot is of another library"
    );
    let differ: Vec<&str> = lines
        .iter()
        .filter(|(name, hash)| pinned.get(name.as_str()).copied() != hash.as_deref())
        .map(|(name, _)| name.as_str())
        .collect();
    assert!(
        differ.is_empty(),
        "{} declarations hash differently from the release build, first {:?}",
        differ.len(),
        &differ[..differ.len().min(10)]
    );
}

#[test]
fn a_prelude_without_a_builtin_is_refused_before_user_code() {
    // The prelude loads, but doesn't declare `IO.simulate`.
    let prelude = prelude().replace("IO.simulate", "IO.simulateRenamed");
    let mut session = Session {
        sources: SourceMap::new(),
        elab: stitchwort_elab::Elaborator::new(),
        warnings: Vec::new(),
    };
    session.elab.set_loading_prelude(true);
    session
        .load("<prelude>", &prelude)
        .expect("the prelude loads");
    let missing = session.elab.finish_core().unwrap_err();
    assert_eq!(missing.code, "E-BUILTIN");
    assert!(
        missing.message.contains("`IO.simulate`"),
        "{}",
        missing.message
    );
    // And no user code is elaborated.
    let errors = session.load("test.sw", "def x : Nat := 1\n").unwrap_err();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].code, "E-BUILTIN");
}

#[test]
fn a_forgotten_builtin_is_an_error_not_a_name_lookup() {
    let mut session = Session::new();
    session
        .load("test.sw", "def x : Nat := 1 + 2\n")
        .expect("loads");
    session
        .elab
        .kernel
        .env
        .forget_builtin_for_tests(Builtin::Add);
    let errors = session.load("more.sw", "def y : Nat := 1\n").unwrap_err();
    assert_eq!(errors[0].code, "E-BUILTIN");
    assert!(errors[0].message.contains("`Nat.add`"));
}

/// A program that declares its own versions of the names syntax used to be
/// looked up by (`add`, `List`, `Nil`, `Comp`, …), which mean something
/// else, and uses the syntax they stand for.
const PROGRAM: &str = r#"
import Std (Char, Nat, Text)

type List (a : Type) : Type =
  | Nil
  | Cons (head : a) (tail : List a)
  | Extra

type Option : Type =
  | None
  | Some

type Unit : Type =
  | Trivial

type Decidable : Type =
  | Yes
  | No

type Peano : Type =
  | Zero
  | Succ (n : Peano)

type UnitType : Type =
  | UnitValue

type Comp : Type =
  | Done
  | Call

type Plus : Type =
  | Plus1

def add (m : Nat) (n : Nat) : Nat := 0

def sub (m : Nat) (n : Nat) : Nat := 0

def LessThan (m : Nat) (n : Nat) : Prop := m = m

def Not : Nat := 1

def append : Nat := 2

def textAppend : Nat := 3

def ifThenElse : Nat := 4

def toBool : Nat := 5

def elimDec : Nat := 6

def fromYes : Nat := 7

def cong : Nat := 8

def fst : Nat := 9

def simulate : Nat := 10

def bind : Nat := 11

def foldComp : Nat := 12

def runPure : Nat := 13

def sigOp : Nat := 14

type Point = { x : Nat, y : Nat }

def isTwo : Nat -> Bool
  | 2 => True
  | n => False

def unitOne : () -> Nat
  | () => 1

def safeDiv (n : Nat) (d : Nat) : [auto ok : d != 0] -> Nat := n / d

def mine : List Nat := Cons 1 Nil

def twice () : {IO} () :=
  IO.print "one"
  let n := 2 + 2
  IO.print (Nat.toText n)

def main () : {IO} () :=
  twice ()
  IO.print ("a" ++ "b")

test "plus" := 2 + 3 == 5
test "minus" := 5 - 3 == 2
test "big plus" := 1000000000000 + 1000000000000 == 2000000000000
test "less" := (if h : 1 < 2 then True else False) == True
test "not equal" := (if h : 1 != 2 then True else False) == True
test "if" := (if 1 == 1 then 4 else 5) == 4
test "text append" := Text.length ("ab" ++ "cd") == 4
test "list append" := Std.List.length ([1, 2] ++ [3]) == 3
test "number patterns" := isTwo 2 == True
test "unit pattern" := unitOne () == 1
test "auto" := safeDiv 6 2 == 3
test "records" := ({ x = 1, y = 2 } : Point) == { x = 1, y = 2 }
test "records differ" := (({ x = 1, y = 2 } : Point) == { x = 1, y = 3 }) == False
test "char literal" := Char.toNat 'a' == 97
"#;

fn hidden_session() -> Session {
    let mut session = Session::new();
    if let Err(errors) = session.load("test.sw", PROGRAM) {
        panic!("{errors:#?}");
    }
    session
}

#[test]
fn syntax_means_the_prelude_whatever_its_names_mean() {
    let session = hidden_session();
    let results = session.run_tests(&Cache::disabled());
    assert!(!results.is_empty());
    for result in &results {
        assert_eq!(result.outcome, Outcome::Passed, "{}", result.name);
    }
}

#[test]
fn natives_stay_on_the_prelude_definitions() {
    let session = hidden_session();
    let g = &session.elab.ev();
    let add = g.env.registry().def(Builtin::Add).unwrap();
    assert!(g.env.builtins().native(add).is_some());
    // The program's own `add` is the last definition of that name.
    let mine = g
        .env
        .defs()
        .iter()
        .rposition(|d| &**d.name() == "add")
        .unwrap();
    assert_ne!(mine, add.0);
    assert!(
        g.env
            .builtins()
            .native(stitchwort_core::DefId(mine))
            .is_none()
    );
}

#[test]
fn the_runner_uses_the_prelude_simulate_and_io() {
    let mut session = hidden_session();
    assert_eq!(session.simulate(&[]).unwrap(), ["one", "4", "ab"]);
    let main = session.main().unwrap();
    let mut output = Vec::new();
    session.run_main(&main, &mut &b""[..], &mut output).unwrap();
    assert_eq!(String::from_utf8(output).unwrap(), "one\n4\nab\n");
}

#[test]
fn a_programs_own_list_prints_as_itself() {
    let mut session = hidden_session();
    let show = |session: &mut Session, text: &str| {
        let expr = session.parse_expression("<t>", text).unwrap();
        session.elab.eval_expr(&expr).unwrap()
    };
    // The program's `List`: constructors, not a list literal.
    let (value, ty) = show(&mut session, "mine");
    assert_eq!(value, "Cons 1 Nil");
    assert_eq!(ty, "List Nat");
    // The prelude's: a literal, and `()` for its unit.
    let (value, _) = show(&mut session, "[1, 2] ++ [3]");
    assert_eq!(value, "[1, 2, 3]");
    let (value, ty) = show(&mut session, "()");
    assert_eq!((value.as_str(), ty.as_str()), ("()", "()"));
}

#[test]
fn a_programs_own_list_crosses_the_js_boundary_as_itself() {
    let mut session = Session::new();
    // Shaped like the prelude's, so only its identity tells them apart.
    let program = "type List (a : Type) : Type =\n  \
                   | Nil\n  \
                   | Cons (head : a) (tail : List a)\n\n\
                   export def size : List Nat -> Nat\n  \
                   | Nil => 0\n  \
                   | Cons x xs => 1 + size xs\n";
    if let Err(errors) = session.load("test.sw", program) {
        panic!("{errors:#?}");
    }
    let out = session.extract().unwrap();
    // Decoded as the tagged objects of a data type of the program's, never
    // as a JS array, which is the prelude's list codec.
    assert!(
        out.dts
            .contains("export declare function size(arg0: List<bigint>): bigint;"),
        "{}",
        out.dts
    );
    assert!(out.dts.contains("readonly $tag: \"Cons\""), "{}", out.dts);
}

/// The core loaded with `from` replaced by `to` in its text: the diagnostics
/// that refuse it.
fn refused_after_editing_the_core(from: &str, to: &str) -> Vec<stitchwort_syntax::Diagnostic> {
    let prelude = prelude();
    assert!(prelude.contains(from), "the core has no `{from}`");
    let prelude = prelude.replace(from, to);
    let mut session = Session {
        sources: SourceMap::new(),
        elab: stitchwort_elab::Elaborator::new(),
        warnings: Vec::new(),
    };
    session.elab.set_loading_prelude(true);
    session
        .load("<prelude>", &prelude)
        .expect_err("the edited core is refused")
}

#[test]
fn a_renamed_binder_of_a_shaped_builtin_is_refused() {
    let errors = refused_after_editing_the_core(
        "(yesEq: ∀ (h: p) => y h = z)",
        "(yesEqual: ∀ (h: p) => y h = z)",
    );
    let e = errors
        .iter()
        .find(|d| d.code == "E-BUILTIN")
        .unwrap_or_else(|| panic!("{errors:#?}"));
    assert!(e.message.contains("`Decidable.elimEq`"), "{}", e.message);
    assert!(
        e.message.contains("expected `[p] [a] d y n z yesEq noEq`")
            && e.message.contains("found `[p] [a] d y n z yesEqual noEq`"),
        "{}",
        e.message
    );
}

#[test]
fn a_reordered_binder_of_a_shaped_builtin_is_refused() {
    let errors = refused_after_editing_the_core(
        "theorem Decidable.elimEq: ∀ [p: Prop] [a: Type]",
        "theorem Decidable.elimEq: ∀ [a: Type] [p: Prop]",
    );
    let e = errors
        .iter()
        .find(|d| d.code == "E-BUILTIN")
        .unwrap_or_else(|| panic!("{errors:#?}"));
    assert!(e.message.contains("`Decidable.elimEq`"), "{}", e.message);
    assert!(
        e.message.contains("found `[a] [p] d y n z yesEq noEq`"),
        "{}",
        e.message
    );
}

/// Every shape is checked where its built-in is bound, so a shape added
/// without a binding site would still be enforced.
#[test]
fn every_shape_is_checked_at_binding() {
    with_stack(STACK, || {
        stitchwort_core::registry::take_shape_checks();
        let _session = Session::eager_from_source_for_stack(STACK);
        let checked = stitchwort_core::registry::take_shape_checks();
        let unchecked: Vec<&str> = Builtin::ALL
            .iter()
            .filter(|b| b.shape().is_some() && !checked.contains(b))
            .map(|b| b.name())
            .collect();
        assert!(
            unchecked.is_empty(),
            "shapes nothing checked: {unchecked:?}"
        );
    });
}
