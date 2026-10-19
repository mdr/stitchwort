//! Running out of resources is an error with no answer, never a crash, a
//! type error, a passed test or a failed one
//! (docs/proposals/stack-safe-evaluation.md).
//!
//! These run in ordinary test threads (2 MiB of stack) with the default
//! limits, which are sized for them.

use stitchwort_core::{Limits, ResourceError};
use stitchwort_driver::driver::{Cache, Outcome, Session};

const REPLICATE: &str = "
def replicate : Nat -> a -> List a
  | Zero,   x => Nil
  | Succ n, x => Cons x (replicate n x)

-- In `List.length (replicate n 1) == n`, the computation appears in a type (the
-- decision's, `Decidable (List.length … = n)`), so checking a test written that
-- way would compute it. Inside a function, `n` is a variable when checked.
def replicateHasLength (n : Nat) : Bool := List.length (replicate n 1) == n
";

fn codes(
    result: Result<stitchwort_syntax::FileId, Vec<stitchwort_syntax::Diagnostic>>,
) -> Vec<&'static str> {
    match result {
        Ok(_) => Vec::new(),
        Err(diagnostics) => diagnostics.iter().map(|d| d.code).collect(),
    }
}

/// The evaluator keeps its pending work on the heap, so recursion a million
/// deep runs in a test thread's 2 MiB of stack.
#[test]
fn deep_recursion_runs_without_using_the_stack() {
    let mut session = Session::new();
    let source = format!(
        "{REPLICATE}\n\
         test \"deep\" := replicateHasLength 1000000\n\n\
         theorem deep : List.length (replicate 1000000 1) = 1000000 := rfl\n"
    );
    session.load("deep.sw", &source).expect("checks");
    let results = session.run_tests(&Cache::disabled());
    assert_eq!(results[0].outcome, Outcome::Passed);
}

/// With fewer frames allowed, the same program has no result.
fn with_few_frames() -> Session {
    let mut session = Session::new();
    session.elab.limits = Limits {
        frames: 10_000,
        ..Limits::default()
    };
    session
}

#[test]
fn a_test_that_recurses_too_deeply_has_no_result() {
    let mut session = with_few_frames();
    let source = format!("{REPLICATE}\ntest \"deep\" := replicateHasLength 100000\n");
    session.load("deep.sw", &source).expect("checks");
    let results = session.run_tests(&Cache::disabled());
    assert_eq!(
        results[0].outcome,
        Outcome::OutOfResources(ResourceError::Depth)
    );
}

#[test]
fn a_proof_that_recurses_too_deeply_is_rejected_for_that_reason() {
    let mut session = with_few_frames();
    let source =
        format!("{REPLICATE}\ntheorem deep : List.length (replicate 100000 1) = 100000 := rfl\n");
    // Not `E-REFL`: the kernel didn't find the sides different.
    let diagnostics = session.load("deep.sw", &source).unwrap_err();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert_eq!(diagnostics[0].code, "E-RESOURCE");
    // It points at the declaration.
    assert_eq!(diagnostics[0].labels.len(), 1, "{diagnostics:?}");
}

#[test]
fn too_much_work_has_no_result() {
    let mut session = Session::new();
    session.load("work.sw", REPLICATE).expect("checks");
    session
        .load("test.sw", "test \"long\" := replicateHasLength 100\n")
        .expect("checks");
    session.elab.limits = Limits {
        work: 50,
        ..Limits::default()
    };
    let results = session.run_tests(&Cache::disabled());
    assert_eq!(
        results[0].outcome,
        Outcome::OutOfResources(ResourceError::Work)
    );
}

#[test]
fn printing_too_large_a_value_is_an_error() {
    let mut session = Session::new();
    session.load("size.sw", REPLICATE).expect("checks");
    session.elab.limits = Limits {
        size: 100,
        ..Limits::default()
    };
    let file = session.sources.add("<input>", "replicate 1000 1");
    let expr = stitchwort_syntax::parse_expression(file, "replicate 1000 1").unwrap();
    let error = session.elab.eval_expr(&expr).unwrap_err();
    assert_eq!(error.code, "E-RESOURCE");
}

/// A program that exercises the elaborator's searches and retries: `auto`
/// arguments, `if h :`, `==` through decision procedures, text, abilities
/// with handlers, and proofs by computation.
const PROGRAM: &str = r#"
def half (n : Nat) : Nat := n / 2

def safeDiv (n : Nat) (d : Nat) : Nat := if h : d != 0 then n / d else 0

theorem halfTen : half 10 = 5 := rfl

ability Count where
  tick : () -> {Count} ()

def ticks : Nat -> {Count} Nat
  | Zero   => 0
  | Succ n =>
    tick ()
    Succ (ticks n)

def counted (prog : () -> {Count | e} a) : {e} Pair Nat a :=
  handle prog () with
    | return x     => MkPair 0 x
    | tick u, k    =>
      let r := k ()
      MkPair (Succ (Pair.fst r)) (Pair.snd r)

test "half"     := half 9 == 4
test "safeDiv"  := safeDiv 7 0 == 0
test "text"     := Text.join '-' (Text.split ',' "a,,b") == "a--b"
test "trim"     := Text.trim "  x " == "x"
test "count"    := Pair.fst (Effect.runPure (counted (\u => ticks 3))) == 3
"#;

/// With every work limit from 1 up to enough for everything: loading either
/// gives the same result as with no limit, or is rejected, and then the first
/// error is running out (nothing else is wrong with the program). Tests that
/// run either pass, as they do without a limit, or have no result.
#[test]
fn running_out_at_any_point_only_ever_means_no_answer() {
    let mut finished = false;
    let mut work = 1;
    while !finished {
        let mut session = Session::new();
        session.elab.limits = Limits {
            work,
            ..Limits::default()
        };
        match session.load("program.sw", PROGRAM) {
            Err(diagnostics) => {
                assert_eq!(
                    diagnostics[0].code, "E-RESOURCE",
                    "work {work}: {diagnostics:?}"
                );
            }
            Ok(_) => {
                let results = session.run_tests(&Cache::disabled());
                assert_eq!(results.len(), 5);
                finished = true;
                for r in &results {
                    match r.outcome {
                        Outcome::Passed => {}
                        Outcome::OutOfResources(ResourceError::Work) => finished = false,
                        other => panic!("work {work}: test {:?} gave {other:?}", r.name),
                    }
                }
            }
        }
        // Every limit while it's small, then in growing steps.
        work += 1 + work / 20;
    }
}

#[test]
fn running_out_leaves_nothing_behind() {
    let mut session = Session::new();
    session.elab.limits = Limits {
        work: 200,
        ..Limits::default()
    };
    assert!(session.load("first.sw", PROGRAM).is_err());
    assert!(session.elab.globals.metas.borrow().is_empty());
    assert_eq!(session.elab.globals.budget.exhausted(), None);
    // The same session, with enough resources, checks a new file as usual.
    session.elab.limits = Limits::default();
    session
        .load(
            "second.sw",
            "def double (n : Nat) : Nat := n + n\n\ntest \"double\" := double 21 == 42\n",
        )
        .expect("checks");
    let results = session.run_tests(&Cache::disabled());
    assert!(results.iter().all(|r| r.outcome == Outcome::Passed));
}

/// Checking `f a` needs `a`'s value only when `f`'s result type depends on it.
/// These arguments would run out of resources if they were computed.
#[test]
fn checking_does_not_compute_arguments_the_types_ignore() {
    let mut session = Session::new();
    let source = format!(
        "{REPLICATE}
def constant (x : a) (y : b) : a := x

def ignored : Nat := constant 0 (List.length (replicate 1000000 1))

def inField : Pair Nat Nat := MkPair 0 (List.length (replicate 1000000 1))

def inList : List Nat := [List.length (replicate 1000000 1)]
"
    );
    assert_eq!(codes(session.load("lazy.sw", &source)), Vec::<&str>::new());
}

/// When the result type does depend on an argument, its value is still used:
/// here a wrong proof is still rejected.
#[test]
fn arguments_the_types_need_are_still_computed() {
    let mut session = Session::new();
    let source = format!(
        "{REPLICATE}
theorem three : List.length (replicate 3 1) = 3 := rfl

def ok : Pair Nat Nat := MkPair (List.length (replicate 3 1)) 0

-- `Eq.cong`'s result type mentions its arguments.
theorem wrong : List.length (replicate 3 1) = 4 := Eq.cong (\\x => x) rfl
"
    );
    assert_eq!(
        codes(session.load("needed.sw", &source)),
        ["E-TYPE-MISMATCH"]
    );
}

const LISTS: &str = "
def allOnes : Nat -> List Nat
  | Zero   => [1]
  | Succ n => Cons 1 (allOnes n)

def endsInTwo : Nat -> List Nat
  | Zero   => [2]
  | Succ n => Cons 1 (endsInTwo n)

def startsWithTwo (n : Nat) : List Nat := Cons 2 (allOnes n)
";

/// Comparing long values, as checking a proof does, walks them with a work
/// list: two lists of 100,000 elements, built separately (so they share
/// nothing), compared equal, differing at the head and differing only at the
/// end.
#[test]
fn comparing_long_values_runs_without_using_the_stack() {
    use stitchwort_core::value::{conv, eval};
    let mut session = Session::new();
    session.load("lists.sw", LISTS).expect("checks");
    let g = &session.elab.globals;
    let def =
        |name: &str| stitchwort_core::DefId(g.defs.iter().position(|d| &*d.name == name).unwrap());
    let call = |name: &str| {
        let term = stitchwort_core::Term::app(
            stitchwort_core::Term::Def(def(name)),
            stitchwort_core::Term::Nat(std::rc::Rc::new(100_000u32.into())),
        );
        eval(g, &[], &term).unwrap()
    };
    let _op = g.budget.operation(Limits::default());
    let ones = call("allOnes");
    assert!(conv(g, 0, &ones, &call("allOnes")).unwrap());
    assert!(!conv(g, 0, &ones, &call("startsWithTwo")).unwrap());
    assert!(!conv(g, 0, &ones, &call("endsInTwo")).unwrap());
}

/// Printing a long value quotes it with a work list.
#[test]
fn printing_long_values_runs_without_using_the_stack() {
    let mut session = Session::new();
    session.load("lists.sw", LISTS).expect("checks");
    let file = session.sources.add("<input>", "allOnes 100000");
    let expr = stitchwort_syntax::parse_expression(file, "allOnes 100000").unwrap();
    let (value, ty) = session.elab.eval_expr(&expr).unwrap();
    assert_eq!(ty, "List Nat");
    // `[1, 1, …, 1]`: 100,001 ones, with ", " between them.
    assert_eq!(value.len(), 2 + 100_001 + 2 * 100_000);
}

/// A proof that compares two long lists.
#[test]
fn proofs_about_long_values_check() {
    let mut session = Session::new();
    let source = format!(
        "{LISTS}\n\
         theorem same : allOnes 20000 = allOnes 20000 := rfl\n\n\
         theorem differ : Not (allOnes 20000 = endsInTwo 20000) := \\p => p\n"
    );
    let codes: Vec<_> = match session.load("proofs.sw", &source) {
        Ok(_) => Vec::new(),
        Err(ds) => ds.iter().map(|d| d.code).collect(),
    };
    // `differ` is wrong on purpose: its body isn't a proof. It must be
    // rejected as a type error, after comparing the lists, not run out.
    assert_eq!(codes, ["E-TYPE-MISMATCH"]);
}

/// The adversarial `let` (docs/proposals/let.md §A.5, "Compile-time cost"),
/// through the elaborator: 20 nested `let`s on an unknown, each the previous
/// one used twice, in a type that is compared (and, for the false claim,
/// printed). Each must finish, or stop with `E-RESOURCE`, under the default
/// limits. A neutral value's spine isn't shared, so `x20`'s value is a tree
/// of 2^20 nodes: about 6 s in a release build, so it's skipped in debug
/// builds (the gate runs release).
#[test]
#[cfg_attr(debug_assertions, ignore = "slow in a debug build")]
fn nested_lets_finish_under_the_budget() {
    use std::time::{Duration, Instant};
    let mut lets = String::from("def nested (a : Nat) : Nat :=\n  let x0 := a\n");
    for i in 1..=20 {
        lets += &format!("  let x{i} := x{} + x{}\n", i - 1, i - 1);
    }
    for (claim, allowed) in [
        ("x20 = x20", ["ok", "E-RESOURCE"]),
        ("x20 = 0", ["E-REFL", "E-RESOURCE"]),
    ] {
        let source = format!("{lets}  let p : {claim} := rfl\n  x20\n");
        let mut session = Session::new();
        let started = Instant::now();
        let codes = codes(session.load("nested.sw", &source));
        let elapsed = started.elapsed();
        let code = codes.first().copied().unwrap_or("ok");
        assert!(allowed.contains(&code), "{claim}: unexpected {codes:?}");
        assert!(
            elapsed < Duration::from_secs(60),
            "{claim}: took {elapsed:?}"
        );
        eprintln!("nested lets, {claim}: {code} in {elapsed:?}");
    }
}

/// The elaborator defers a `let` whose value isn't quick to compute: it's
/// computed while checking only if a type needs it (docs/proposals/let.md
/// §A.7), and then correctly.
#[test]
fn a_large_let_is_computed_only_when_a_type_needs_it() {
    let work = |body: &str| {
        let mut session = Session::new();
        let before = session.elab.globals.budget.total_work();
        let source =
            format!("def f : Nat :=\n  let xs := List.range 200000\n{body}  List.length xs\n");
        let result = codes(session.load("big.sw", &source));
        assert!(result.is_empty(), "{result:?}");
        session.elab.globals.budget.total_work() - before
    };
    let unused = work("");
    let used = work("  let p : List.length xs = 200000 := rfl\n");
    eprintln!("a large let: {unused} steps unused, {used} used");
    assert!(
        unused * 4 < used,
        "{unused} steps when no type needs it, {used} when one does"
    );
}

/// Freeing a deeply nested term doesn't recurse.
#[test]
fn freeing_deep_terms_runs_without_using_the_stack() {
    use stitchwort_core::{DataId, Term};
    let mut term = Term::Refl;
    for _ in 0..1_000_000 {
        term = Term::ctor(DataId(0), 1, vec![Term::Refl, term]);
    }
    drop(term);
    let mut term = Term::Refl;
    for _ in 0..1_000_000 {
        term = Term::app(Term::Refl, term);
    }
    drop(term);
}
