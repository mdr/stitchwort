//! Running out of resources is an error with no answer, never a crash, a
//! type error, a passed test or a failed one
//! (docs/proposals/stack-safe-evaluation.md).
//!
//! These run in ordinary test threads (2 MiB of stack) with the default
//! limits, which are sized for them.

use stitchwort_core::{Limits, ResourceError};
use stitchwort_driver::driver::{Cache, Outcome, Session};

const REPLICATE: &str = "
replicate : Nat -> a -> List a
replicate Zero     x = Nil
replicate (Succ n) x = Cons x (replicate n x)

-- In `length (replicate n 1) == n`, the computation appears in a type (the
-- decision's, `Decidable (length … = n)`), so checking a test written that
-- way would compute it. Inside a function, `n` is a variable when checked.
replicateHasLength : Nat -> Bool
replicateHasLength n = length (replicate n 1) == n
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
        "{REPLICATE}\ntest \"deep\" = replicateHasLength 1000000\n\n\
         theorem deep : length (replicate 1000000 1) = 1000000\ndeep = rfl\n"
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
    let source = format!("{REPLICATE}\ntest \"deep\" = replicateHasLength 100000\n");
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
        format!("{REPLICATE}\ntheorem deep : length (replicate 100000 1) = 100000\ndeep = rfl\n");
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
        .load("test.sw", "test \"long\" = replicateHasLength 100\n")
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
half : Nat -> Nat
half n = n / 2

safeDiv : Nat -> Nat -> Nat
safeDiv n d = if h : d != 0 then n / d else 0

theorem halfTen : half 10 = 5
halfTen = rfl

ability Count where
  tick : () -> {Count} ()

ticks : Nat -> {Count} Nat
ticks Zero     = 0
ticks (Succ n) =
  tick ()
  Succ (ticks n)

counted : (() -> {Count | e} a) -> {e} Pair Nat a
counted prog =
  handle prog () with
    | return x     -> MkPair 0 x
    | tick u => k  ->
      let r = k ()
      MkPair (Succ (fst r)) (snd r)

test "half"     = half 9 == 4
test "safeDiv"  = safeDiv 7 0 == 0
test "text"     = textJoin '-' (textSplit ',' "a,,b") == "a--b"
test "trim"     = textTrim "  x " == "x"
test "count"    = fst (runPure (counted (\u -> ticks 3))) == 3
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
            "double : Nat -> Nat\ndouble n = n + n\n\ntest \"double\" = double 21 == 42\n",
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
constant : a -> b -> a
constant x y = x

ignored : Nat
ignored = constant 0 (length (replicate 1000000 1))

inField : Pair Nat Nat
inField = MkPair 0 (length (replicate 1000000 1))

inList : List Nat
inList = [length (replicate 1000000 1)]
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
theorem three : length (replicate 3 1) = 3
three = rfl

ok : Pair Nat Nat
ok = MkPair (length (replicate 3 1)) 0

-- `cong`'s result type mentions its arguments.
theorem wrong : length (replicate 3 1) = 4
wrong = cong (\\x -> x) rfl
"
    );
    assert_eq!(
        codes(session.load("needed.sw", &source)),
        ["E-TYPE-MISMATCH"]
    );
}
