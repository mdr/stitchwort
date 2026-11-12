//! Running out of resources is an error with no answer, never a crash, a
//! type error, a passed test or a failed one
//! (docs/proposals/stack-safe-evaluation.md).
//!
//! These run in ordinary test threads (2 MiB of stack) with the default
//! limits, which are sized for them.

use stitchwort_core::{Limits, ResourceError};
use stitchwort_driver::driver::{Cache, Outcome, Session, tier_sample, with_stack};

// mimalloc, the CLI's allocator, and so the language server's. With macOS's own,
// `running_out_at_any_point_only_ever_means_no_answer` grew to 6.7 GB,
// though every session's memory is freed when it's dropped (SW-921): at
// about 30 of its limits about 50 of the library's theorems fail, the
// counterexample searches on them grow the fast runtime's registers to as
// much as 162 MB, and the
// system allocator kept those freed blocks, 229 MB more for each such
// session (with `MallocLargeCache=0` the same run stays at 61 MB). With
// mimalloc it stays under 400 MB.
use stitchwort_test_alloc as _;

const REPLICATE: &str = "
import Std (List)

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
    session.elab.options.limits = Limits {
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
    session.elab.options.limits = Limits {
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
    session.elab.options.limits = Limits {
        size: 100,
        ..Limits::default()
    };
    let file = session.sources.add("<input>", "replicate 1000 1");
    let expr = stitchwort_syntax::parse_expression(file, "replicate 1000 1").unwrap();
    let error = session.elab.eval_expr(&expr).unwrap_err();
    assert_eq!(error.code, "E-RESOURCE");
}

/// "A value was too large to write out" in a theorem that unfolds an opaque
/// definition names the theorem and the definition it unfolds, so the
/// reader knows where the large value came from
/// (docs/proposals/opaque-definitions.md §6.10).
#[test]
fn a_value_too_large_to_show_names_the_declaration_and_what_it_unfolds() {
    let mut session = Session::new();
    session
        .load(
            "big.sw",
            "import Std (List, Nat)\n\n\
             def replicate : Nat -> a -> List a\n  | Zero,   x => Nil\n  \
             | Succ n, x => Cons x (replicate n x)\n\n\
             opaque def big (n: Nat): List Nat := replicate 500 n\n",
        )
        .expect("checks");
    session.elab.options.limits = Limits {
        size: 100,
        ..Limits::default()
    };
    let diagnostics = session
        .load(
            "use.sw",
            "theorem t (n: Nat): big n = big n unfolding big := rewrite Eq.refl (big n) in rfl\n",
        )
        .unwrap_err();
    let resource = diagnostics
        .iter()
        .find(|d| d.code == "E-RESOURCE")
        .unwrap_or_else(|| panic!("{diagnostics:?}"));
    assert!(
        stitchwort_core::budget::ResourceError::is_size_message(&resource.message),
        "{resource:?}"
    );
    let notes = resource.notes.join("\n");
    assert!(notes.contains("while checking `t`"), "{notes}");
    assert!(
        notes.contains("it unfolds `big`, so its opaque body was computed here"),
        "{notes}"
    );
}

/// A proof that runs out of steps names the definition it was unfolding,
/// so the reader knows which computation was too long.
#[test]
fn running_out_of_steps_names_the_definition_being_unfolded() {
    let mut session = Session::new();
    session.elab.options.limits = Limits {
        work: 5_000,
        ..Limits::default()
    };
    let source =
        format!("{REPLICATE}\ntheorem long : List.length (replicate 10000 1) = 10000 := rfl\n");
    let diagnostics = session.load("work.sw", &source).unwrap_err();
    let resource = diagnostics
        .iter()
        .find(|d| d.code == "E-RESOURCE")
        .unwrap_or_else(|| panic!("{diagnostics:?}"));
    let notes = resource.notes.join("\n");
    assert!(
        notes.contains("it ran out while unfolding `replicate`"),
        "{resource:?}"
    );
}

/// A program that exercises the elaborator's searches and retries: `auto`
/// arguments, `if h :`, `==` through decision procedures, text, abilities
/// with handlers, and proofs by computation.
const PROGRAM: &str = r#"
import Std (Pair, Text)

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
test "text"     := Text.join (Text.split "a,,b" ',') '-' == "a--b"
test "trim"     := Text.trim "  x " == "x"
test "count"    := Pair.fst (counted (u => ticks 3)) == 3
"#;

/// With every work limit from 1 up to enough for everything: loading either
/// gives the same result as with no limit, or is rejected, and then the first
/// error is running out (nothing else is wrong with the program). Tests that
/// run either pass, as they do without a limit, or have no result.
///
/// The limits are every one while they're small, then in growing steps: 161
/// up to enough for everything, about 107 s, most of it the counterexample
/// searches on the library's theorems that fail at limits from about 2,000
/// to 8,000. Outside the full tier the test takes a corpus sweep's sample of
/// them, every 4th in the daily tier (docs/testing.md).
#[test]
fn running_out_at_any_point_only_ever_means_no_answer() {
    let mut limits = Vec::new();
    let mut work = 1;
    while work < Limits::default().work {
        limits.push(work);
        work += 1 + work / 20;
    }
    let mut finished = false;
    for work in tier_sample(limits, 4) {
        let mut session = Session::new();
        session.elab.options.limits = Limits {
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
        if finished {
            break;
        }
    }
    assert!(finished, "the program never ran within the limits");
}

#[test]
fn running_out_leaves_nothing_behind() {
    let mut session = Session::new();
    session.elab.options.limits = Limits {
        work: 200,
        ..Limits::default()
    };
    assert!(session.load("first.sw", PROGRAM).is_err());
    assert!(session.elab.metas().metas.borrow().is_empty());
    assert_eq!(session.elab.kernel.machine.budget.exhausted(), None);
    // The same session, with enough resources, checks a new file as usual.
    session.elab.options.limits = Limits::default();
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
theorem wrong : List.length (replicate 3 1) = 4 := Std.Eq.cong (x => x) rfl
"
    );
    // `rfl` is checked after the rest of its call (postponement stage 7),
    // against `List.length (replicate 3 1) = 4`: computing the left side
    // gives 3, so `rfl` itself is refused (before stage 7, the call's
    // result type was: `E-TYPE-MISMATCH`).
    assert_eq!(codes(session.load("needed.sw", &source)), ["E-REFL"]);
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
    let g = &session.elab.ev();
    let def = |name: &str| {
        stitchwort_core::DefId(
            g.env
                .defs()
                .iter()
                .position(|d| &**d.name() == name)
                .unwrap(),
        )
    };
    let call = |name: &str| {
        let term = stitchwort_core::Term::app(
            stitchwort_core::Term::Def(def(name)),
            stitchwort_core::Term::Nat(std::rc::Rc::new(100_000u32.into())),
        );
        eval(g, &[], &term).unwrap()
    };
    let _op = g.machine.budget.operation(Limits::default());
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
         theorem differ : Not (allOnes 20000 = endsInTwo 20000) := p => p\n"
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
        let before = session.elab.kernel.machine.budget.total_work();
        let source = format!(
            "import Std (List)\ndef f : Nat :=\n  let xs := List.range 0 200000\n{body}  List.length xs\n"
        );
        let result = codes(session.load("big.sw", &source));
        assert!(result.is_empty(), "{result:?}");
        session.elab.kernel.machine.budget.total_work() - before
    };
    let unused = work("");
    let used = work("  let p : List.length xs = 200000 := rfl\n");
    eprintln!("a large let: {unused} steps unused, {used} used");
    assert!(
        unused * 4 < used,
        "{unused} steps when no type needs it, {used} when one does"
    );
}

/// Comparing a large `let` with `==` doesn't compute it while checking: the
/// decision is made about a bound variable, so the kernel's types never
/// mention the `let` (SW-412: a real-input test computed its answer in the
/// kernel, then again when it ran). Its effectful form is the same: the
/// computation is run in place as a `let`.
#[test]
fn comparing_a_large_let_does_not_compute_it_while_checking() {
    let work = |decl: &str| {
        let mut session = Session::new();
        let before = session.elab.kernel.machine.budget.total_work();
        let source = format!("import Std (List)\n{decl}\n");
        let result = codes(session.load("big.sw", &source));
        assert!(result.is_empty(), "{result:?}");
        session.elab.kernel.machine.budget.total_work() - before
    };
    let small = work("test \"small\" := (List.range 0 2).length == 2");
    for decl in [
        "test \"let\" :=\n  let n := (List.range 0 200000).length\n  n == 200000",
        "def f (b: Bool): Bool :=\n  let n := (List.range 0 200000).length\n  b && n == 200000",
        "import Std (Fail)\n\
         test \"effectful\" := Fail.orElse 0 (() => (List.range 0 200000).length) == 200000",
    ] {
        let large = work(decl);
        eprintln!("{decl:?}: {large} steps (a small one: {small})");
        // Computing the list while checking takes about 3 times what
        // loading the library does.
        assert!(
            large < small * 2,
            "{decl:?}: {large} steps, {small} for a small one"
        );
    }
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

/// Checking nested calls of `List.map` in a pure function takes work that
/// grows with the depth of the nesting, not exponentially in it (SW-439):
/// with pure callbacks, and with an effectful one, which is refused. The
/// work is the elaborator's (`Budget::total_visits`); doubling with each
/// level, depth 30 would take a billion times depth 0's.
#[test]
fn nested_maps_check_in_work_polynomial_in_their_depth() {
    let visits = |callback: &str, depth: usize| {
        let mut nested = "xs".to_string();
        for _ in 0..depth {
            nested = format!("List.map ({nested}) {callback}");
        }
        let source = format!(
            "import Std (List, Fail)\n\
             def pure (n: Nat): Nat := n + 1\n\
             def fails (n: Nat): {{Fail}} Nat := if n == 0 then Fail.fail \"zero\" else n\n\
             def g (xs: List Nat): Nat := List.length ({nested})\n"
        );
        let mut session = Session::new();
        let before = session.elab.kernel.machine.budget.total_visits();
        let result = codes(session.load("nested.sw", &source));
        let expected: &[&str] = match (callback, depth) {
            ("fails", 1..) => &["E-ABILITY"],
            _ => &[],
        };
        assert_eq!(result, expected, "{callback} at depth {depth}");
        session.elab.kernel.machine.budget.total_visits() - before
    };
    for callback in ["pure", "fails"] {
        let base = visits(callback, 0);
        let d10 = visits(callback, 10) - base;
        let d20 = visits(callback, 20) - base;
        // Asked before depth 30, which work that doubles with each level
        // wouldn't finish in hours: it makes depth 20 a thousand times
        // depth 10, where cubic work makes it 8 times.
        assert!(
            d20 < 10 * d10,
            "{callback}: {d10}, {d20} visits at depths 10, 20"
        );
        let d30 = visits(callback, 30) - base;
        eprintln!("nested maps of {callback}: {d10}, {d20}, {d30} visits at depths 10, 20, 30");
        // Linear work adds as much from depth 20 to 30 as from 10 to 20,
        // quadratic 5/3 as much, cubic 2.7 times as much.
        assert!(
            d30 - d20 < 3 * (d20 - d10),
            "{callback}: {d10}, {d20}, {d30} visits at depths 10, 20, 30"
        );
    }
}

/// Checking `%` of a number with an unknown in it, `(x + k) % 2`, takes time
/// linear in `k` (SW-2572). Its quotient `(x + k) / 2` is `k / 2` `Succ`s
/// around a stuck step, and `%` multiplies it back; `*` took one `Succ` off
/// a step and walked the rest of the chain each time to see it wasn't a
/// number, so `k = 16000` took 10 s and the effect fuzzer's programs, with
/// constants near a million, over ten minutes. Its time, not its steps, is
/// what's measured: the walk took no steps, only forced calls already
/// unfolded. `y` unknown takes the case tree one `Succ` at a time, which
/// was quadratic for the same reason.
#[test]
#[cfg_attr(debug_assertions, ignore = "slow in a debug build")]
fn remainders_of_long_numbers_check_in_linear_time() {
    use std::time::{Duration, Instant};
    let source = "import Std (Nat)\n\n\
                  def remainder (x: Nat): Nat := if (x + 40000) % 2 == 0 then 1 else 2\n\
                  def times (x: Nat) (y: Nat): Nat := if ((x + 40000) / 2) * y == 0 then 1 else 2\n\
                  def twice (x: Nat): Nat :=\n  \
                  let a := if (x + 40000) % 2 == 0 then 4 else 4\n  \
                  if a % 2 == 0 then 1 else 2\n";
    let mut session = Session::new();
    let started = Instant::now();
    let result = codes(session.load("long.sw", source));
    let elapsed = started.elapsed();
    assert!(result.is_empty(), "{result:?}");
    eprintln!("remainders of long numbers: {elapsed:?}");
    // Quadratic, this was minutes; linear, it's about a second, most of it
    // loading the library.
    assert!(elapsed < Duration::from_secs(10), "took {elapsed:?}");
}

/// `x * t` with `x` unknown is stuck on `x` at once, and `*`'s shortcut for
/// unknowns (SW-2572) doesn't compute `t` either, as `Nat.mul`'s definition
/// never looks at it then: `count 100000000` would take 10^8 steps.
#[test]
fn a_product_stuck_on_its_left_does_not_compute_its_right() {
    let mut session = Session::new();
    let before = session.elab.kernel.machine.budget.total_work();
    let source = "def count: (n: Nat) → Nat\n  | Zero => 0\n  | Succ n => Succ (count n)\n\n\
                  def f (x: Nat): Nat := x * count 100000000\n\n\
                  theorem t (x: Nat): f x = x * count 100000000 := rfl\n";
    let result = codes(session.load("stuck.sw", source));
    assert!(result.is_empty(), "{result:?}");
    let work = session.elab.kernel.machine.budget.total_work() - before;
    assert!(work < 1_000_000, "{work} steps");
}

/// Whatever a check ran out of, the error says which declaration it was
/// checking, and points at it (SW-843).
#[test]
fn running_out_of_steps_names_the_declaration_being_checked() {
    let mut session = Session::new();
    session.elab.options.limits = Limits {
        work: 5_000,
        ..Limits::default()
    };
    let source =
        format!("{REPLICATE}\ntheorem long : List.length (replicate 10000 1) = 10000 := rfl\n");
    let diagnostics = session.load("work.sw", &source).unwrap_err();
    let resource = diagnostics
        .iter()
        .find(|d| d.code == "E-RESOURCE")
        .unwrap_or_else(|| panic!("{diagnostics:?}"));
    let notes = resource.notes.join("\n");
    assert!(
        notes.contains("it happened while checking `long`"),
        "{notes}"
    );
    assert_eq!(resource.labels.len(), 1, "{resource:?}");
}

const SEARCH: &str = "import Std (List, Nat, Option)\n\n\
    def search (xs: List Nat) (number: Nat): Nat → Option Nat\n  \
    | 0 => None\n  \
    | Succ more =>\n    \
    if xs.all (x => x == 0) then Some number\n    \
    else search (xs.map (x => x - 1)) (Succ number) more\n\n\
    def answer (xs: List Nat): Option Nat := search xs 1 1000\n\n\
    def isSome: Option Nat → Bool\n  | Some _ => True\n  | None => False\n";

/// A `match` on a bounded search reads its scrutinee back only as far as
/// the largest term it could occur in (SW-982): here the type `Nat`, so it
/// checks under a size limit far below the size of the search unfolded
/// through its 1000 steps, each stuck on `xs`.
#[test]
fn a_match_reads_its_scrutinee_back_only_as_far_as_it_could_occur() {
    let mut session = Session::new();
    session.load("search.sw", SEARCH).expect("checks");
    session.elab.options.limits = Limits {
        size: 1_000,
        ..Limits::default()
    };
    session
        .load(
            "use.sw",
            "def describe (xs: List Nat): Nat :=\n  \
             match answer xs with\n    | Some n => n\n    | None => 0\n",
        )
        .expect("checks within the size limit");
}

/// A `match` whose goal does mention a scrutinee that large can't read the
/// goal back unfolded; it generalises the goal as written instead, with a
/// warning that copies hidden inside calls weren't looked for (SW-1630).
#[test]
fn a_match_whose_goal_is_too_large_to_read_back_uses_the_goal_as_written() {
    let mut session = Session::new();
    session.load("search.sw", SEARCH).expect("checks");
    session.elab.options.limits = Limits {
        size: 1_000,
        ..Limits::default()
    };
    session
        .load(
            "use.sw",
            "theorem same (xs: List Nat): isSome (answer xs) = isSome (answer xs) :=\n  \
             match answer xs with\n    | Some n => rfl\n    | None => rfl\n",
        )
        .expect("checks with the goal as written");
    assert!(
        session
            .warnings
            .iter()
            .any(|w| w.code == "W-MATCH-UNCONFIRMED"),
        "{:?}",
        session.warnings
    );
}

/// A proposition that doubles at each level, `P(i) x := P(i-1) x ∧ P(i-1) x`,
/// is 2^40 conjuncts unfolded but 41 calls glued. A hypothesis of it costs
/// nothing to bind in the kernel's signature check, nor in scope of an
/// `auto` argument decided by search (SW-1779: each of these once unfolded
/// it all, so depth 25 took minutes).
#[test]
fn a_doubling_hypothesis_is_never_unfolded_in_full() {
    let mut source = String::from("def P0 (x: Nat): Prop := x = x\n");
    for i in 1..=40 {
        source.push_str(&format!(
            "def P{i} (x: Nat): Prop := P{j} x ∧ P{j} x\n",
            j = i - 1
        ));
    }
    source.push_str(
        "def needs (k: Nat) [auto ok: k ≠ 0]: Nat := k\n\
         def f (n: Nat) (h: P40 n): Nat := needs 3\n",
    );
    let mut session = Session::new();
    session.elab.options.limits = Limits {
        work: 5_000_000,
        ..Limits::default()
    };
    session.load("doubling.sw", &source).expect("checks");
}

/// A proof that splits a list and rewrites in each arm: running out of stack
/// inside it, at any depth, leaves the elaborator's contexts and lifted
/// terms consistent for what is checked next.
const SPLIT_PROOF: &str = "
import Std (Add, Eq, List)

theorem sumByFlatMapAgain [auto add: Add c] (xs: List a) (f: b → c) (g: a → List b): List.sumBy (List.flatMap xs g) f = List.sumBy xs (x => List.sumBy (g x) f) :=
  match xs with
    | [] => rfl
    | [x, ..xs] =>
      Eq.trans (List.sumByAppend (g x) (List.flatMap xs g) f)
        (Eq.trans (Eq.cong (t => List.sumBy (g x) f + t) (sumByFlatMapAgain xs f g)) (Eq.sym (List.sumByCons xs x (x => List.sumBy (g x) f))))

def afterwards (n : Nat) : Nat := n + 1
";

/// With the stack guard at sizes from a few kilobytes up, a quarter again each time, loading either
/// succeeds or fails, and the first error is running out of resources; a
/// session that ran out checks a later file as usual. Debug builds run it
/// too: their arithmetic overflow checks are what notice contexts that
/// disagree after an error unwinds.
#[test]
fn running_out_of_stack_at_any_point_only_ever_means_no_answer() {
    const STACK: usize = 64 * 1024 * 1024;
    with_stack(STACK, || {
        let roomy = Limits::for_stack(STACK);
        let mut stack = 16 * 1024;
        loop {
            let mut session = Session::new();
            session.elab.options.limits = Limits { stack, ..roomy };
            let finished = match session.load("proof.sw", SPLIT_PROOF) {
                Err(diagnostics) => {
                    assert_eq!(
                        diagnostics[0].code, "E-RESOURCE",
                        "stack {stack}: {diagnostics:?}"
                    );
                    false
                }
                Ok(_) => true,
            };
            session.elab.options.limits = roomy;
            session
                .load(
                    "later.sw",
                    "def double (n : Nat) : Nat := n + n\n\ntest \"double\" := double 21 == 42\n",
                )
                .unwrap_or_else(|d| panic!("stack {stack}: a later file: {d:?}"));
            if finished {
                break;
            }
            stack += 1 + stack / 4;
            assert!(stack < roomy.stack, "never checked");
        }
    });
}
