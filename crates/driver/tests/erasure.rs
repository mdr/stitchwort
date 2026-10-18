//! Erasure when running (`crates/core/src/erase.rs`): skipping proofs and
//! types must not change what a program prints or whether its tests pass, and
//! must make programs that carry proofs in their data cheaper.
//!
//! Each comparison runs the same session twice, toggling
//! `Globals::erasure.set_disabled`, and compares outcomes and output.

use std::io::Cursor;
use std::path::Path;

use stitchwort_driver::driver::{Cache, Outcome, Session, with_stack};
use stitchwort_driver::run::Policy;

const STACK: usize = 64 * 1024 * 1024;

fn outcomes(session: &mut Session) -> Vec<(String, &'static str)> {
    session
        .run_tests(&Cache::disabled())
        .into_iter()
        .map(|r| {
            let o = match r.outcome {
                Outcome::Passed => "passed",
                Outcome::Failed => "failed",
                Outcome::OutOfResources(_) => "out of resources",
            };
            (r.name, o)
        })
        .collect()
}

/// Runs `f` with erasure on, then off: each result with the steps it took.
fn both<T>(session: &mut Session, mut f: impl FnMut(&mut Session) -> T) -> ((T, u64), (T, u64)) {
    let mut measure = |session: &mut Session, disabled: bool| {
        session.elab.globals.erasure.set_disabled(disabled);
        let before = session.elab.globals.budget.total_work();
        let result = f(session);
        let steps = session.elab.globals.budget.total_work() - before;
        session.elab.globals.erasure.set_disabled(false);
        (result, steps)
    };
    let with = measure(session, false);
    let without = measure(session, true);
    (with, without)
}

fn examples() -> Vec<(String, String)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut found = Vec::new();
    for dir in ["accept", "extract"] {
        let mut paths: Vec<_> = std::fs::read_dir(root.join(dir))
            .expect("examples directory")
            .map(|e| e.expect("entry").path())
            .filter(|p| p.extension().is_some_and(|e| e == "sw"))
            .collect();
        paths.sort();
        for path in paths {
            let name = format!("{dir}/{}", path.file_name().unwrap().to_string_lossy());
            found.push((name, std::fs::read_to_string(&path).expect("readable")));
        }
    }
    found
}

#[test]
fn erasure_doesnt_change_what_examples_print_or_test() {
    with_stack(STACK, || {
        let (mut tests_run, mut mains_run) = (0, 0);
        let (mut steps_with, mut steps_without) = (0u64, 0u64);
        let mut cheaper = Vec::new();
        for (name, text) in examples() {
            let mut session = Session::for_stack(STACK);
            session.load(&name, &text).expect("examples check");
            let ((a, wa), (b, wb)) = both(&mut session, outcomes);
            assert_eq!(a, b, "{name}: test outcomes differ");
            tests_run += a.len();
            steps_with += wa;
            steps_without += wb;
            if wa < wb {
                cheaper.push(format!("{name} (tests): {wa} < {wb}"));
            }
            // A program without a `main` that checks is skipped; one that
            // fails the same way both times is compared by its error code.
            if session.main().is_err() {
                continue;
            }
            let ((a, wa), (b, wb)) = both(&mut session, |s| {
                s.simulate(&[]).map_err(|d| d.code.to_string())
            });
            assert_eq!(a, b, "{name}: printed lines differ");
            if a.is_ok() {
                mains_run += 1;
            }
            if wa < wb {
                cheaper.push(format!("{name} (main): {wa} < {wb}"));
            }
        }
        eprintln!("tests: {tests_run}, mains: {mains_run}");
        eprintln!("test steps with erasure {steps_with}, without {steps_without}");
        for c in &cheaper {
            eprintln!("cheaper: {c}");
        }
        assert!(tests_run > 50, "only {tests_run} tests compared");
        assert!(mains_run > 0, "no main simulated");
        assert!(
            !cheaper.is_empty(),
            "erasure never did less work (is the toggle taking effect?)"
        );
    });
}

const POS: &str = r#"
type Pos = { at : Nat, ok : at < 100 }

wrap : Int -> Pos
wrap x = { at = Int.modNat x 100, ok = Int.modNatLt x 100 }

walk : List Text -> Pos -> Nat
walk Nil         p = p.at
walk (Cons t ts) p = walk ts (wrap (p.at.toInt + Nat.toInt (Text.length t * 37)))

main : () -> {IO, Partial} ()
main u = print (Nat.toText (walk (IO.readAllLines ()) (wrap 50)))
"#;

#[test]
fn proofs_in_data_cost_nothing_at_runtime() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session.load("pos.sw", POS).expect("checks");
        let main = session.main().expect("main");
        // Without erasure each line costs millions of steps (`Int.modNatLt`
        // runs), so the input is short.
        let input = "L68\n".repeat(20);
        let ((out_with, steps_with), (out_without, steps_without)) = both(&mut session, |s| {
            let mut out = Vec::new();
            let r = s.run_main_with(
                &main,
                &mut Cursor::new(input.as_bytes()),
                &mut out,
                &Policy::default(),
                &mut |_| {},
            );
            assert!(r.is_ok(), "the run failed");
            String::from_utf8(out).unwrap()
        });
        eprintln!("proof fields: with erasure {steps_with} steps, without {steps_without}");
        assert_eq!(out_with, out_without);
        assert!(!out_with.trim().is_empty());
        assert!(
            steps_with * 10 < steps_without,
            "{steps_with} steps with erasure is not under a tenth of {steps_without}"
        );
    });
}

/// Loads `source`; every test must pass with and without erasure. Returns
/// the steps taken with and without.
fn tests_pass_both_ways(source: &str, expected: usize) -> (u64, u64) {
    let mut session = Session::for_stack(STACK);
    if let Err(errors) = session.load("t.sw", source) {
        panic!("{errors:#?}");
    }
    let ((a, wa), (b, wb)) = both(&mut session, outcomes);
    assert_eq!(a.len(), expected);
    for (name, o) in a.iter().chain(b.iter()) {
        assert_eq!(*o, "passed", "{name}");
    }
    eprintln!("steps with erasure {wa}, without {wb}");
    (wa, wb)
}

/// Rule 4: `J` on a proof that's a function argument takes its base.
#[test]
fn j_on_an_erased_proof_argument() {
    tests_pass_both_ways(
        r#"
type Box (n : Nat) =
  | MkBox (v : Nat)

Box.value : [n : Nat] -> Box n -> Nat
Box.value (MkBox v) = v

castBox : [a b : Nat] -> a = b -> Box a -> Box b
castBox p x = J (\y q -> Box y) x p

test "transport keeps the payload" = Box.value (castBox (rfl : 2 + 2 = 4) (MkBox 7)) == 7
test "and through a symmetric proof" =
  Box.value (castBox (Eq.sym (rfl : 2 + 2 = 4)) (MkBox 9)) == 9
"#,
        2,
    );
}

/// Rule 5: a case on a one-constructor proposition with only proof fields,
/// producing data.
#[test]
fn subsingleton_elimination_on_an_erased_proof() {
    tests_pass_both_ways(
        r#"
type Both2 (p : Prop) (q : Prop) : Prop =
  | MkBoth2 (x : p) (y : q)

pick : [p q : Prop] -> Both2 p q -> Nat
pick (MkBoth2 x y) = 5

theorem twoProofs : Both2 (1 = 1) (2 = 2)
twoProofs = MkBoth2 rfl rfl

test "a literal proof" = pick (MkBoth2 (rfl : 1 = 1) (rfl : 3 = 3)) == 5
test "a theorem as the proof" = pick twoProofs == 5
"#,
        2,
    );
}

/// Rules 1 and 3: type and proof arguments, and a theorem used as one.
#[test]
fn type_and_proof_arguments_are_skipped() {
    tests_pass_both_ways(
        r#"
const : (a : Type) -> (n : Nat) -> n < 10 -> Nat
const a n p = n + 1

theorem small : 3 < 10
small = rfl

test "type and proof arguments" = const Nat 3 small == 4
test "a type computed by a function" = const (List Nat) 3 small == 4
"#,
        2,
    );
}

/// Rule 3: an expensive proof in a record's proof field is never run.
#[test]
fn an_expensive_proof_in_data_isnt_run() {
    let (with, without) = tests_pass_both_ways(
        r#"
theorem addZero : (n : Nat) -> n + 0 = n
addZero Zero     = rfl
addZero (Succ k) = Eq.cong Succ (addZero k)

type Wit = { n : Nat, ok : n + 0 = n }

mk : Nat -> Wit
mk k = { n = k, ok = addZero k }

test "the field's value" = (mk 2000).n == 2000
"#,
        1,
    );
    assert!(
        with < without,
        "{with} steps with erasure, {without} without"
    );
}
