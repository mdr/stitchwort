//! Running indexed families (docs/proposals/indexed-families.md §6.8, §8.1,
//! §9): with and without erasure a program computes the same, a family's
//! proof fields are erased while its data fields (forced implicit ones
//! included) are kept, and the linear `fromList` really is linear.
//!
//! The accept example `examples/accept/indexed-families.sw` is also run with
//! and without erasure by `erasure.rs`, which covers every accepted example.

use stitchwort_driver::driver::{Cache, Outcome, Session, with_stack};

const STACK: usize = 64 * 1024 * 1024;

const VEC: &str = "
import Std (List, Nat, Void)

type Vec (a: Type): Nat -> Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def toList: Vec a n -> List a
  | VNil       => Nil
  | VCons x xs => Cons x (toList xs)
";

/// Loads `source`, runs its tests with erasure on and then off, and returns
/// the number of tests and the steps each run took. Every test must pass both
/// ways.
fn run_both_ways(source: &str) -> (usize, u64, u64) {
    let mut session = Session::for_stack(STACK);
    if let Err(errors) = session.load("t.sw", source) {
        panic!("{errors:#?}");
    }
    let run = |disabled: bool| {
        session.elab.globals.erasure.set_disabled(disabled);
        let before = session.elab.globals.budget.total_work();
        let results = session.run_tests(&Cache::disabled());
        let steps = session.elab.globals.budget.total_work() - before;
        session.elab.globals.erasure.set_disabled(false);
        for r in &results {
            assert!(
                matches!(r.outcome, Outcome::Passed),
                "{} (erasure disabled: {disabled})",
                r.name
            );
        }
        (results.len(), steps)
    };
    let (n, with) = run(false);
    let (m, without) = run(true);
    assert_eq!(n, m);
    (n, with, without)
}

#[test]
fn the_vec_examples_agree_with_and_without_erasure() {
    with_stack(STACK, || {
        let source = format!(
            "{VEC}
def append: Vec a n -> Vec a m -> Vec a (n + m)
  | VNil, ys       => ys
  | VCons x xs, ys => VCons x (append xs ys)

def zipWith (f: a -> b -> c): Vec a n -> Vec b n -> Vec c n
  | VNil, VNil             => VNil
  | VCons x xs, VCons y ys => VCons (f x y) (zipWith f xs ys)

def head: Vec a (Succ n) -> a
  | VCons x _ => x

def replicate: (n: Nat) -> a -> Vec a n
  | Zero, _   => VNil
  | Succ k, x => VCons x (replicate k x)

def length: Vec a n -> Nat
  | VNil               => 0
  | VCons [n := k] _ _ => Succ k

test \"append\" := toList (append (replicate 2 7) (replicate 3 8)) == [7, 7, 8, 8, 8]
test \"zipWith\" := toList (zipWith (a b => a + b) (replicate 3 1) (replicate 3 2)) == [3, 3, 3]
test \"head\" := head (VCons 5 (replicate 2 6)) == 5
test \"the forced field is stored\" := length (append (replicate 4 0) (replicate 5 0)) == 9
"
        );
        let (tests, _, _) = run_both_ways(&source);
        assert_eq!(tests, 4);
    });
}

/// `Certified` has an index, a data field `n` (written, so not implicit), and
/// a proof field whose value is costly to compute. `CVec` has a forced
/// implicit data field `n` beside a proof field `ok`. The proof fields are
/// erased (the work disappears), the data fields are kept (the results are the
/// same).
const CERTIFIED: &str = "
import Std (Nat)

type Certified: Nat -> Type =
  | MkCertified (n: Nat) (ok: n + 3000 = 3000 + n): Certified n

def Certified.value: Certified n -> Nat
  | MkCertified v _ => v

def certify (n: Nat): Certified n := MkCertified n (Nat.addComm n 3000)

type CVec (a: Type): Nat -> Type =
  | CNil: CVec a 0
  | CCons (x: a) (ok: x = x) (xs: CVec a n): CVec a (Succ n)

def CVec.length: CVec a n -> Nat
  | CNil                 => 0
  | CCons [n := k] _ _ _ => Succ k

def CVec.sum: CVec Nat n -> Nat
  | CNil         => 0
  | CCons x _ xs => x + CVec.sum xs

test \"a data field is kept\" := Certified.value (certify 41) == 41
test \"and read through a pattern\" := Certified.value (certify 7) + 1 == 8
test \"forced implicit fields are kept\" :=
  CVec.length (CCons 1 rfl (CCons 2 rfl (CCons 3 rfl CNil))) == 3
test \"and the other fields too\" :=
  CVec.sum (CCons 1 rfl (CCons 2 rfl (CCons 3 rfl CNil))) == 6
";

#[test]
fn proof_fields_are_erased_and_data_fields_kept() {
    with_stack(STACK, || {
        let (tests, with, without) = run_both_ways(CERTIFIED);
        assert_eq!(tests, 4);
        eprintln!("Certified: with erasure {with} steps, without {without}");
        assert!(
            with * 3 < without,
            "{with} steps with erasure is not well under {without} without: \
             was the proof field erased?"
        );
    });
}

/// The steps that running the tests of `source` takes, with erasure.
fn steps(source: &str) -> u64 {
    let mut session = Session::for_stack(STACK);
    if let Err(errors) = session.load("t.sw", source) {
        panic!("{errors:#?}");
    }
    let before = session.elab.globals.budget.total_work();
    let results = session.run_tests(&Cache::disabled());
    assert!(
        results.iter().all(|r| matches!(r.outcome, Outcome::Passed)),
        "{:?}",
        results.iter().map(|r| &r.name).collect::<Vec<_>>()
    );
    session.elab.globals.budget.total_work() - before
}

/// §8.1's linear `fromList`: it passes the length down, so every stored `n`
/// is a number already computed.
fn linear_program(n: usize) -> String {
    format!(
        "{VEC}
def fromListN: (n: Nat) -> (xs: List a) -> List.length xs = n -> Vec a n
  | 0, Nil, _             => VNil
  | Succ k, Cons x xs, ok => VCons [n := k] x (fromListN k xs (Nat.succInjective _ _ ok))
  | 0, Cons _ _, ok       => Void.absurd (Nat.succNotZero _ ok)
  | Succ _, Nil, ok       => Void.absurd (Nat.zeroNotSucc _ ok)

def fromList (xs: List a): Vec a (List.length xs) := fromListN (List.length xs) xs rfl

test \"round trip\" := List.length (toList (fromList (List.range {n}))) == {n}
"
    )
}

/// The same with the length recomputed at every step (§8.1 as first
/// written): quadratic.
fn quadratic_program(n: usize) -> String {
    format!(
        "{VEC}
def fromList: (xs: List a) -> Vec a (List.length xs)
  | Nil       => VNil
  | Cons x xs => VCons x (fromList xs)

test \"round trip\" := List.length (toList (fromList (List.range {n}))) == {n}
"
    )
}

#[test]
fn the_linear_from_list_takes_linear_time() {
    with_stack(STACK, || {
        let (small, large) = (steps(&linear_program(8000)), steps(&linear_program(16000)));
        let ratio = large as f64 / small as f64;
        eprintln!("linear fromList: 8000 -> {small} steps, 16000 -> {large} ({ratio:.2}x)");
        // Twice the elements: about twice the work, where quadratic is four times.
        assert!(
            ratio < 2.5,
            "doubling the input multiplied the work by {ratio:.2}"
        );
    });
}

#[test]
fn the_first_from_list_is_quadratic() {
    // Guards the test above: this measurement tells the two apart.
    with_stack(STACK, || {
        let (small, large) = (
            steps(&quadratic_program(400)),
            steps(&quadratic_program(800)),
        );
        let ratio = large as f64 / small as f64;
        eprintln!("quadratic fromList: 400 -> {small} steps, 800 -> {large} ({ratio:.2}x)");
        assert!(
            ratio > 3.0,
            "doubling the input multiplied the work by {ratio:.2}"
        );
    });
}
