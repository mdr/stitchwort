//! Stage N1 of docs/proposals/native-compilation.md: `run --native` against
//! the machine. For the three benchmarks at small sizes and a few small
//! programs in the subset, native code must print what the machine prints,
//! make the same allocation trace event for event, and run out of frames
//! and steps at exactly the machine's points (D1253).

mod common;

use common::*;
use stitchwort_driver::driver::with_stack;
use stitchwort_rt::{Limits, alloc_trace};

#[test]
fn the_benchmarks_agree_with_the_machine() {
    assert_eq!(agrees(&bench("micro_call.sw")), "20000\n");
    assert_eq!(agrees(&bench("micro_tail.sw")), "499500\n");
    assert_eq!(agrees(&bench("set_nat.sw")), "1000\n");
}

/// A sum that passes `u64::MAX`: the `Nat` fast paths fall back to big
/// numbers, which native code carries and matches like small ones.
const BIG_NUMBERS: &str = r#"import Std (IO)

def grow: Nat → Nat → Nat
  | Zero, acc => acc
  | Succ n, acc => grow n (acc * 3 + n)

def isBig (n: Nat): Nat := if 18446744073709551615 <= n then 1 else 0

def shrink: Nat → Nat
  | 0 => 100
  | 1 => 101
  | 18446744073709551616 => 102
  | Succ n => n

def run (k: Nat): Nat := grow k 1 + isBig (grow k 1) + shrink (grow 2 0) + shrink 18446744073709551616

def main(): {IO} () :=
  IO.print "${run 50}"
"#;

/// Mutual tail recursion between different functions (`return_call`),
/// constants computed natively, and a tree rebuilt with reuse.
const SHAPES: &str = r#"import Std (IO, List)

def even: Nat → Nat → Nat
  | Zero, acc => acc
  | Succ n, acc => odd n (acc + 2)

def odd: Nat → Nat → Nat
  | Zero, acc => acc
  | Succ n, acc => even n (acc + 1)

def table: List Nat := [3, 1, 4, 1, 5, 9, 2, 6]

def bump: List Nat → List Nat
  | [] => []
  | Cons x rest => Cons (x + 1) (bump rest)

def total: List Nat → Nat
  | [] => 0
  | Cons x rest => x + total rest

def run (n: Nat): Nat := even n 0 + total (bump (bump table)) + total table

def main(): {IO} () :=
  IO.print "${run 100001}"
"#;

#[test]
fn small_programs_agree_with_the_machine() {
    let big = agrees(BIG_NUMBERS);
    assert!(big.trim().len() > 20, "{big}");
    assert_eq!(agrees(SHAPES), format!("{}\n", 150002 + 47 + 31));
}

#[test]
fn the_allocation_traces_are_the_same() {
    same_trace(&bench("set_nat.sw"));
    same_trace(SHAPES);
}

/// A function applying function values it's given, one of which uses
/// `Text.fold` (which the machine runs for native code, stage N4): every
/// body `main` reaches but its entry runs natively, with the same output
/// and allocation trace. (Before N4, the call stayed on the machine.)
#[test]
fn a_function_value_using_text_fold_runs_natively() {
    let source = r#"import Std (IO, List, Text)

def applyAll: List (Text → Nat) → Text → Nat
  | [], t => 0
  | Cons f rest, t => f t + applyAll rest t

def main(): {IO} () :=
  IO.print "${applyAll [t => Text.fold t 0 (c n => n + 1), t => 7] "hello"}"
"#;
    assert_eq!(agrees(source), "12\n");
    same_trace(source);
    with_stack(STACK, move || {
        let (program, limits) = lowered(source);
        let (_, notes) = native(&program, limits, false);
        assert!(
            !notes
                .iter()
                .any(|n| n.contains("which native code doesn't compile")),
            "{notes:#?}"
        );
    });
}

/// `Text.fold` inside a recursive function: native code has the machine
/// run it, and the machine calls the compiled lambda back. (Before N4, the
/// whole run stayed on the machine.)
#[test]
fn text_fold_in_a_recursion_runs_natively() {
    let source = r#"import Std (IO, List, Text)

def count: List Text → Nat
  | [] => 0
  | Cons t rest => Text.fold t 0 (c n => n + 1) + count rest

def main(): {IO} () :=
  IO.print "${count ["hello", "you"]}"
"#;
    assert_eq!(agrees(source), "8\n");
    same_trace(source);
}

/// `run 3000` builds a list 3,000 deep and sums it twice, keeping it while
/// the first sum recurses. The smallest frame limit, and the smallest step
/// limit, under which it finishes are found for each runner by bisection:
/// they must be the same, one below must be `E-RESOURCE` on both, and
/// running out mid-recursion must free every cell.
#[test]
fn resources_run_out_at_the_machines_points() {
    let source = r#"import Std (IO, List)

def build: Nat → List Nat
  | Zero => []
  | Succ n => Cons n (build n)

def total: List Nat → Nat
  | [] => 0
  | Cons x rest => x + total rest

def run (n: Nat): Nat :=
  let xs := build n
  total xs + total xs

def main(): {IO} () :=
  IO.print "${run 3000}"
"#;
    with_stack(STACK, move || {
        let (program, limits) = lowered(source);
        let finishes_native = |limits: Limits| {
            let (ran, notes) = native(&program, limits, false);
            assert!(ran_natively(&notes), "{notes:#?}");
            ran.1.is_ok()
        };
        let finishes_machine = |limits: Limits| on_machine(&program, limits).1.is_ok();
        // The least `n` for which `finishes(n)`, given `finishes(high)`.
        let least = |finishes: &dyn Fn(u64) -> bool, high: u64| {
            let (mut low, mut high) = (0, high);
            while low < high {
                let mid = (low + high) / 2;
                if finishes(mid) {
                    high = mid;
                } else {
                    low = mid + 1;
                }
            }
            low
        };
        let frames = |n: u64| Limits {
            frames: n as usize,
            ..limits
        };
        let steps = |n: u64| Limits { steps: n, ..limits };
        let machine_frames = least(&|n| finishes_machine(frames(n)), 10_000);
        let native_frames = least(&|n| finishes_native(frames(n)), 10_000);
        assert_eq!(native_frames, machine_frames);
        assert!(machine_frames > 3000, "{machine_frames}");
        let machine_steps = least(&|n| finishes_machine(steps(n)), 100_000);
        let native_steps = least(&|n| finishes_native(steps(n)), 100_000);
        assert_eq!(native_steps, machine_steps);

        let short = native(&program, frames(machine_frames - 1), false).0;
        assert_eq!(short, on_machine(&program, frames(machine_frames - 1)));
        assert_eq!(short.1, Err("out of frames".to_string()));
        let short = native(&program, steps(machine_steps - 1), false).0;
        assert_eq!(short, on_machine(&program, steps(machine_steps - 1)));
        assert_eq!(short.1, Err("out of steps".to_string()));

        // Running out mid-recursion frees every cell native code held.
        alloc_trace::start();
        let ran = native(&program, frames(machine_frames - 1), true).0;
        let trace = alloc_trace::finish();
        assert_eq!(ran.1, Err("out of frames".to_string()));
        assert_eq!(trace.leaks(), Vec::<u32>::new());
    });
}

/// Values live across calls of every kind (a direct call, a function value
/// applied, a constant computed the first time, tail calls), in registers
/// that native code keeps in machine registers (stage N2a). For every step
/// limit and every frame limit up to the least under which the run
/// finishes, the run stops where the machine's does, with the same output,
/// and frees every cell: so each error exit, wherever it is, releases
/// exactly the registers live there.
#[test]
fn every_error_exit_frees_the_live_registers() {
    let source = r#"import Std (IO, List)

def big: Nat := 18446744073709551616 + 5

def total: List Nat → Nat
  | [] => 0
  | Cons x rest => x + total rest

def inc (m: Nat): Nat := m + 1

def twice (f: Nat → Nat) (x: Nat): Nat := f (f x)

def count: Nat → Nat → Nat
  | Zero, acc => acc
  | Succ n, acc => count n (acc + 1)

def keep: Nat → List Nat → Nat
  | Zero, xs => total xs
  | Succ n, xs =>
    let ys := [n, n + big]
    let a := keep n ys
    let b := twice inc a
    a + b + total xs + total ys + count n 0

def run (n: Nat): Nat := keep n [1, 2, 3]

def main(): {IO} () :=
  IO.print "${run 3}"
"#;
    with_stack(STACK, move || {
        let (program, limits) = lowered(source);
        let machine = on_machine(&program, limits);
        assert!(machine.1.is_ok(), "{machine:?}");
        // The least limit under which the run finishes, checking every
        // limit below it.
        let sweep = |limits_at: &dyn Fn(u64) -> Limits| {
            let mut k = 0;
            loop {
                let limits = limits_at(k);
                let expected = on_machine(&program, limits);
                alloc_trace::start();
                let (ran, notes) = native(&program, limits, false);
                let trace = alloc_trace::finish();
                assert!(ran_natively(&notes), "{notes:#?}");
                assert_eq!(ran, expected, "at limit {k}");
                assert_eq!(trace.leaks(), Vec::<u32>::new(), "leaked at limit {k}");
                if expected.1.is_ok() {
                    return k;
                }
                k += 1;
            }
        };
        let least_steps = sweep(&|n| Limits { steps: n, ..limits });
        let least_frames = sweep(&|n| Limits {
            frames: n as usize,
            ..limits
        });
        assert!(least_steps > 20, "{least_steps}");
        assert!(least_frames > 5, "{least_frames}");
    });
}
