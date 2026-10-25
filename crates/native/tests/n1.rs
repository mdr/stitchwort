//! Stage N1 of docs/proposals/native-compilation.md: `run --native` against
//! the machine. For the three benchmarks at small sizes and a few small
//! programs in the subset, native code must print what the machine prints,
//! make the same allocation trace event for event, and run out of frames
//! and steps at exactly the machine's points (D1253).

use std::cell::RefCell;
use std::path::Path;
use std::rc::Rc;

use stitchwort_core::ResourceError;
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_native::n1::{Options, factory};
use stitchwort_rt::host::RunError;
use stitchwort_rt::{Limits, Program, alloc_trace, lower_main, run_main, run_main_native};

const STACK: usize = 512 * 1024 * 1024;

fn bench(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../bench/native")
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// `source` checked and its `main` lowered, with the default limits.
fn lowered(source: &str) -> (Program, Limits) {
    let mut session = Session::for_stack(STACK);
    session
        .load("test.sw", source)
        .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
    let main = session.main().expect("`main` has the right type");
    let program = lower_main(
        &session.elab.globals,
        session.elab.limits,
        main.term(),
        main.row,
    )
    .expect("lowers");
    (program, Limits::from_core(session.elab.limits))
}

/// How a run ended: what it printed, and the error if any.
type Ran = (String, Result<(), String>);

fn ended(output: Vec<u8>, result: Result<(), RunError>) -> Ran {
    (
        String::from_utf8(output).expect("text"),
        result.map_err(|e| match e {
            RunError::Resource(ResourceError::Work) => "out of steps".to_string(),
            RunError::Resource(ResourceError::Depth) => "out of frames".to_string(),
            other => other.to_string(),
        }),
    )
}

fn on_machine(program: &Program, limits: Limits) -> Ran {
    let mut output = Vec::new();
    let result = run_main(program, limits, &mut "".as_bytes(), &mut output);
    ended(output, result)
}

/// The run with native code, and the notes on what ran natively.
fn native(program: &Program, limits: Limits, trace_refcounts: bool) -> (Ran, Vec<String>) {
    let notes = Rc::new(RefCell::new(Vec::new()));
    let options = Options {
        trace_refcounts,
        stack_size: Some(STACK),
    };
    let mut make = factory(options, notes.clone());
    let mut output = Vec::new();
    let result = run_main_native(program, limits, &mut make, &mut "".as_bytes(), &mut output);
    let notes = notes.borrow().clone();
    (ended(output, result), notes)
}

fn ran_natively(notes: &[String]) -> bool {
    notes.iter().any(|n| n.starts_with("native: running "))
}

/// Native code prints what the machine prints, and did run.
fn agrees(source: &str) -> String {
    let source = source.to_string();
    with_stack(STACK, move || {
        let (program, limits) = lowered(&source);
        let machine = on_machine(&program, limits);
        let (native, notes) = native(&program, limits, false);
        assert!(ran_natively(&notes), "nothing ran natively: {notes:#?}");
        assert_eq!(native, machine, "{notes:#?}");
        machine.0
    })
}

/// The allocation traces of the machine and native code (counting through
/// the runtime), each from the start of its run, are the same text, and
/// native code frees every cell.
fn same_trace(source: &str) {
    let source = source.to_string();
    with_stack(STACK, move || {
        let (program, limits) = lowered(&source);
        // Out of the traces (its own values would be in the first).
        stitchwort_rt::native_abi::probe_layout().expect("the layout is as expected");
        let trace = |native_code: bool| {
            alloc_trace::start();
            let ran = if native_code {
                let (ran, notes) = native(&program, limits, true);
                assert!(ran_natively(&notes), "nothing ran natively: {notes:#?}");
                ran
            } else {
                on_machine(&program, limits)
            };
            (ran, alloc_trace::finish())
        };
        let (machine_ran, machine) = trace(false);
        let (native_ran, native) = trace(true);
        assert_eq!(native_ran, machine_ran);
        assert!(machine.count("alloc") > 0, "the program allocates nothing");
        assert_eq!(native.leaks(), Vec::<u32>::new(), "native code leaked");
        let (machine, native) = (machine.render(), native.render());
        // For reading the two side by side.
        if let Ok(dir) = std::env::var("N1_TRACE_DIR") {
            std::fs::write(format!("{dir}/machine.trace"), &machine).expect("writes");
            std::fs::write(format!("{dir}/native.trace"), &native).expect("writes");
        }
        if machine != native {
            let first = machine
                .lines()
                .zip(native.lines())
                .position(|(a, b)| a != b)
                .unwrap_or(machine.lines().count().min(native.lines().count()));
            panic!(
                "the traces differ from event {first}: machine {:?}, native {:?}",
                machine.lines().nth(first),
                native.lines().nth(first)
            );
        }
    });
}

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

/// A root that applies a function value it's given: the island fits, but
/// the call has a function in its arguments, so it runs on the machine.
#[test]
fn a_function_value_from_outside_keeps_the_call_on_the_machine() {
    let source = r#"import Std (IO, List)

def applyAll: List (Nat → Nat) → Nat → Nat
  | [], x => x
  | Cons f rest, x => applyAll rest (f x)

def main(): {IO} () :=
  IO.print "${applyAll [n => n + 3, n => n + 3] 4}"
"#;
    with_stack(STACK, move || {
        let (program, limits) = lowered(source);
        let machine = on_machine(&program, limits);
        let (native, notes) = native(&program, limits, false);
        assert_eq!(native, machine);
        assert_eq!(machine.0, "10\n");
        assert!(
            notes
                .iter()
                .any(|n| n.contains("was given a function value")),
            "{notes:#?}"
        );
    });
}

/// An island with an instruction outside N1 keeps the whole run on the
/// machine, and says why.
#[test]
fn an_island_outside_the_subset_runs_on_the_machine() {
    let source = r#"import Std (IO, Text)

def shout: Nat → Text → Text
  | Zero, t => t
  | Succ k, t => shout k (t ++ "!")

def main(): {IO} () :=
  IO.print (shout 1 "hi")
"#;
    with_stack(STACK, move || {
        let (program, limits) = lowered(source);
        let (native, notes) = native(&program, limits, false);
        assert_eq!(native, ("hi!\n".to_string(), Ok(())));
        assert!(!ran_natively(&notes), "{notes:#?}");
        assert!(
            notes.iter().any(|n| n.contains("which N1 doesn't compile")),
            "{notes:#?}"
        );
    });
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
