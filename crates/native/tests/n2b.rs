//! Stage N2b of docs/proposals/native-compilation.md: the safety work after
//! N2a, against the machine.
//!
//! - The frame counter fires before the stack can run out: recursion to
//!   exactly the frame limit, in the widest functions that can be built,
//!   ends as the machine's does, on a stack sized by the rule in
//!   `stitchwort_native::frames`; and the bound that rule uses is at least
//!   what the code really uses.
//! - Tail calls of every shape run in constant native stack (ten million
//!   iterations), and agree with the machine's output, allocation traces
//!   and least step and frame limits.
//! - The allocation trace of each error exit is event-identical to the
//!   machine's.

use std::cell::RefCell;
use std::rc::Rc;

use stitchwort_core::ResourceError;
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_native::frames;
use stitchwort_native::n1::{Options, factory};
use stitchwort_rt::host::{NoTerminal, RunError};
use stitchwort_rt::{Limits, Program, alloc_trace, lower_main, run_main, run_main_native};

/// The stack of the thread the tests run on, unless a test sizes its own.
const STACK: usize = 4 * 1024 * 1024 * 1024;

fn lowered(source: &str, stack: usize) -> (Program, Limits) {
    let mut session = Session::for_stack(stack);
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
            RunError::Resource(ResourceError::Depth) | RunError::Deep(_) => {
                "out of frames".to_string()
            }
            other => other.to_string(),
        }),
    )
}

fn on_machine(program: &Program, limits: Limits) -> Ran {
    let mut output = Vec::new();
    let result = run_main(program, limits, &mut "".as_bytes(), &mut output);
    ended(output, result)
}

/// The run with native code on a stack of `stack` bytes, and the notes.
fn native_on(
    program: &Program,
    limits: Limits,
    trace_refcounts: bool,
    stack: usize,
) -> (Ran, Vec<String>) {
    let notes = Rc::new(RefCell::new(Vec::new()));
    let options = Options {
        trace_refcounts,
        stack_size: Some(stack),
    };
    let mut make = factory(options, notes.clone());
    let mut output = Vec::new();
    let result = run_main_native(
        program,
        limits,
        &mut make,
        &mut "".as_bytes(),
        &mut output,
        &mut NoTerminal,
    );
    let notes = notes.borrow().clone();
    (ended(output, result), notes)
}

fn native(program: &Program, limits: Limits, trace_refcounts: bool) -> (Ran, Vec<String>) {
    native_on(program, limits, trace_refcounts, STACK)
}

fn ran_natively(notes: &[String]) -> bool {
    notes.iter().any(|n| n.starts_with("native: running "))
        && !notes.iter().any(|n| n.contains("ran on the machine"))
}

/// The widest body's frame bound, from the note on what ran natively.
fn frame_bound(notes: &[String]) -> usize {
    let note = notes
        .iter()
        .find(|n| n.starts_with("native: running "))
        .unwrap_or_else(|| panic!("nothing ran natively: {notes:#?}"));
    let after = note.split("frames of at most ").nth(1).expect("the bound");
    after
        .split(' ')
        .next()
        .and_then(|n| n.parse().ok())
        .expect("a number of bytes")
}

/// The least `n` for which `finishes(n)`, given `finishes(high)`.
fn least(finishes: &dyn Fn(u64) -> bool, high: u64) -> u64 {
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
}

fn with_frames(limits: Limits, n: u64) -> Limits {
    Limits {
        frames: n as usize,
        ..limits
    }
}

fn with_steps(limits: Limits, n: u64) -> Limits {
    Limits { steps: n, ..limits }
}

/// The allocation traces of the machine and of native code (counting
/// through the runtime) under `limits`, each from the start of its run:
/// the same outcome, the same events, and no cell leaked. `what` says where
/// in a sweep this is.
fn same_trace_under(program: &Program, limits: Limits, what: &str) {
    alloc_trace::start();
    let machine_ran = on_machine(program, limits);
    let machine = alloc_trace::finish();
    alloc_trace::start();
    let (native_ran, notes) = native(program, limits, true);
    let native = alloc_trace::finish();
    assert!(ran_natively(&notes), "nothing ran natively: {notes:#?}");
    assert_eq!(native_ran, machine_ran, "{what}");
    assert_eq!(native.leaks(), Vec::<u32>::new(), "{what}: native leaked");
    assert_eq!(machine.leaks(), Vec::<u32>::new(), "{what}: machine leaked");
    let (machine, native) = (machine.render(), native.render());
    if machine != native {
        let first = machine
            .lines()
            .zip(native.lines())
            .position(|(a, b)| a != b)
            .unwrap_or(machine.lines().count().min(native.lines().count()));
        let window = |text: &str| {
            text.lines()
                .skip(first.saturating_sub(6))
                .take(14)
                .collect::<Vec<_>>()
                .join(" | ")
        };
        panic!(
            "{what}: the traces differ from event {first}:\n machine {}\n native  {}",
            window(&machine),
            window(&native)
        );
    }
}

// ------------------------------------------------------------ stack sizing

/// A non-tail recursion `deep` on `width` Nat arguments, each live across
/// the call, `depth` deep: wide frames
/// with many live values.
fn wide_recursion(width: usize, depth: u64) -> String {
    let names: Vec<String> = (0..width).map(|i| format!("a{i}")).collect();
    let pattern = names.join(", ");
    let shifted: Vec<String> = names
        .iter()
        .enumerate()
        .map(|(i, _)| format!("(a{} + {})", (i + 1) % width, i + 1))
        .collect();
    let arrows = vec!["Nat"; width + 1].join(" → ");
    let live = names.join(" + ");
    let zeros = vec!["0"; width].join(" ");
    format!(
        r#"import Std (IO, List)

def deep: Nat → {arrows}
  | Zero, {pattern} => {live}
  | Succ p, {pattern} =>
    let r := deep p {shifted}
    r + {live}

def main(): {{IO}} () :=
  IO.print "${{deep {depth} {zeros}}}"
"#,
        shifted = shifted.join(" "),
    )
}

/// Recursing to exactly the frame limit, in the widest functions that can
/// be built, on a stack sized by the rule: the run ends as the machine's
/// does (the same output, and one frame fewer is the same error), the stack
/// check never fires first, and the bound is at least what the code uses.
#[test]
fn recursion_to_the_frame_limit_stops_at_the_counter() {
    for (width, depth) in [(1, 20_000), (6, 20_000), (12, 20_000)] {
        let source = wide_recursion(width, depth);
        // The host's stack for the checker and the runs: well above what the
        // native stack below needs.
        let host = 1024 * 1024 * 1024;
        with_stack(host, move || {
            let (program, limits) = lowered(&source, host);
            let expected = on_machine(&program, limits);
            assert!(expected.1.is_ok(), "width {width}: {expected:?}");
            // The frames the machine needs for it.
            let exact = least(
                &|n| on_machine(&program, with_frames(limits, n)).1.is_ok(),
                depth + 100,
            );
            assert!(exact > depth, "width {width}: {exact}");
            // The bound, and the stack the rule asks for at that limit.
            let (_, notes) = native_on(&program, with_frames(limits, exact), false, host / 2);
            let bound = frame_bound(&notes);
            let needed = frames::HOST_ROOM + frames::HELPER_ROOM + bound + exact as usize * bound;
            assert!(needed < host, "width {width}: needs {needed}");
            assert!(
                frames::counter_fires_first(exact, needed, bound),
                "width {width}"
            );

            let at = native_on(&program, with_frames(limits, exact), false, needed);
            assert!(ran_natively(&at.1), "width {width}: {:#?}", at.1);
            assert_eq!(at.0, expected, "width {width}, at the limit");
            let under = native_on(&program, with_frames(limits, exact - 1), false, needed);
            assert_eq!(
                under.0,
                on_machine(&program, with_frames(limits, exact - 1)),
                "width {width}, one under"
            );
            assert_eq!(under.0.1, Err("out of frames".to_string()), "width {width}");
        });
    }
}

/// With a stack too small for the frame limit to be sure of, the call stays
/// on the machine (and says so), so the run is the machine's: it never
/// reaches a stack it can't hold.
#[test]
fn a_stack_too_small_for_the_limit_keeps_the_run_on_the_machine() {
    let source = wide_recursion(12, 20_000);
    let host = 1024 * 1024 * 1024;
    with_stack(host, move || {
        let (program, limits) = lowered(&source, host);
        let (_, notes) = native_on(&program, limits, false, host / 2);
        let bound = frame_bound(&notes);
        let expected = on_machine(&program, limits);
        assert!(expected.1.is_ok());
        // Room for a tenth of the frames the run needs, under a limit that
        // the run reaches (2,000,000 is the default).
        let size = frames::HOST_ROOM + frames::HELPER_ROOM + bound * 2_000;
        let (ran, notes) = native_on(&program, limits, false, size);
        assert_eq!(ran, expected, "{notes:#?}");
        assert!(
            notes.iter().any(|n| n.contains("ran on the machine")),
            "{notes:#?}"
        );
        // Nor can a stack smaller than the rooms alone run anything.
        let (ran, notes) = native_on(&program, limits, false, 1024 * 1024);
        assert_eq!(ran, expected, "{notes:#?}");
        assert!(
            notes.iter().any(|n| n.contains("ran on the machine")),
            "{notes:#?}"
        );
        // A limit that does fit runs natively, on the same stack.
        let fits = (size - frames::HOST_ROOM - frames::HELPER_ROOM) as u64 / bound as u64 - 1;
        let (ran, notes) = native_on(&program, with_frames(limits, fits), false, size);
        assert!(ran_natively(&notes), "{notes:#?}");
        assert_eq!(ran.1, Err("out of frames".to_string()));
    });
}

// ------------------------------------------------------------- tail calls

/// A program for each calling shape of a tail call: `{N}` is the number of
/// iterations. Each prints a number that depends on every iteration.
fn tail_shapes() -> Vec<(&'static str, &'static str)> {
    vec![
        (
            "direct",
            r#"import Std (IO)

def spin: Nat → Nat → Nat
  | Zero, acc => acc
  | Succ n, acc => spin n (acc + n)

def main(): {IO} () :=
  IO.print "${spin {N} 0}"
"#,
        ),
        (
            "through a function value picked at each step",
            r#"import Std (IO)

def left (k: Nat) (acc: Nat): Nat := acc + k
def right (k: Nat) (acc: Nat): Nat := acc + 2 * k

def through (f: Nat → Nat → Nat) (k: Nat) (acc: Nat): Nat := f k acc

def drive: Nat → Nat → Nat
  | Zero, acc => acc
  | Succ n, acc => drive n (through (if n % 2 == 0 then left else right) n acc)

def main(): {IO} () :=
  IO.print "${drive {N} 0}"
"#,
        ),
        (
            "through a function value (a tail apply in each iteration)",
            r#"import Std (IO)

def leaf (k: Nat) (acc: Nat): Nat := acc + k

def through (f: Nat → Nat → Nat) (k: Nat) (acc: Nat): Nat := f k acc

def drive: Nat → Nat → Nat
  | Zero, acc => acc
  | Succ n, acc => drive n (through leaf n acc)

def main(): {IO} () :=
  IO.print "${drive {N} 0}"
"#,
        ),
        (
            "mutual recursion",
            r#"import Std (IO)

def ping: Nat → Nat → Nat
  | Zero, acc => acc
  | Succ n, acc => pong n (acc + 1)

def pong: Nat → Nat → Nat
  | Zero, acc => acc + 7
  | Succ n, acc => ping n (acc + 2)

def main(): {IO} () :=
  IO.print "${ping {N} 0}"
"#,
        ),
        (
            "next to runtime helpers",
            r#"import Std (IO, List)

def big: Nat := 18446744073709551616

def mixed: Nat → List Nat → Nat → Nat
  | Zero, xs, acc => acc
  | Succ n, Nil, acc => mixed n [acc] acc
  | Succ n, Cons x _, acc =>
    let y := (x + big) - big
    mixed n [y + 1, n] (acc + y)

def main(): {IO} () :=
  IO.print "${mixed {N} [] 0}"
"#,
        ),
        (
            "wide argument lists",
            r#"import Std (IO)

def wide: Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat
  | Zero, a, b, c, d, e, f, g, h, i, j, k, l, m => a + b + c + d + e + f + g + h + i + j + k + l + m
  | Succ n, a, b, c, d, e, f, g, h, i, j, k, l, m =>
    wide n b c d e f g h i j k l m (a + 1)

def main(): {IO} () :=
  IO.print "${wide {N} 1 2 3 4 5 6 7 8 9 10 11 12 13}"
"#,
        ),
        (
            "to a wider callee than the caller's",
            r#"import Std (IO)

def narrow: Nat → Nat → Nat
  | Zero, a => a
  | Succ n, a => wider n a 1 2 3 4 5 6 7 8 9 10 11 12 13 14

def wider: Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat
  | n, a, b, c, d, e, f, g, h, i, j, k, l, m, o, p =>
    narrow n (a + b + c + d + e + f + g + h + i + j + k + l + m + o + p)

def main(): {IO} () :=
  IO.print "${narrow {N} 0}"
"#,
        ),
        (
            "from a frame with live registers to free",
            r#"import Std (IO, List)

def total: List Nat → Nat
  | [] => 0
  | Cons x rest => x + total rest

def live: Nat → List Nat → Nat → Nat
  | Zero, xs, acc => acc + total xs
  | Succ n, xs, acc =>
    let ys := [n, acc]
    let zs := Cons acc ys
    let a := total ys
    let b := total zs
    let c := total xs
    live n [a + 1, b] ((acc + a + b + c) - (a + b + c) + 1)

def main(): {IO} () :=
  IO.print "${live {N} [] 0}"
"#,
        ),
    ]
}

/// Native code runs ten million iterations of every tail-call shape in
/// constant native stack: the thread has 64 MiB, so a leak of even 8 bytes
/// an iteration would run it off the end. The frame limit is small (a tail
/// loop pends only a few frames). The output is the machine's at the
/// iterations the machine runs in good time (200,000); the traces and
/// least limits are in the next test.
#[test]
fn tail_calls_of_every_shape_run_in_constant_stack() {
    const SMALL: usize = 64 * 1024 * 1024;
    for (name, template) in tail_shapes() {
        for (iterations, check_machine) in [("200000", true), ("10000000", false)] {
            let source = template.replace("{N}", iterations);
            with_stack(SMALL, move || {
                let (program, limits) = lowered(&source, SMALL);
                let limits = with_frames(limits, 1000);
                let (ran, notes) = native_on(&program, limits, false, SMALL);
                assert!(ran_natively(&notes), "{name}: {notes:#?}");
                assert!(ran.1.is_ok(), "{name} at {iterations}: {ran:?}");
                if check_machine {
                    assert_eq!(ran, on_machine(&program, limits), "{name}: {notes:#?}");
                }
            });
        }
    }
}

/// Every tail-call shape, at a few hundred iterations: the allocation
/// traces are event for event the machine's, and the least step and frame
/// limits are the same.
#[test]
fn tail_calls_of_every_shape_agree_with_the_machine() {
    for (name, template) in tail_shapes() {
        let source = template.replace("{N}", "300");
        with_stack(STACK, move || {
            let (program, limits) = lowered(&source, STACK);
            // A frame limit a stack of 4 GiB holds for the widest frames.
            let limits = with_frames(limits, 1_000_000);
            let machine = on_machine(&program, limits);
            assert!(machine.1.is_ok(), "{name}: {machine:?}");
            let (ran, notes) = native(&program, limits, false);
            assert!(ran_natively(&notes), "{name}: {notes:#?}");
            assert_eq!(ran, machine, "{name}");

            let finishes_machine = |l: Limits| on_machine(&program, l).1.is_ok();
            let finishes_native = |l: Limits| native(&program, l, false).0.1.is_ok();
            let machine_steps = least(&|n| finishes_machine(with_steps(limits, n)), 100_000);
            let native_steps = least(&|n| finishes_native(with_steps(limits, n)), 100_000);
            assert_eq!(native_steps, machine_steps, "{name}: least steps");
            assert!(machine_steps >= 100, "{name}: {machine_steps}");
            let machine_frames = least(&|n| finishes_machine(with_frames(limits, n)), 1_000);
            let native_frames = least(&|n| finishes_native(with_frames(limits, n)), 1_000);
            assert_eq!(native_frames, machine_frames, "{name}: least frames");

            // One under each limit is the same error with the same trace.
            for limits in [
                with_steps(limits, machine_steps - 1),
                with_frames(limits, machine_frames - 1),
                limits,
            ] {
                same_trace_under(&program, limits, name);
            }
        });
    }
}

// ----------------------------------------------------------- error traces

/// The program of N2a's error-exit sweep: values live across direct calls,
/// `Apply`, a constant's first computation and tail calls.
const EXITS: &str = r#"import Std (IO, List)

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

/// Every step limit and every frame limit up to the least that finishes
/// `source`: the allocation trace on the error exit (every allocation, and
/// every count, in order) is the machine's, event for event.
fn sweep_error_traces(name: &str, source: &str) {
    let source = source.to_string();
    let name = name.to_string();
    with_stack(STACK, move || {
        let (program, limits) = lowered(&source, STACK);
        // Out of the traces (its own values would be in the first).
        stitchwort_rt::native_abi::probe_layout().expect("the layout is as expected");
        for (what, at) in [
            (
                "steps",
                &(|k: u64| with_steps(limits, k)) as &dyn Fn(u64) -> Limits,
            ),
            ("frames", &|k: u64| with_frames(limits, k)),
        ] {
            let mut k = 0;
            loop {
                same_trace_under(&program, at(k), &format!("{name}, {what} limit {k}"));
                if on_machine(&program, at(k)).1.is_ok() {
                    break;
                }
                k += 1;
            }
            assert!(k > 2, "{name}, {what}: {k}");
        }
    });
}

/// The error exits of N2a's sweep program (values live across direct
/// calls, `Apply`, a constant's first computation and tail calls).
#[test]
fn error_exits_make_the_machines_allocation_trace() {
    sweep_error_traces("exits", EXITS);
}

/// The same for tail calls of each shape that holds values.
#[test]
fn tail_call_error_exits_make_the_machines_allocation_trace() {
    for (name, template) in tail_shapes() {
        if [
            "next to runtime helpers",
            "from a frame with live registers to free",
            "through a function value picked at each step",
        ]
        .iter()
        .any(|n| name.starts_with(n))
        {
            sweep_error_traces(name, &template.replace("{N}", "6"));
        }
    }
}
