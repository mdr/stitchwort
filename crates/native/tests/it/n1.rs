//! Stage N1 of docs/proposals/native-compilation.md: `run --native` against
//! the machine. For the three benchmarks at small sizes and a few small
//! programs in the subset, native code must print what the machine prints,
//! make the same allocation trace event for event, and run out of frames
//! and steps at exactly the machine's points (D1253).

use crate::common::*;
use stitchwort_driver::driver::with_stack;
use stitchwort_native::n1::{Options, compile, stack_for};
use stitchwort_rt::host::NoTerminal;
use stitchwort_rt::{Limits, alloc_trace, run_main_native};

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

/// `Text.fold` inside a recursive function: compiled (stage NO1 of
/// native-only.md; from N4 to NO1 the machine ran it, calling the compiled
/// lambda back). (Before N4, the whole run stayed on the machine.)
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

/// The cell-by-cell loops behind `map`, `filter`, `append` and `concat`
/// build their result with the hole operations (`New`, `Fill`, `Take`),
/// which native code does as a store and a load. The elements are shared
/// (the same lists and texts are used again after the loops, and appear
/// several times in the results), so every `Fill` takes a count on a value
/// others hold, and every `Take` a count on the chain: the traces equal the
/// machine's, and nothing leaks.
#[test]
fn list_loops_building_cells_agree_and_free_everything() {
    let source = r#"import Std (IO, List, Text)

def nothing: List Nat := []

def main(): {IO} () :=
  let words := ["ab", "cd", "ef"]
  let rows := [words, [], words]
  let longer := words.map (w => "${w}!")
  let both := words ++ longer ++ words
  let flat := rows.concat
  let kept := both.filter (w => w != "cd!")
  IO.print "${longer} ${both.length} ${flat.length} ${kept.length}"
  IO.print "${words} ${rows.length} ${List.map nothing (n => n + 1)}"
"#;
    let out = agrees(source);
    assert!(
        out.starts_with("[\"ab!\", \"cd!\", \"ef!\"] 9 6 8\n"),
        "{out}"
    );
    assert!(out.contains("[\"ab\", \"cd\", \"ef\"] 3 []"), "{out}");
    same_trace(source);
}

/// Functions that add to a call of themselves, run as loops carrying the
/// sum (`stitchwort_rt::sums`), on `Nat` past a machine word and on `Int`:
/// native code prints what the machine prints, stops where it does at
/// every limit, and needs the same frames however long the list.
#[test]
fn calls_plus_a_number_agree_and_use_constant_frames() {
    let source = |n: u32| {
        format!(
            r#"import Std (IO, Int, List, Nat)

def size: List Nat → Nat
  | [] => 0
  | Cons x rest => Succ (size rest)

def total: List Nat → Nat
  | [] => 18446744073709551610
  | Cons x rest => x + total rest

def signed: List Nat → Int
  | [] => -7
  | Cons x rest => signed rest + (Nat.toInt x - 3)

def main(): {{IO}} () :=
  let xs := List.range 0 {n}
  IO.print "${{size xs}} ${{total xs}} ${{signed xs}}"
"#
        )
    };
    assert_eq!(agrees(&source(10)), "10 18446744073709551655 8\n");
    with_stack(STACK, move || {
        let (short, limits) = lowered(&source(5));
        let (long, _) = lowered(&source(10));
        let (short_steps, short_frames) = every_limit_agrees(&short, limits);
        let (long_steps, long_frames) = every_limit_agrees(&long, limits);
        assert_eq!(short_frames, long_frames);
        assert!(long_steps > short_steps, "{short_steps} {long_steps}");
    });
}

/// Comparisons made as values (not branched on) and the array operations
/// `getOr` and `set`, which native code does inline for small numbers and
/// an array nothing else holds, and by the generic call otherwise: a number
/// beyond a word, an index past the end, an array that another name still
/// holds (which `set` must copy, leaving the other alone). The elements are
/// texts, so the old element dropped by an in-place `set` and the copy taken
/// by `getOr` show in the allocation trace, which equals the machine's.
#[test]
fn comparisons_and_array_access_agree_on_small_big_and_shared() {
    let source = r#"import Std (Array, IO, List, Nat, Text)

def flag (b: Bool): Nat := if b then 1 else 0

def compare (a: Nat) (b: Nat): Text := "${flag (a ≤ b)}${flag (a == b)}${flag (b ≤ a)}"

def fill (a: Array Text) (n: Nat): Array Text :=
  match n with
    | Zero => a
    | Succ m => fill (a.set m "x${n}") m

def main(): {IO} () :=
  let huge := 1180591620717411303424
  IO.print "${compare 3 5} ${compare 5 5} ${compare 5 3} ${compare 0 0}"
  IO.print "${compare huge huge} ${compare 5 huge} ${compare huge 5} ${compare (huge + 1) huge}"
  let base := Array.replicate (count := 4) "a"
  let filled := fill base 4
  IO.print "${filled.toList} ${base.toList}"
  IO.print "${filled.getOr 0 "none"} ${filled.getOr 3 "none"} ${filled.getOr 4 "none"} ${filled.getOr huge "none"}"
  let shared := base.set 1 "b"
  let again := base.set 2 "c"
  IO.print "${shared.toList} ${again.toList} ${base.toList}"
  IO.print "${(base.set 9 "z").toList} ${(base.set huge "z").toList} ${(base.set 0 "q").getOr 0 "none"}"
"#;
    let out = agrees(source);
    assert_eq!(
        out,
        "100 111 001 111\n111 100 001 001\n\
         [\"x1\", \"x2\", \"x3\", \"x4\"] [\"a\", \"a\", \"a\", \"a\"]\n\
         x1 x4 none none\n\
         [\"a\", \"b\", \"a\", \"a\"] [\"a\", \"a\", \"c\", \"a\"] [\"a\", \"a\", \"a\", \"a\"]\n\
         [\"a\", \"a\", \"a\", \"a\"] [\"a\", \"a\", \"a\", \"a\"] q\n"
    );
    same_trace(source);
}

/// Cells of every size native code builds and frees: a one-field box,
/// pairs and trees nested in each other, an eight-field cell (the largest
/// `sw_cell_new` and `sw_cell_free` build and free with a fixed layout) and
/// a nine-field one (the first past it), with fields shared between cells
/// and with names still in use. Every cell matched apart is unique when
/// `sum` and `spread` take its fields, so it's freed emptied; the shared
/// ones are dropped by a count. The output and the allocation trace equal
/// the machine's, and nothing leaks.
#[test]
fn cells_of_every_size_agree_and_free_everything() {
    let source = r#"import Std (IO, List, Nat, Text)

type Box = | Boxed (value: Nat)
type Tree = | Leaf | Node (left: Tree) (label: Text) (right: Tree)
type Eight = | Octet (a: Nat) (b: Text) (c: Nat) (d: Tree) (e: Nat) (f: Text) (g: Nat) (h: Box)
type Nine = | Nonet (a: Nat) (b: Nat) (c: Nat) (d: Nat) (e: Nat) (f: Nat) (g: Nat) (h: Nat) (i: Text)

def Tree.size: Tree → Nat
  | Leaf => 0
  | Node left _ right => 1 + left.size + right.size

def Tree.build: Nat → Text → Tree
  | Zero, _ => Leaf
  | Succ n, t => Node (Tree.build n t) "${t}${n}" (Tree.build n t)

def Box.open: Box → Nat
  | Boxed v => v

def eight (n: Nat) (t: Text) (tree: Tree): Eight := Octet n t (n + 1) tree (n + 2) t (n + 3) (Boxed n)

def Eight.sum: Eight → Nat
  | Octet a b c d e f g h => a + b.length + c + d.size + e + f.length + g + h.open

def nine (n: Nat) (t: Text): Nine := Nonet n (n + 1) (n + 2) (n + 3) (n + 4) (n + 5) (n + 6) (n + 7) t

def Nine.spread: Nine → Nat
  | Nonet a b c d e f g h i => a + b + c + d + e + f + g + h + i.length

def Nine.label: Nine → Text
  | Nonet _ _ _ _ _ _ _ _ i => i

def main(): {IO} () :=
  let label := "x"
  let shared := Tree.build 3 label
  let both := Node shared label shared
  let eights := List.map (List.range 0 5) (n => eight n label shared)
  let nines := List.map (List.range 0 5) (n => nine n label)
  IO.print "${shared.size} ${both.size} ${(Tree.build 4 "y").size} ${(Boxed 7).open}"
  IO.print "${List.map eights (e => e.sum)} ${List.map nines (n => n.spread)}"
  IO.print "${(nine 9 "kept").label} ${(eight 1 label Leaf).sum} ${(nine 2 label).spread} ${label}"
"#;
    let out = agrees(source);
    assert_eq!(
        out,
        "7 15 15 7\n[15, 20, 25, 30, 35] [29, 37, 45, 53, 61]\nkept 13 45 x\n"
    );
    same_trace(source);
}

/// The instructions the machine executed in a native run of `program`
/// (`machine::instructions_executed`: none since stage NO4 of
/// native-only.md), and how it ended.
fn machine_instructions(program: &stitchwort_rt::Program, limits: Limits) -> (Ran, u64) {
    let before = stitchwort_rt::machine::instructions_executed();
    let (ran, notes) = native(program, limits, false);
    assert!(ran_natively(&notes), "{notes:#?}");
    (
        ran,
        stitchwort_rt::machine::instructions_executed() - before,
    )
}

/// A recursion through `Text.fold` (stage NO1 of native-only.md): each
/// level's function is a closure called from the compiled `Text.fold`, on a
/// character that isn't ASCII (a new cell each time). It runs out of frames
/// (and of steps) exactly where the machine does, with the same output and
/// freeing every cell at every limit, and never has the machine run
/// anything for it.
#[test]
fn a_recursion_through_text_fold_stops_where_the_machine_does() {
    let source = r#"import Std (IO, Text)

def depth: Nat → Nat
  | Zero => 0
  | Succ n => Text.fold "é" 1 (c acc => acc + depth n)

def main(): {IO} () :=
  IO.print "${depth 20}"
"#;
    assert_eq!(agrees(source), "20\n");
    same_trace(source);
    with_stack(STACK, move || {
        let (program, limits) = lowered(source);
        let (least_steps, least_frames) = every_limit_agrees(&program, limits);
        assert!(least_frames > 40, "{least_frames}");
        assert!(least_steps > 40, "{least_steps}");
        let (ran, executed) = machine_instructions(&program, limits);
        assert_eq!(ran.1, Ok(()));
        assert_eq!(executed, 0);
        // The counter counts the machine's runs, so 0 means none.
        let before = stitchwort_rt::machine::instructions_executed();
        let _ = on_machine(&program, limits);
        assert!(stitchwort_rt::machine::instructions_executed() > before);
        // One frame short: out of frames on both, with no machine instructions.
        let short = Limits {
            frames: least_frames as usize - 1,
            ..limits
        };
        let (ran, executed) = machine_instructions(&program, short);
        assert_eq!(ran, on_machine(&program, short));
        assert_eq!(ran.1, Err("out of frames".to_string()));
        assert_eq!(executed, 0);
    });
}

/// `Text.fold` as a function value, applied through the apply stub
/// (`abi::FOLD_CODE`), and with a partial application as its function (its
/// calls through `apply2`): compiled, with the machine's output, trace and
/// limits, and no machine instructions.
#[test]
fn text_fold_as_a_function_value_runs_natively() {
    let source = r#"import Std (IO, List, Text)

def step (k: Nat) (c: Char) (acc: Nat): Nat := acc * k + 1

def withFold (fold: Text → Nat → (Char → Nat → Nat) → Nat) (t: Text): Nat :=
  fold t 0 (step 2) + fold t 1 (c acc => acc + 3)

def main(): {IO} () :=
  IO.print "${withFold Text.fold "añb" + List.length (List.map [step 3, step 4] (Text.fold "xy" 0))}"
"#;
    let printed = agrees(source);
    assert_eq!(printed, format!("{}\n", 7 + 10 + 2));
    same_trace(source);
    with_stack(STACK, move || {
        let (program, limits) = lowered(source);
        every_limit_agrees(&program, limits);
        let (ran, executed) = machine_instructions(&program, limits);
        assert_eq!(ran.1, Ok(()));
        assert_eq!(executed, 0);
    });
}

/// `run 3000` builds a list 3,000 deep and finds its largest element twice
/// (by non-tail recursion: a sum would be a loop, `stitchwort_rt::sums`),
/// keeping it while the first search recurses. The smallest frame limit, and the smallest step
/// limit, under which it finishes are found for each runner by bisection:
/// they must be the same, one below must be `E-RESOURCE` on both, and
/// running out mid-recursion must free every cell.
#[test]
fn resources_run_out_at_the_machines_points() {
    let source = r#"import Std (IO, List, Nat)

def build: Nat → List Nat
  | Zero => []
  | Succ n => Cons n (build n)

def largest: List Nat → Nat
  | [] => 0
  | Cons x rest => Nat.max x (largest rest)

def run (n: Nat): Nat :=
  let xs := build n
  largest xs + largest xs

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
    let source = r#"import Std (IO, List, Nat)

def big: Nat := 18446744073709551616 + 5

def largest: List Nat → Nat
  | [] => 0
  | Cons x rest => Nat.max x (largest rest)

def inc (m: Nat): Nat := m + 1

def twice (f: Nat → Nat) (x: Nat): Nat := f (f x)

def count: Nat → Nat → Nat
  | Zero, acc => acc
  | Succ n, acc => count n (acc + 1)

def keep: Nat → List Nat → Nat
  | Zero, xs => largest xs
  | Succ n, xs =>
    let ys := [n, n + big]
    let a := keep n ys
    let b := twice inc a
    a + b + largest xs + largest ys + count n 0

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

/// The compiled code owns the image its tables point into (SW-1124): with
/// the program and every other handle on the image gone, and the freed
/// memory reused, code that reads the constant pool (the big numbers, the
/// texts) and the number tables (`shrink`'s cases) still runs as the
/// machine does.
#[test]
fn the_code_keeps_its_image() {
    with_stack(STACK, || {
        let (program, limits) = lowered(BIG_NUMBERS);
        let expected = on_machine(&program, limits);
        let islands = {
            let image = stitchwort_rt::code::compile(&program);
            compile(&program, image, Options::default()).expect("compiles")
        };
        drop(program);
        let churn: Vec<Vec<u64>> = (0..2000).map(|n| vec![u64::MAX; n % 64]).collect();
        let stack = stack_for(limits.frames as u64, islands.max_frame, &islands.widest)
            .expect("fits the cap");
        let mut output = Vec::new();
        let result = run_main_native(
            Box::new(islands),
            limits,
            stack.min(STACK),
            &mut "".as_bytes(),
            &mut output,
            &mut NoTerminal,
        );
        drop(churn);
        assert_eq!(ended(output, result), expected);
    });
}

/// `count(n)` enters `down` n + 1 times (a self tail call each time), and
/// `count` once.
const COUNTED: &str = r#"import Std (IO)

def down: Nat → Nat → Nat
  | Zero, acc => acc
  | Succ n, acc => down n (acc + 2)

def count (n: Nat): Nat := down n 0

def main(): {IO} () :=
  IO.print "${count 1000}"
"#;

#[test]
fn bodies_count_their_entries_when_asked() {
    use stitchwort_rt::call_counts;
    with_stack(STACK, || {
        let (program, limits) = lowered(COUNTED);
        let counting = Options {
            trace_refcounts: false,
            count_bodies: true,
            pc_map: false,
        };
        // The name's address (a data symbol) and the count call are in the
        // code only when asked for.
        let image = stitchwort_rt::code::compile(&program);
        let plain = stitchwort_native::n1::listing(&program, &image, Options::default())
            .unwrap_or_else(|e| panic!("{e:#?}"));
        let asked = stitchwort_native::n1::listing(&program, &image, counting)
            .unwrap_or_else(|e| panic!("{e:#?}"));
        assert!(!plain.contains("symbol_value"));
        assert!(asked.contains("symbol_value"));
        // By its full address: JIT code and data can be mapped too far
        // apart for a PC-relative reference (SW-3139).
        assert!(asked.contains("= symbol "));
        assert!(!asked.contains("symbol colocated"), "{asked}");

        let (ran, notes) = native_with(&program, limits, counting, STACK);
        assert!(ran_natively(&notes), "{notes:#?}");
        assert_eq!(ran, ("2000\n".to_string(), Ok(())));
        let report = call_counts::report();
        if call_counts::ENABLED {
            // `down`'s body is entered 1001 times, the self tail calls
            // included, and `count` (probably inlined into `main`) and
            // `main` at most once.
            let entries = |name: &str| {
                report.iter().find_map(|l| {
                    let (n, symbol) = l.trim_start().split_once("  ")?;
                    symbol
                        .starts_with(name)
                        .then(|| n.parse::<u64>().ok())
                        .flatten()
                })
            };
            assert_eq!(entries("Main.down#"), Some(1001), "{report:#?}");
        } else {
            assert!(report.is_empty());
        }
    });
}
