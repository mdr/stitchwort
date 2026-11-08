//! Reuse across calls (crates/rt/src/reuse.rs): a cell taken apart in one
//! function and rebuilt in place by a copy of another that is given it. For
//! each program, native code prints what the machine prints, makes the same
//! allocation trace and frees every cell (`same_trace`), and the cells are
//! counted: how many `Bin` nodes of a `Map` are new, and how many reused.

use crate::common::*;
use stitchwort_driver::driver::with_stack;
use stitchwort_rt::alloc_trace;
use stitchwort_rt::ir::Reuse;
use stitchwort_rt::{Limits, Program};

/// Inserts in increasing, decreasing and scattered order, which between
/// them rebalance with every rotation, then pops every entry.
const MAP_PATHS: &str = r#"import Std (IO, List, Map, Nat, Option)

def build (keys: List Nat): Map Nat Nat :=
  List.foldLeft keys Map.empty (m i => Map.insert m i i)

def drain: Nat → Map Nat Nat → Nat
  | Zero, m => Map.size m
  | Succ fuel, m => match Map.popMin m with
    | None => 0
    | Some found => found.fst.snd + drain fuel found.snd

def run (keys: List Nat): Nat := drain (keys.length + 1) (build keys)

def main(): {IO} () :=
  let up := List.range 0 300
  let scattered := up.map (i => (i * 7919) % 1009)
  IO.print "${run up} ${run (List.reverse up)} ${run scattered}"
"#;

/// The new and reused cells of `arity` fields in a machine run of
/// `program`, and what it printed.
fn cells(program: &Program, limits: Limits, arity: usize) -> (String, usize, usize) {
    alloc_trace::start();
    let ran = on_machine(program, limits);
    let trace = alloc_trace::finish();
    assert_eq!(ran.1, Ok(()));
    let count = |kind: &str| {
        trace
            .events
            .iter()
            .filter(|e| e.arity == arity && e.to_string().starts_with(kind))
            .count()
    };
    (ran.0, count("alloc "), count("reuse "))
}

/// `program` with its copies taking reuse tokens left unused: the bytecode
/// is as it was before reuse across calls.
fn without_copies(mut program: Program) -> Program {
    for global in &mut program.globals {
        if let Reuse::Copies(_) = global.reuse {
            global.reuse = Reuse::None;
        }
    }
    program
}

fn copy_named(program: &Program, name: &str) -> bool {
    program
        .globals
        .iter()
        .any(|g| &*g.name == name && matches!(g.reuse, Reuse::Copy { .. }))
}

/// Every insert builds one new node, its leaf, and rebuilds the rest of its
/// path in the cells it took apart, through `balance`, `rebuild` and the
/// rotations; every pop builds none. Without the copies, every node on the
/// path is new.
#[test]
fn map_paths_reuse_their_nodes() {
    with_stack(STACK, || {
        let (program, limits) = lowered(MAP_PATHS);
        for name in [
            "Std.Map.Tree.minView[reuse]",
            "Std.Map.Tree.rebuild[reuse]",
            "Std.Map.Tree.singleL[reuse]",
            "Std.Map.Tree.doubleL[reuse]",
            "Std.Map.Tree.singleR[reuse]",
            "Std.Map.Tree.doubleR[reuse]",
        ] {
            assert!(copy_named(&program, name), "no {name}");
        }
        let (out, fresh, reused) = cells(&program, limits, 5);
        let expected = "44850 44850 151509\n";
        assert_eq!(out, expected);
        // 900 inserts, each of a new key, and 900 pops: at most one new
        // node each (an insert's leaf; a pop's root, when the map's root
        // is still held).
        assert!(fresh <= 1_800, "{fresh} new, {reused} reused");
        let (out, fresh_before, reused_before) = cells(&without_copies(program), limits, 5);
        assert_eq!(out, expected);
        assert!(fresh_before > 10_000, "{fresh_before}");
        assert!(
            reused > 10 * reused_before,
            "{reused} against {reused_before}"
        );
        assert_eq!(fresh + reused, fresh_before + reused_before);
    });
    same_trace(MAP_PATHS);
}

/// A map used again after an insert: the insert finds every node on its
/// path shared, so it copies the path and changes no cell of the old map,
/// which still reads as before.
#[test]
fn a_shared_map_is_left_alone() {
    let source = r#"import Std (IO, List, Map, Nat, Option)

def build (keys: List Nat): Map Nat Nat :=
  List.foldLeft keys Map.empty (m i => Map.insert m i (i * 2))

def total (m: Map Nat Nat): Nat := Map.foldLeft m 0 (acc k v => acc + k + v)

def both (m: Map Nat Nat) (k: Nat): Nat :=
  let pair := (m, Map.insert m k 1000)
  total pair.fst * 100000 + total pair.snd

def run: Nat → Map Nat Nat → Nat → Nat
  | Zero, m, acc => acc
  | Succ n, m, acc => run n m (acc + both m (n * 3))

def main(): {IO} () :=
  let m := build (List.range 0 50)
  IO.print "${run 40 m 0} ${total m}"
"#;
    with_stack(STACK, || {
        let (program, limits) = lowered(source);
        let (out, _, _) = cells(&program, limits, 5);
        let (before, _, _) = cells(&without_copies(program), limits, 5);
        assert_eq!(out, before);
        assert_eq!(out, "14700188116 3675\n");
    });
    same_trace(source);
}

/// Tokens held across a call of a closure (`insertWith`'s `f`, on keys
/// already there), and across recursion (`minView`).
#[test]
fn tokens_held_across_closures_and_recursion() {
    let source = r#"import Std (IO, List, Map, Nat, Option)

def count (keys: List Nat): Map Nat Nat :=
  List.foldLeft keys Map.empty (m i => Map.insertWith m (i % 37) 1 (new old => new + old * 2))

def drain: Nat → Map Nat Nat → Nat
  | Zero, m => 0
  | Succ fuel, m => match Map.popMin m with
    | None => 0
    | Some found => found.fst.fst + found.fst.snd + drain fuel found.snd

def main(): {IO} () :=
  IO.print "${drain 100 (count (List.range 0 400))}"
"#;
    with_stack(STACK, || {
        let (program, limits) = lowered(source);
        let (out, fresh, reused) = cells(&program, limits, 5);
        let (before, fb, rb) = cells(&without_copies(program), limits, 5);
        assert!(fb > 10 * fresh, "{fb} new before");
        let _ = rb;
        assert_eq!(out, before);
        // At most one new node per new key (37) and per pop (37): every
        // other insert, and every node on a path, reuses its cell.
        assert!(fresh <= 74, "{fresh} new, {reused} reused");
        assert!(reused > 1_500, "{reused}");
    });
    same_trace(source);
}

/// A copy reached by a tail call, and a copy calling itself in tail
/// position (a jump in native code), with the token passed round the loop
/// until the constructor at its end fills it.
#[test]
fn tokens_go_round_tail_calls() {
    let source = r#"import Std (IO, Nat)

type Box =
  | MkBox (a: Nat) (b: Nat)

def fill: Nat → Nat → Box
  | Zero, x => MkBox (x % 1000) (x % 7)
  | Succ n, x => fill n (x + 1)

def step (b: Box): Box :=
  match b with
    | MkBox x y => fill 3 (x + y)

def run: Nat → Box → Nat
  | Zero, b => (match b with | MkBox x y => x * 1000 + y)
  | Succ n, b => run n (step b)

def main(): {IO} () :=
  IO.print "${run 50 (MkBox 1 2)}"
"#;
    with_stack(STACK, || {
        let (program, limits) = lowered(source);
        assert!(copy_named(&program, "Main.fill[reuse]"));
        let (out, fresh, reused) = cells(&program, limits, 2);
        let (before, fresh_before, rb) = cells(&without_copies(program), limits, 2);
        assert_eq!(rb, 0);
        assert_eq!(out, before);
        // The constant box is shared, so the first step builds a new one;
        // every later step rebuilds its box in place.
        assert_eq!((fresh, reused), (2, 50));
        assert_eq!(fresh_before, 52);
    });
    same_trace(source);
}

/// A constructor whose field is a call that could take the token gets it
/// first (`Node (s + 1) (insert key l) kk r`): the A/B pair of
/// docs/research/in-place-reuse.md §2.2, with the node built in the arm
/// (A, 80.6% reused before) and in a recursive helper (B, 6.9%).
#[test]
fn constructors_take_the_token_before_their_fields() {
    let pair = |node: &str| {
        format!(
            r#"import Std (IO, List, Nat)

type Tree =
  | Leaf
  | Node (size: Nat) (left: Tree) (key: Nat) (right: Tree)

def size: Tree → Nat
  | Leaf => 0
  | Node s _ _ _ => s

def mk: Nat → Tree → Nat → Tree → Tree
  | Zero, l, k, r => Node (size l + size r + 1) l k r
  | Succ n, l, k, r => mk n l k r

def ins (key: Nat): Tree → Tree
  | Leaf => Node 1 Leaf key Leaf
  | Node s l kk r =>
    if key < kk then {node_l}
    else if kk < key then {node_r}
    else Node s l kk r

def main(): {{IO}} () :=
  let keys := (List.range 0 1000).map (i => (i * 7919) % 1009)
  IO.print "${{size (List.foldLeft keys Leaf (t k => ins k t))}}"
"#,
            node_l = node.replace("SIDE", "(ins key l) kk r"),
            node_r = node.replace("SIDE", "l kk (ins key r)"),
        )
    };
    let a = pair("Node (s + 1) SIDE");
    let b = pair("mk 0 SIDE");
    for (source, at_least) in [(a, 0.806), (b, 0.806)] {
        with_stack(STACK, {
            let source = source.clone();
            move || {
                let (program, limits) = lowered(&source);
                alloc_trace::start();
                let ran = on_machine(&program, limits);
                let trace = alloc_trace::finish();
                assert_eq!(ran, ("1000\n".to_string(), Ok(())));
                let (fresh, reused) = (trace.count("alloc"), trace.count("reuse"));
                let share = reused as f64 / (fresh + reused) as f64;
                assert!(share >= at_least, "{share:.3} reused ({fresh} new)");
            }
        });
        same_trace(&source);
    }
}

/// A run stopped by the step or frame limit at every point of a chain of
/// copies passing tokens frees every cell, natively, and stops where the
/// machine does.
#[test]
fn early_exits_mid_chain_free_every_cell() {
    let source = r#"import Std (IO, List, Map, Nat, Option)

def build (keys: List Nat): Map Nat Nat :=
  List.foldLeft keys Map.empty (m i => Map.insert m i i)

def drain: Nat → Map Nat Nat → Nat
  | Zero, m => 0
  | Succ fuel, m => match Map.popMin m with
    | None => 0
    | Some found => found.fst.snd + drain fuel found.snd

def main(): {IO} () :=
  IO.print "${drain 20 (build (List.range 0 12))}"
"#;
    with_stack(STACK, move || {
        let (program, limits) = lowered(source);
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
                    assert_eq!(expected.0, "66\n");
                    return k;
                }
                k += 1;
            }
        };
        let steps = sweep(&|n| Limits { steps: n, ..limits });
        let frames = sweep(&|n| Limits {
            frames: n as usize,
            ..limits
        });
        assert!(steps > 100, "{steps}");
        assert!(frames > 5, "{frames}");
    });
}

/// The depth note counts a copy's frames as its original's: a recursion
/// that enters `deep` once and then its copy `deep[reuse]` is one entry,
/// named `Main.deep`, with all its frames.
#[test]
fn the_depth_note_counts_copies_as_their_original() {
    let source = r#"import Std (IO, Nat)

type Box =
  | MkBox (a: Nat) (b: Nat)

def deep: Nat → Box
  | Zero => MkBox 0 0
  | Succ n => match deep n with
    | MkBox a b => MkBox (a + 1) b

def start (b: Box): Box :=
  match b with
    | MkBox x y => deep (x + y + 100000)

def main(): {IO} () :=
  match start (MkBox 1 2) with
    | MkBox a b => IO.print "${a}"
"#;
    with_stack(STACK, move || {
        let (program, limits) = lowered(source);
        assert!(copy_named(&program, "Main.deep[reuse]"));
        let limits = Limits {
            frames: 5_000,
            ..limits
        };
        let mut output = Vec::new();
        let error = stitchwort_rt::run_main(&program, limits, &mut "".as_bytes(), &mut output)
            .expect_err("runs out of frames");
        let text = format!("{error} {error:?}");
        assert!(text.contains("`Main.deep` ("), "{text}");
        assert!(!text.contains("[reuse]"), "{text}");
        let (ran, _) = native(&program, limits, false);
        assert_eq!(ran.1, Err("out of frames".to_string()));
    });
}

/// `List.map`'s loop (a TRMC twin) is left alone: no copy of a twin, a
/// twin's helpers or its wrapper.
#[test]
fn loops_get_no_copies() {
    with_stack(STACK, || {
        let (program, _) = lowered(MAP_PATHS);
        for global in &program.globals {
            if global.name.contains("[cells") || global.name.starts_with("Std.List.map") {
                assert_eq!(global.reuse, Reuse::None, "{}", global.name);
            }
        }
    });
}
