//! The run's cell cache (`stitchwort_rt::cell_cache`) leaves nothing
//! behind: a native run that caches cells and then ends, normally, out of
//! steps, out of frames or by a failure, frees every byte it allocated.
//! Its own binary, for the counting allocator.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicIsize, Ordering};

use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_native::n1::{Options, compile, stack_for};
use stitchwort_rt::host::{NoTerminal, RunError};
use stitchwort_rt::{Limits, Program, cell_cache, lower_main, run_main_native};

/// Counts the bytes live as it passes every request to the system
/// allocator. `unsafe` because `GlobalAlloc` is an unsafe trait; sound
/// because each call is passed unchanged to `System`.
struct Counting;

static LIVE: AtomicIsize = AtomicIsize::new(0);

#[allow(unsafe_code)]
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        LIVE.fetch_add(layout.size() as isize, Ordering::Relaxed);
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        LIVE.fetch_sub(layout.size() as isize, Ordering::Relaxed);
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

const STACK: usize = 1024 * 1024 * 1024;

/// Builds and walks 200 trees of 511 nodes, so the cache fills and is
/// drawn on, then ends as `ending` says.
fn source(ending: &str) -> String {
    format!(
        "import Std (Fail, IO, Nat)

type Tree = | Leaf | Node (left: Tree) (right: Tree)

def Tree.make: Nat → Tree
  | Zero => Node Leaf Leaf
  | Succ depth => Node (Tree.make depth) (Tree.make depth)

def Tree.check: Tree → Nat
  | Leaf => 0
  | Node left right => 1 + left.check + right.check

def checks: Nat → Nat → Nat → Nat
  | Zero, depth, total => total
  | Succ rest, depth, total => checks rest depth (total + (Tree.make depth).check)

def count: Nat → Nat
  | Zero => 0
  | Succ n => 1 + count n

def main(): {{IO, Fail}} () :=
  IO.print \"${{checks 200 8 0}}\"
  {ending}
"
    )
}

fn lowered(source: &str) -> (Program, Limits) {
    let mut session = Session::for_stack(STACK);
    session.use_test_std_cache();
    session
        .load("test.sw", source)
        .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
    let main = session.main().expect("`main` has the right type");
    let program = lower_main(
        &session.elab.ev(),
        session.elab.options.limits,
        main.term(),
        main.row,
    )
    .expect("lowers");
    (program, Limits::from_core(session.elab.options.limits))
}

/// Compiles and runs `program` natively; how it ended.
fn run(program: &Program, limits: Limits) -> Result<(), String> {
    let options = Options {
        trace_refcounts: false,
        count_bodies: false,
        pc_map: false,
    };
    let image = stitchwort_rt::code::compile(program);
    let islands = compile(program, image, options).expect("compiles");
    let stack =
        stack_for(limits.frames as u64, islands.max_frame, &islands.widest).expect("a stack size");
    let mut output = Vec::new();
    run_main_native(
        Box::new(islands),
        limits,
        stack.min(STACK),
        &mut "".as_bytes(),
        &mut output,
        &mut NoTerminal,
    )
    .map_err(|e: RunError| e.to_string())
}

#[test]
fn a_run_frees_its_cached_cells_however_it_ends() {
    with_stack(STACK, || {
        let done = lowered(&source("IO.print \"done\""));
        let failed = lowered(&source("Fail.fail \"stop\""));
        let deep = lowered(&source("IO.print \"${count 100000}\""));
        let cases = [
            ("ended", &done.0, done.1, true),
            (
                "out of steps",
                &done.0,
                Limits {
                    steps: 150_000,
                    ..done.1
                },
                false,
            ),
            (
                "out of frames",
                &deep.0,
                Limits {
                    frames: 1_000,
                    ..deep.1
                },
                false,
            ),
            ("failed", &failed.0, failed.1, false),
        ];
        // Once first, for whatever is allocated on first use and kept.
        for &(_, program, limits, _) in &cases {
            let _ = run(program, limits);
        }
        for (what, program, limits, ok) in cases {
            let drained = cell_cache::drained();
            let before = LIVE.load(Ordering::Relaxed);
            let result = run(program, limits);
            assert_eq!(result.is_ok(), ok, "{what}: {result:?}");
            drop(result);
            let after = LIVE.load(Ordering::Relaxed);
            assert_eq!(after, before, "{what}: bytes left behind");
            if cell_cache::ENABLED {
                assert!(
                    cell_cache::drained() > drained,
                    "{what}: the run cached no cells"
                );
            }
        }
    });
}
