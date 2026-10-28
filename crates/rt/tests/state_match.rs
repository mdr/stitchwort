//! State-passing handlers whose clauses resume inside a `match` run as a
//! loop (`stitchwort_rt::fusion`): every operation is a jump, and the most
//! bytes live at once during a run don't grow with the number of
//! operations. Each handler counts in its state; the program performs `n`
//! operations and keeps nothing else, so a run's memory is a constant.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicIsize, Ordering};

use stitchwort_core::DefId;
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_rt::value::Value;
use stitchwort_rt::{Limits, Machine, lower_global};

/// Counts the bytes live as it passes every request to the system
/// allocator. `unsafe` because `GlobalAlloc` is an unsafe trait and counting
/// allocations needs a global allocator; sound because each call is passed
/// unchanged to `System`, which upholds the trait's contract.
struct Counting;

static LIVE: AtomicIsize = AtomicIsize::new(0);
static PEAK: AtomicIsize = AtomicIsize::new(0);

#[allow(unsafe_code)]
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let live =
            LIVE.fetch_add(layout.size() as isize, Ordering::Relaxed) + layout.size() as isize;
        PEAK.fetch_max(live, Ordering::Relaxed);
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        LIVE.fetch_sub(layout.size() as isize, Ordering::Relaxed);
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

const STACK: usize = 256 * 1024 * 1024;

const PROGRAM: &str = "import Std (Nat, Option)

-- `next` resumes inside a `match`; `skip` resumes directly, which alone
-- makes the handler's fold a loop.
ability Count where
  next: () → {Count} Nat
  skip: () → {Count} ()

-- Matches on the state itself.
def Count.byState (prog: () → {Count} a): Nat → a :=
  handle prog() with
    | return x => s => x
    | Count.next u, k => s =>
      match s with
        | 0 => k 0 1
        | Succ m => k (m + 1) (m + 2)
    | Count.skip u, k => s => k () s

-- Matches on a pair a helper gives.
def Count.step (s: Nat): (Nat, Nat) := (s, s + 1)

def Count.byPair (prog: () → {Count} a): Nat → a :=
  handle prog() with
    | return x => s => x
    | Count.next u, k => s =>
      match Count.step s with
        | (value, after) => k value after
    | Count.skip u, k => s => k () s

-- Two `match`es, one inside the other, and an `if` in an arm.
def Count.nested (prog: () → {Count} a): Nat → a :=
  handle prog() with
    | return x => s => x
    | Count.next u, k => s =>
      match Count.step s with
        | (value, after) =>
          match Some value with
            | Some v => if v == 7 then k 7 after else k v after
            | None => k 0 after
    | Count.skip u, k => s => k () s

-- Written for an open row, used at the empty row.
def Count.open (start: Nat) (prog: () → {Count | e} a): {e} a :=
  let run: Nat → {e} a :=
    handle prog() with
      | return x => s => x
      | Count.next u, k => s =>
        match s with
          | 0 => k 0 1
          | Succ m => k (m + 1) (m + 2)
      | Count.skip u, k => s => k () s
  run start

def total (sum: Nat): Nat → {Count} Nat
  | 0 => sum
  | Succ more =>
    Count.skip()
    total (sum + Count.next()) more

export def byState (n: Nat): Nat := Count.byState (() => total 0 n) 0
export def byPair (n: Nat): Nat := Count.byPair (() => total 0 n) 0
export def nested (n: Nat): Nat := Count.nested (() => total 0 n) 0
export def opened (n: Nat): Nat := Count.open 0 (() => total 0 n)
";

fn def_named(session: &Session, name: &str) -> DefId {
    let g = &session.elab.globals;
    (0..g.defs.len())
        .map(DefId)
        .rfind(|id| &*g.def(*id).name == name)
        .unwrap_or_else(|| panic!("no definition `{name}`"))
}

/// Each export performs `n` of each operation: each is a jump of its
/// handler's loop, the sum is `0 + 1 + … + (n - 1)`, and the bytes live at once
/// during a run of 100,000 operations are about those of a run of 1,000.
#[test]
fn resuming_inside_a_match_runs_as_a_loop() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load("state-match.sw", PROGRAM)
            .unwrap_or_else(|e| panic!("state-match.sw doesn't check: {e:?}"));
        let g = &session.elab.globals;
        let limits = Limits::from_core(session.elab.limits);
        for name in ["byState", "byPair", "nested", "opened"] {
            let program = lower_global(g, session.elab.limits, def_named(&session, name))
                .unwrap_or_else(|e| panic!("lowering {name}: {e:?}"));
            let mut peaks = Vec::new();
            for n in [1_000u64, 100_000] {
                let mut m = Machine::new(&program, limits);
                let f = m.entry().expect("the export's value");
                m.reset_effect_counts();
                let base = LIVE.load(Ordering::Relaxed);
                PEAK.store(base, Ordering::Relaxed);
                let result = m.call(f, vec![Value::Nat(n)]);
                peaks.push(PEAK.load(Ordering::Relaxed) - base);
                let counts = m.effect_counts();
                let value = result.unwrap_or_else(|e| panic!("{name} at {n}: {e}"));
                assert!(
                    matches!(value, Value::Nat(sum) if sum == n * (n - 1) / 2),
                    "{name} at {n}: {value:?}"
                );
                assert_eq!(counts.jumps, 2 * n, "{name} at {n}: {counts:?}");
            }
            assert!(
                peaks[1] < peaks[0] + 64 * 1024,
                "{name}: {} bytes live at 1,000 operations, {} at 100,000",
                peaks[0],
                peaks[1]
            );
        }
    });
}
