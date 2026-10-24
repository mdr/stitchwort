//! Allocation of the native effect runtime (docs/proposals/effect-runtime.md
//! §9.3, stage 4f): bytes and blocks allocated, and the most bytes live at
//! once, during one call of each export of `bench/effect-runtime`'s
//! `map.sw` and `shapes.sw` over 1,000,000 elements, against plain `map`.
//! The input list is built before counting starts and the result dropped
//! after it ends. A measurement, not a check, so it's ignored by default:
//!
//!   cargo test --release -p stitchwort-rt --test effect_alloc -- --ignored --nocapture

use std::alloc::{GlobalAlloc, Layout, System};
use std::path::Path;
use std::sync::atomic::{AtomicIsize, AtomicUsize, Ordering};
use std::time::Instant;

use stitchwort_core::DefId;
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_rt::value::Value;
use stitchwort_rt::{Limits, Machine, lower_global};

/// Counts bytes and blocks as it passes every request to the system
/// allocator. `unsafe` because `GlobalAlloc` is an unsafe trait and counting
/// allocations needs a global allocator; sound because each call is passed
/// unchanged to `System`, which upholds the trait's contract.
struct Counting;

static ALLOCATED: AtomicUsize = AtomicUsize::new(0);
static BLOCKS: AtomicUsize = AtomicUsize::new(0);
static LIVE: AtomicIsize = AtomicIsize::new(0);
static PEAK: AtomicIsize = AtomicIsize::new(0);

#[allow(unsafe_code)]
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCATED.fetch_add(layout.size(), Ordering::Relaxed);
        BLOCKS.fetch_add(1, Ordering::Relaxed);
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

fn load(name: &str) -> Session {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../bench/effect-runtime")
        .join(name);
    let text = std::fs::read_to_string(&path).expect("readable benchmark");
    let mut session = Session::for_stack(STACK);
    session
        .load(name, &text)
        .unwrap_or_else(|e| panic!("{name} doesn't check: {e:?}"));
    session
}

fn def_named(session: &Session, name: &str) -> DefId {
    let g = &session.elab.globals;
    (0..g.defs.len())
        .map(DefId)
        .rfind(|id| &*g.def(*id).name == name)
        .unwrap_or_else(|| panic!("no definition `{name}`"))
}

#[test]
#[ignore]
fn allocation_per_element() {
    with_stack(STACK, || {
        let n: u64 = std::env::var("STITCHWORT_ALLOC_N")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(1_000_000);
        for (file, names) in [
            (
                "map.sw",
                &["plain", "checked", "failsLast", "counted", "countedChecked"][..],
            ),
            (
                "shapes.sw",
                &[
                    "asked",
                    "askedChecked",
                    "askedIn",
                    "emittedIn",
                    "searchedIn",
                    "emitted",
                    "searched",
                ][..],
            ),
        ] {
            let session = load(file);
            let g = &session.elab.globals;
            for name in names {
                let program = lower_global(g, session.elab.limits, def_named(&session, name))
                    .unwrap_or_else(|e| panic!("lowering {name}: {e:?}"));
                let limits = Limits::from_core(session.elab.limits);
                let s = &program.shapes;
                let mut xs = Value::Tag(s.nil);
                for i in (0..n).rev() {
                    xs = Value::data(s.cons, [Value::Nat(i), xs]);
                }
                // Kept alive throughout, so that what the call frees of
                // its input doesn't hide what it allocates.
                let input = xs.clone();
                let args = if matches!(*name, "failsLast" | "countedChecked") {
                    vec![Value::Nat(n), xs]
                } else {
                    vec![xs]
                };
                let mut m = Machine::new(&program, limits);
                let f = m.entry().expect("the export's value");
                let base = LIVE.load(Ordering::Relaxed);
                PEAK.store(base, Ordering::Relaxed);
                let (a0, b0) = (
                    ALLOCATED.load(Ordering::Relaxed),
                    BLOCKS.load(Ordering::Relaxed),
                );
                let start = Instant::now();
                let result = m.call(f, args);
                let ms = start.elapsed().as_millis();
                let allocated = ALLOCATED.load(Ordering::Relaxed) - a0;
                let blocks = BLOCKS.load(Ordering::Relaxed) - b0;
                let peak = PEAK.load(Ordering::Relaxed) - base;
                let kept = LIVE.load(Ordering::Relaxed) - base;
                let result = result.unwrap_or_else(|e| panic!("{name}: {e}"));
                eprintln!(
                    "{name}\t{n}\t{ms} ms\talloc {} MB ({} B/elem, {:.1} blocks/elem)\tpeak live {} MB\tkept {} MB",
                    allocated / 1_000_000,
                    allocated as u64 / n,
                    blocks as f64 / n as f64,
                    peak / 1_000_000,
                    kept / 1_000_000,
                );
                drop((result, m, input));
            }
        }
    });
}
