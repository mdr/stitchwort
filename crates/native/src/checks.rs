//! The spike's checks and measurements, shared by its tests and by
//! `stitchwort dev native-spike` (which prints them).

use std::hint::black_box;
use std::time::{Duration, Instant};

use crate::spike::{
    Code, CodeMemory, Context, OK, OUT_OF_FRAMES, OUT_OF_STEPS, Spike, VARIANTS, Variant,
};

/// `1 + 2 + … + n`.
pub fn triangle(n: i64) -> i64 {
    n * (n + 1) / 2
}

/// The deepest the native stack went below `top` (an address in the
/// caller's frame), in bytes, as `note_step` saw it.
fn depth_below(top: u64, context: &Context) -> u64 {
    top.saturating_sub(context.lowest_stack)
}

/// An address in the current frame: roughly the stack pointer.
fn stack_here() -> u64 {
    let marker = 0u8;
    black_box(&marker) as *const u8 as u64
}

/// Runs `f` on a new thread with `stack` bytes of reserved stack.
pub fn on_stack<T: Send>(stack: usize, f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(stack)
            .spawn_scoped(scope, f)
            .expect("spawning a thread")
            .join()
            .expect("the thread panicked")
    })
}

/// A tail-call run: its result, its counters and the native stack it used.
#[derive(Debug)]
pub struct TailRun {
    pub result: i64,
    pub context: Context,
    /// Stack used by a 10-step run and by the long run, in bytes.
    pub short_depth: u64,
    pub long_depth: u64,
}

/// `count_loop` (the self tail call as a loop) for `n` steps.
pub fn self_tail_loop(code: Code, n: i64) -> TailRun {
    tail_run(n, |context, n| code.count_loop(context, n, 0))
}

/// `even`/`odd` (mutual tail calls) for `n` steps.
pub fn mutual_tail_calls(code: Code, n: i64) -> TailRun {
    tail_run(n, |context, n| code.even_odd(context, n))
}

fn tail_run(n: i64, run: impl Fn(&mut Context, i64) -> i64 + Send + Sync) -> TailRun {
    // A small stack (256 KiB): a call that grew the stack on every step
    // would overflow it after a few thousand.
    on_stack(256 * 1024, || {
        let top = stack_here();
        let mut short = Context::unlimited();
        run(&mut short, 10);
        let mut context = Context::unlimited();
        let result = run(&mut context, n);
        TailRun {
            result,
            short_depth: depth_below(top, &short),
            long_depth: depth_below(top, &context),
            context,
        }
    })
}

/// A deep non-tail recursion: its result, its counters, and the stack per
/// frame.
#[derive(Debug)]
pub struct DeepRun {
    pub result: i64,
    pub context: Context,
    pub stack_used: u64,
}

impl DeepRun {
    /// Native stack per pending frame (one level of `sum`), in bytes.
    pub fn bytes_per_frame(&self) -> f64 {
        self.stack_used as f64 / self.context.callbacks.max(1) as f64
    }
}

/// The machine's frame limit (`crates/rt/src/machine.rs`).
pub const FRAME_LIMIT: u64 = 2_000_000;

/// The reserved stack the deep runs get: the note's "about 1 GiB".
pub const BIG_STACK: usize = 1024 * 1024 * 1024;

/// `sum(n)` with counting and the callback, on a thread with `BIG_STACK`
/// and a frame limit of `FRAME_LIMIT`.
pub fn deep_recursion(code: Code, n: i64) -> DeepRun {
    on_stack(BIG_STACK, || {
        let top = stack_here();
        let mut context = Context::new(u64::MAX, FRAME_LIMIT);
        let variant = Variant {
            counting: true,
            callback: true,
        };
        let result = code.sum(variant, &mut context, n);
        DeepRun {
            result,
            stack_used: depth_below(top, &context),
            context,
        }
    })
}

/// `count_loop` with a step limit of `limit`.
pub fn step_limited(code: Code, limit: u64, n: i64) -> (i64, Context) {
    let mut context = Context::new(limit, FRAME_LIMIT);
    let result = code.count_loop(&mut context, n, 0);
    (result, context)
}

/// The per-call benchmark, shaped like `micro_call.sw` (§1.3 of the note):
/// `rounds` calls of `sum(20)`, so 21 entries and 20 pending frames each.
pub const CALL_DEPTH: i64 = 20;

/// Nanoseconds per call (function entry) of `call`, the best of five runs.
pub fn ns_per_call(rounds: u64, mut call: impl FnMut() -> i64) -> f64 {
    let calls = rounds as f64 * (CALL_DEPTH + 1) as f64;
    let mut best = Duration::MAX;
    for _ in 0..5 {
        let start = Instant::now();
        let mut total = 0i64;
        for _ in 0..rounds {
            total = total.wrapping_add(call());
        }
        black_box(total);
        best = best.min(start.elapsed());
    }
    best.as_nanos() as f64 / calls
}

/// The same recursion in Rust, for comparison on this machine: plain.
#[inline(never)]
fn rust_sum(n: i64) -> i64 {
    if n == 0 {
        0
    } else {
        black_box(n) + rust_sum(n - 1)
    }
}

/// … and counting steps and frames as the native code does.
#[inline(never)]
fn rust_sum_counting(context: &mut Context, n: i64) -> i64 {
    context.steps += 1;
    if context.steps > context.step_limit {
        context.error = OUT_OF_STEPS;
        return 0;
    }
    if n == 0 {
        return 0;
    }
    context.frames += 1;
    if context.frames > context.frame_limit {
        context.error = OUT_OF_FRAMES;
        return 0;
    }
    let rest = rust_sum_counting(context, n - 1);
    context.frames -= 1;
    if context.error != OK {
        return 0;
    }
    black_box(n) + rest
}

/// Per-call costs: each native variant, and Rust plain and counting.
pub fn call_costs(code: Code, rounds: u64) -> Vec<(String, f64)> {
    let mut costs = Vec::new();
    for variant in VARIANTS {
        let mut context = Context::unlimited();
        let ns = ns_per_call(rounds, || {
            code.sum(variant, &mut context, black_box(CALL_DEPTH))
        });
        costs.push((
            format!(
                "native, {}, {}",
                if variant.counting {
                    "counting"
                } else {
                    "no counting"
                },
                if variant.callback {
                    "calls Rust each step"
                } else {
                    "no callback"
                }
            ),
            ns,
        ));
    }
    costs.push((
        "Rust, plain".to_string(),
        ns_per_call(rounds, || rust_sum(black_box(CALL_DEPTH))),
    ));
    let mut context = Context::unlimited();
    costs.push((
        "Rust, counting".to_string(),
        ns_per_call(rounds, || {
            rust_sum_counting(&mut context, black_box(CALL_DEPTH))
        }),
    ));
    costs
}

/// Runs every check, panicking on a failure, and returns the report.
pub fn report(memory: CodeMemory, rounds: u64) -> Result<String, String> {
    let mut out = String::new();
    let mut line = |text: String| {
        out.push_str(&text);
        out.push('\n');
    };
    line(format!(
        "Cranelift 0.136.2 JIT on {}, code memory {memory:?}",
        crate::spike::target_description()
    ));
    let spike = Spike::compile_into(memory)?;
    let code = spike.code;
    line(format!(
        "compile: {:.0} µs for the whole module (ISA, 8 functions, finalize)",
        spike.total_compile_time.as_secs_f64() * 1e6
    ));
    for (name, time) in &spike.compile_times {
        line(format!("  {name}: {:.0} µs", time.as_secs_f64() * 1e6));
    }

    for variant in VARIANTS {
        let mut context = Context::unlimited();
        assert_eq!(code.sum(variant, &mut context, 1000), triangle(1000));
    }
    line("sum, all four variants: 1 + … + 1000 = 500500".to_string());

    let (result, context) = step_limited(code, 1000, 3_000_000);
    assert_eq!(
        (result, context.error, context.steps),
        (0, OUT_OF_STEPS, 1001)
    );
    line("step limit 1000: stops with OUT_OF_STEPS at step 1001".to_string());

    for (name, run) in [
        ("self tail call (loop)", self_tail_loop(code, 3_000_000)),
        (
            "mutual tail calls (return_call)",
            mutual_tail_calls(code, 3_000_000),
        ),
    ] {
        assert_eq!(run.result, triangle(3_000_000));
        assert_eq!(run.context.error, OK);
        assert_eq!(run.context.steps, 3_000_001);
        assert_eq!(run.context.callbacks, 3_000_000);
        assert_eq!(run.long_depth, run.short_depth);
        line(format!(
            "{name}: 3,000,000 steps on a 256 KiB stack, {} bytes deep after 10 steps and after 3,000,000",
            run.long_depth
        ));
    }

    let deep = deep_recursion(code, 1_000_000);
    assert_eq!(deep.result, triangle(1_000_000));
    assert_eq!((deep.context.error, deep.context.frames), (OK, 0));
    let per_frame = deep.bytes_per_frame();
    line(format!(
        "non-tail recursion 1,000,000 deep on a 1 GiB stack: fine, {:.1} MB of stack, {per_frame:.0} bytes a frame",
        deep.stack_used as f64 / 1e6
    ));

    let too_deep: i64 = 100_000_000;
    let would_need = too_deep as f64 * per_frame;
    assert!(would_need > BIG_STACK as f64);
    let over = deep_recursion(code, too_deep);
    assert_eq!(
        (over.result, over.context.error, over.context.frames),
        (0, OUT_OF_FRAMES, FRAME_LIMIT + 1)
    );
    line(format!(
        "recursion 100,000,000 deep (would need {:.1} GB of stack): OUT_OF_FRAMES at frame {}, about {:.0} MB down a 1 GiB stack",
        would_need / 1e9,
        FRAME_LIMIT + 1,
        (FRAME_LIMIT + 1) as f64 * per_frame / 1e6
    ));

    line(format!(
        "per call ({} × sum({CALL_DEPTH}), best of 5; the note's Rust figures are 0.6 ns plain, 2.2 ns counting):",
        rounds
    ));
    for (name, ns) in call_costs(code, rounds) {
        line(format!("  {name}: {ns:.2} ns"));
    }
    Ok(out)
}
