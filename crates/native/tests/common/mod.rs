//! What the native tests share: checking and lowering a program, running it
//! on the machine and natively, and comparing the two.

#![allow(dead_code)] // each test binary uses some of these

use std::path::Path;

use stitchwort_core::ResourceError;
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_native::n1::{Options, compile, stack_for};
use stitchwort_rt::host::{NoTerminal, RunError};
use stitchwort_rt::{Limits, Program, alloc_trace, lower_main, run_main, run_main_native};

pub const STACK: usize = 16 * 1024 * 1024 * 1024;

pub fn bench(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../bench/native")
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// `source` checked and its `main` lowered, with the default limits.
pub fn lowered(source: &str) -> (Program, Limits) {
    lowered_for(source, STACK)
}

/// [`lowered`], for a thread with `stack` bytes of stack.
pub fn lowered_for(source: &str, stack: usize) -> (Program, Limits) {
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
pub type Ran = (String, Result<(), String>);

pub fn ended(output: Vec<u8>, result: Result<(), RunError>) -> Ran {
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

pub fn on_machine(program: &Program, limits: Limits) -> Ran {
    let mut output = Vec::new();
    let result = run_main(program, limits, &mut "".as_bytes(), &mut output);
    ended(output, result)
}

/// The run with native code, and the notes on what ran natively.
pub fn native(program: &Program, limits: Limits, trace_refcounts: bool) -> (Ran, Vec<String>) {
    native_on(program, limits, trace_refcounts, STACK)
}

/// [`native`], on a thread with `stack` bytes of stack: the native stack is
/// the one the run sizes for its frames, or `stack` if that is less (the
/// stack-pointer check behind the frame counter then stops the run). If
/// the program can't be compiled, the error is why, and so are the notes.
pub fn native_on(
    program: &Program,
    limits: Limits,
    trace_refcounts: bool,
    stack: usize,
) -> (Ran, Vec<String>) {
    let options = Options { trace_refcounts };
    let mut output = Vec::new();
    let executed_before = stitchwort_rt::machine::instructions_executed();
    // Compiled as `run --native` compiles it (stage NO5 of
    // docs/proposals/native-only.md): every body or a refusal, and a stack
    // sized for the frame limit, here at most the thread's `stack`.
    let image = stitchwort_rt::code::compile(program);
    let compiled = compile(program, &image, options).and_then(|islands| {
        let sized = stack_for(limits.frames as u64, islands.max_frame, &islands.widest)?;
        Ok((islands, sized))
    });
    let (islands, sized) = match compiled {
        Ok(compiled) => compiled,
        Err(why) => return ((String::new(), Err(why.join("; "))), why),
    };
    let notes = vec![islands.note()];
    let result = run_main_native(
        program,
        image,
        Box::new(islands),
        limits,
        sized.min(stack),
        &mut "".as_bytes(),
        &mut output,
        &mut NoTerminal,
    );
    // A native run is native through and through (stage NO4 of
    // docs/proposals/native-only.md): the machine executes nothing.
    if ran_natively(&notes) {
        assert_eq!(
            stitchwort_rt::machine::instructions_executed() - executed_before,
            0,
            "the machine ran part of a native run"
        );
    }
    (ended(output, result), notes)
}

pub fn ran_natively(notes: &[String]) -> bool {
    notes.iter().any(|n| n.starts_with("native: running "))
}

/// Native code prints what the machine prints, and did run.
pub fn agrees(source: &str) -> String {
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
pub fn same_trace(source: &str) {
    let source = source.to_string();
    with_stack(STACK, move || {
        let (program, limits) = lowered(&source);
        // Out of the traces (its own values would be in the first).
        stitchwort_rt::native_abi::probe_layout().expect("the layout is as expected");
        // So is a run's first use of the runtime's per-thread caches (the
        // ASCII `Char` cells `prims::char_value` keeps), which would be in
        // the first trace only.
        let _ = on_machine(&program, limits);
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
        // Counting inline, as `run --native` does, the trace sees only the
        // cells made and freed: the same cells, and every one freed.
        alloc_trace::start();
        let (inline_ran, notes) = native(&program, limits, false);
        let inline = alloc_trace::finish();
        let (native_ran, native) = trace(true);
        // For reading them side by side.
        if let Ok(dir) = std::env::var("N1_TRACE_DIR") {
            for (name, trace) in [
                ("machine", &machine),
                ("inline", &inline),
                ("native", &native),
            ] {
                std::fs::write(format!("{dir}/{name}.trace"), trace.render()).expect("writes");
            }
        }
        assert!(ran_natively(&notes), "nothing ran natively: {notes:#?}");
        assert_eq!(inline_ran, machine_ran);
        assert_eq!(inline.count("alloc"), machine.count("alloc"));
        assert_eq!(inline.leaks(), Vec::<u32>::new(), "inline counting leaked");
        assert_eq!(native_ran, machine_ran);
        assert!(machine.count("alloc") > 0, "the program allocates nothing");
        assert_eq!(native.leaks(), Vec::<u32>::new(), "native code leaked");
        let (machine, native) = (machine.render(), native.render());
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

/// For every step limit, then every frame limit, up to the least under
/// which the run finishes, native code stops where the machine does, with
/// the same output, and frees every cell: so each error exit releases
/// exactly what is live there. The two least limits.
pub fn every_limit_agrees(program: &Program, limits: Limits) -> (u64, u64) {
    let machine = on_machine(program, limits);
    assert!(machine.1.is_ok(), "{machine:?}");
    let sweep = |limits_at: &dyn Fn(u64) -> Limits| {
        let mut k = 0;
        loop {
            let limits = limits_at(k);
            let expected = on_machine(program, limits);
            alloc_trace::start();
            let (ran, notes) = native(program, limits, false);
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
    (least_steps, least_frames)
}
