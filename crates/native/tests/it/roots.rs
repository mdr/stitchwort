//! A program of several roots and no entry, as `stitchwort test --native`
//! compiles its tests (SW-2543, `n1::compile_roots`): each root constant is
//! a way into the code, computed in a frame of its own as the machine's
//! `Machine::global` computes it, with the same value and at the same step
//! and frame limits, and kept for the next root that uses it.

use crate::common::*;
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_native::n1::{Options, compile_roots, stack_for};
use stitchwort_rt::ir::{GlobalId, GlobalKind};
use stitchwort_rt::native_abi::NativeExecutor;
use stitchwort_rt::value::Value;
use stitchwort_rt::{Executor, Limits, Machine, Program, lower_definitions};

const TESTS: &str = r#"import Std (List)

def numbers: List Nat := List.range 0 200

def deeper: Nat -> Nat
  | 0 => 0
  | Succ k => deeper k * 2

test "sum" := List.sum numbers == 19900
test "wrong sum" := List.sum numbers == 19901
test "length" := numbers.length == 200
test "deep" := deeper 3000 == 0
"#;

/// `TESTS` lowered as `stitchwort test` lowers its tests, and each test's
/// global.
fn lowered_tests() -> (Program, Limits, Vec<u32>) {
    let mut session = Session::for_stack(STACK);
    session.use_test_std_cache();
    session
        .load("test.sw", TESTS)
        .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
    let defs: Vec<_> = session.elab.tests().iter().map(|t| t.def).collect();
    let program =
        lower_definitions(&session.elab.ev(), session.elab.options.limits, &defs).expect("lowers");
    let roots = defs
        .iter()
        .map(|def| {
            let g = program.globals.iter().position(|g| g.def == *def).unwrap();
            assert!(matches!(
                program.globals[g].kind,
                GlobalKind::Constant { .. }
            ));
            u32::try_from(g).unwrap()
        })
        .collect();
    (
        program,
        Limits::from_core(session.elab.options.limits),
        roots,
    )
}

/// Each root's value (or error) natively under `limits`, one executor for
/// them all.
fn natively(program: &Program, roots: &[u32], limits: Limits) -> Vec<Result<Value, String>> {
    let image = stitchwort_rt::code::compile(program);
    let islands = compile_roots(program, image, roots, Options::default()).expect("compiles");
    let stack = stack_for(limits.frames as u64, islands.max_frame, &islands.widest).unwrap();
    let mut executor = NativeExecutor::new(Box::new(islands), limits, stack.min(STACK));
    roots
        .iter()
        .map(|&g| {
            executor.reset_steps();
            executor
                .global(g)
                .expect("a root")
                .map_err(|e| e.to_string())
        })
        .collect()
}

/// [`natively`] on the machine.
fn on_the_machine(program: &Program, roots: &[u32], limits: Limits) -> Vec<Result<Value, String>> {
    let mut machine = Machine::new(program, limits);
    roots
        .iter()
        .map(|&g| {
            machine.reset_steps();
            machine.global(GlobalId(g)).map_err(|e| e.to_string())
        })
        .collect()
}

fn shown(results: &[Result<Value, String>]) -> Vec<String> {
    results
        .iter()
        .map(|r| match r {
            Ok(Value::Tag(t)) => format!("tag {t}"),
            Ok(_) => "another value".to_string(),
            Err(e) => e.clone(),
        })
        .collect()
}

#[test]
fn each_root_gives_the_machines_value() {
    with_stack(STACK, || {
        let (program, limits, roots) = lowered_tests();
        let executed_before = stitchwort_rt::machine::instructions_executed();
        let native = shown(&natively(&program, &roots, limits));
        assert_eq!(
            stitchwort_rt::machine::instructions_executed() - executed_before,
            0,
            "the machine ran part of a native run"
        );
        let true_ = program.shapes.true_;
        let false_ = 1 - true_;
        assert_eq!(
            native,
            [true_, false_, true_, true_].map(|t| format!("tag {t}"))
        );
        assert_eq!(native, shown(&on_the_machine(&program, &roots, limits)));
    });
}

/// Step and frame limits from nothing up past what the roots need: both
/// runners stop, or finish, alike. The constant `numbers`, which the first
/// three tests share, is computed by whichever needs it first and counted
/// there.
#[test]
fn each_root_stops_at_the_machines_limits() {
    with_stack(STACK, || {
        let (program, limits, roots) = lowered_tests();
        // The ranges reach limits under which every root finishes.
        let finished = |limits| natively(&program, &roots, limits).iter().all(Result::is_ok);
        assert!(finished(Limits {
            steps: 11_000,
            ..limits
        }));
        assert!(finished(Limits {
            frames: 3_050,
            ..limits
        }));
        for steps in (0..40).chain((40..12_000).step_by(97)) {
            let limits = Limits { steps, ..limits };
            assert_eq!(
                shown(&natively(&program, &roots, limits)),
                shown(&on_the_machine(&program, &roots, limits)),
                "at a step limit of {steps}"
            );
        }
        for frames in (0..20).chain((20..3_100).step_by(61)) {
            let limits = Limits { frames, ..limits };
            assert_eq!(
                shown(&natively(&program, &roots, limits)),
                shown(&on_the_machine(&program, &roots, limits)),
                "at a frame limit of {frames}"
            );
        }
    });
}
