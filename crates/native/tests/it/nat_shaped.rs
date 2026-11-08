//! Types shaped like `Nat` run as machine numbers
//! (docs/proposals/nat-shaped-types.md, stage 1): `Fin`, and types of the
//! program's own in either constructor order, with a parameter, a proof
//! field or an index. The representation can't be seen, so the reference
//! evaluator (on unary values), the machine and native code print the same,
//! and the machine and native code stop at the same step and frame limits,
//! which are the ones they had when these were cells.

use crate::common::*;
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_driver::run::Policy;
use stitchwort_rt::{Limits, Program};

fn example() -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/accept/nat-shaped.sw");
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// What `main` prints on the reference evaluator.
fn on_reference(source: &str) -> String {
    let mut session = Session::for_stack(STACK);
    session.use_test_std_cache();
    session
        .load("test.sw", source)
        .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
    let main = session.main().expect("`main` has the right type");
    let mut output = Vec::new();
    session
        .run_main_with(
            &main,
            &mut std::io::empty(),
            &mut output,
            &Policy::default(),
            &mut |_| {},
        )
        .expect("runs");
    String::from_utf8(output).expect("text")
}

/// The least limit, set by `at`, under which the machine finishes, found by
/// bisection (a run that finishes under a limit finishes under every larger
/// one); native code stops where the machine does just below it, and
/// finishes the same way at it.
fn least(program: &Program, at: &dyn Fn(u64) -> Limits) -> u64 {
    let finishes = |k: u64| on_machine(program, at(k)).1.is_ok();
    let (mut low, mut high) = (0, 1);
    while !finishes(high) {
        low = high;
        high *= 2;
    }
    while low + 1 < high {
        let mid = low + (high - low) / 2;
        if finishes(mid) {
            high = mid;
        } else {
            low = mid;
        }
    }
    for k in [high - 1, high] {
        let (ran, notes) = native(program, at(k), false);
        assert!(ran_natively(&notes), "{notes:#?}");
        assert_eq!(ran, on_machine(program, at(k)), "at limit {k}");
    }
    high
}

#[test]
fn nat_shaped_types_agree_on_every_runner() {
    let source = example();
    let printed = "12 6 9 [\"zero\", \"one\", \"other\", \"three\", \"other\"] 5 100 9 16 \
                   [0, 3, 10] lt eq 6\n";
    assert_eq!(agrees(&source), printed);
    let reference = source.clone();
    let on_ref = with_stack(STACK, move || on_reference(&reference));
    assert_eq!(on_ref, printed);
    same_trace(&source);
    with_stack(STACK, move || {
        let (program, limits) = lowered(&source);
        let steps = least(&program, &|n| Limits { steps: n, ..limits });
        let frames = least(&program, &|n| Limits {
            frames: n as usize,
            ..limits
        });
        assert_eq!((steps, frames), (562, 11));
    });
}
