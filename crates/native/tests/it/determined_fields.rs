//! Constructor fields the result indices determine aren't stored by the
//! machine or native code, and a match that reads one rebuilds it
//! (docs/proposals/erase-determined-fields.md). The reference evaluator
//! stores them, so it checks the rebuilt values: examples/accept/
//! determined-fields.sw prints the same on all three, and the same again
//! when lowered with the fields stored as well and every rebuild compared
//! with the stored field.

use crate::common::*;
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_driver::run::Policy;

fn example() -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/accept/determined-fields.sw");
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

#[test]
fn determined_fields_agree_on_every_runner() {
    let source = example();
    with_stack(STACK, move || {
        let expected = on_reference(&source);
        assert!(expected.starts_with("height 3,"), "{expected}");
        for check in [false, true] {
            let _check = check.then(stitchwort_rt::erasure::checking_rebuilds);
            let (program, limits) = lowered(&source);
            let machine = on_machine(&program, limits);
            assert_eq!(machine, (expected.clone(), Ok(())), "checked: {check}");
            let (native, notes) = native(&program, limits, false);
            assert!(ran_natively(&notes), "{notes:#?}");
            assert_eq!(native, machine, "checked: {check}");
        }
    });
}

/// The cells without their determined fields are made and freed alike by
/// the machine and native code.
#[test]
fn determined_fields_traces_are_the_same() {
    same_trace(&example());
}
