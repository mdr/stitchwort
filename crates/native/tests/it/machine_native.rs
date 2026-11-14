//! The machine's differential cases (`stitchwort-rt`'s `machine.rs`, kept
//! in `differential.rs`) run on native code instead: the same programs and
//! inputs, against the reference evaluator.
//!
//! Opt-in, so the default runs don't grow: the tests are `ignore`d, and run with
//! `task test:one -- --run-ignored only -E 'binary(it) & test(/^machine_native::/)'`
//! (docs/reviews/SW-2535-native-default-plan.md, N5a/N5b).

differential_tests!(
    ignore = "native copy of the machine's differential cases; run with --run-ignored"
);
