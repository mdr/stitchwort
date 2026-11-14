//! Guards what importing std costs: the checker steps spent checking the
//! files of each of the namespaces programs import most (`check --std
//! <namespace>`: the namespace's files and what they need). Std's declarations are checked
//! whenever a program imports their namespace, so one expensive proof in
//! std (SW-3221: `List.inRangeReads`, about 860,000 steps in `omega`) is
//! paid by every importer, and shows up nowhere else until the benchmark's
//! count check runs in the broad tier.
//!
//! Steps are the resource budget's work counter, deterministic for a given
//! std and checker. `BOUNDS` records them; the test fails when a count
//! passes its bound by more than `TOLERANCE_PERCENT`, and says so when one
//! falls that far below it (a gain worth recording).

use stitchwort_driver::driver::{Session, par_map};

const STACK: usize = 64 * 1024 * 1024;

/// How far a count may stray from its recorded bound, in percent.
const TOLERANCE_PERCENT: u64 = 10;

/// `(namespace, checker steps to check its files)`, recorded on
/// the commit that added this test. To update after a deliberate change:
/// `IMPORT_COST_PRINT=1 task test:one -- importing_std` prints the table in
/// this form; paste it and say in the commit why std got dearer or cheaper.
const BOUNDS: &[(&str, u64)] = &[
    ("Bool", 1477089),
    ("Int", 13736060),
    ("List", 55789355),
    ("Map", 30905125),
    ("Nat", 21386860),
    ("Option", 206060),
    ("Result", 9384051),
    ("Set", 52366027),
    ("Text", 14550376),
    ("Vec", 19891542),
];

fn steps(namespace: &str) -> u64 {
    let mut session = Session::for_stack(STACK);
    let before = session.elab.kernel.machine.budget.total_work();
    if let Err(ds) = session.elab.check_library_targets(&[namespace.to_string()]) {
        panic!("checking std's `{namespace}` failed: {ds:?}");
    }
    session.elab.kernel.machine.budget.total_work() - before
}

#[test]
fn importing_std_namespaces_stays_within_recorded_step_counts() {
    if std::env::var_os("IMPORT_COST_PRINT").is_some() {
        for (namespace, now) in par_map(STACK, BOUNDS, |&(namespace, _)| {
            (namespace, steps(namespace))
        }) {
            println!("    (\"{namespace}\", {now}),");
        }
        return;
    }
    let mut failures = Vec::new();
    let counts = par_map(STACK, BOUNDS, |&(namespace, _)| steps(namespace));
    for (&(namespace, bound), now) in BOUNDS.iter().zip(counts) {
        if now * 100 > bound * (100 + TOLERANCE_PERCENT) {
            failures.push(format!(
                "checking std's `{namespace}` took {now} steps, over the recorded {bound} by more than {TOLERANCE_PERCENT}%"
            ));
        } else if now * 100 < bound * (100 - TOLERANCE_PERCENT) {
            eprintln!(
                "note: checking std's `{namespace}` took {now} steps, more than {TOLERANCE_PERCENT}% under the recorded {bound}: lower BOUNDS"
            );
        }
    }
    assert!(
        failures.is_empty(),
        "{}\n\nA declaration std checks on import got dearer. Find the new or changed proof \
         (`git log -p -- crates/elab/src/std` for the namespace; heavy `omega`, `decide` or `simp` \
         proofs are the usual cause, SW-3221) and make it cheaper, or, if the cost is worth it, \
         update BOUNDS in crates/driver/tests/library/import_cost.rs with the reason in the commit.",
        failures.join("\n")
    );
}

/* Left out to keep the test under about ten seconds: Abort, Array, Decidable,
Each, Effect, Fail, Fin, Finite, Float, Function, Graph, Mod, NonEmptyList,
Omega, Ord, Parse, Quot, Random, Ring, Terminal. Add one when it grows
something worth guarding. */
