//! Guards what a program pays for importing std: the checker steps spent
//! loading a tiny program that uses one common namespace, through a fresh
//! session like the benchmark's `check-closed-*` programs. Loading checks
//! the std declarations the program depends on, so one expensive proof in
//! std is paid by every importer (SW-3221: `List.inRangeReads`, proved with
//! `omega`, doubled `check-closed-*` from 1.1M to 2.09M steps and nobody
//! noticed for three days, because the benchmark's count check runs only in
//! the broad tier). Checking all of std in one go would hide it, +1.5% of
//! `List`'s 55M steps.
//!
//! Steps are the resource budget's work counter, deterministic for a given
//! std and checker. `BOUNDS` records them; the test fails when a count
//! passes its bound by more than `TOLERANCE_PERCENT`, and says so when one
//! falls that far below it (a gain worth recording).

use stitchwort_driver::driver::{Session, par_map};

const STACK: usize = 64 * 1024 * 1024;

/// How far a count may stray from its recorded bound, in percent.
const TOLERANCE_PERCENT: u64 = 10;

/// `(name, program, checker steps to load it)`, recorded on the commit that
/// added this test. To update after a deliberate change:
/// `IMPORT_COST_PRINT=1 task test:one -- importing_std` prints the counts;
/// paste them and say in the commit why std got dearer or cheaper.
const BOUNDS: &[(&str, &str, u64)] = &[
    (
        "List",
        "import Std (List, Nat)\ndef n : Nat := List.length (List.range 0 20)\n",
        1250163,
    ),
    (
        "Nat",
        "import Std (Nat)\ndef n : Nat := Nat.gcd (Nat.pow 3 4) (Nat.max 6 9)\n",
        10297569,
    ),
    (
        "Int",
        "import Std (Int, Nat)\ndef n : Int := Int.neg 5 + Nat.toInt (Nat.digitCount 12345)\n",
        16401616,
    ),
    (
        "Text",
        "import Std (Text, Nat)\ndef t : Text := Text.trim (Nat.toText (Text.length \"x\"))\n",
        9458161,
    ),
    (
        "Map",
        "import Std (Map, Nat)\ndef m : Map Nat Nat := Map.insert Map.empty 1 2\n",
        30803107,
    ),
];

fn steps(program: &str) -> u64 {
    let mut session = Session::for_stack(STACK);
    let before = session.elab.kernel.machine.budget.total_work();
    if let Err(ds) = session.load("import_cost.sw", program) {
        let text: String = ds
            .iter()
            .map(|d| format!("{}: {}\n", d.code, d.message))
            .collect();
        panic!("`{program}` doesn't check:\n{text}");
    }
    session.elab.kernel.machine.budget.total_work() - before
}

#[test]
fn importing_std_namespaces_stays_within_recorded_step_counts() {
    let counts = par_map(STACK, BOUNDS, |&(_, program, _)| steps(program));
    if std::env::var_os("IMPORT_COST_PRINT").is_some() {
        for (&(name, ..), now) in BOUNDS.iter().zip(counts) {
            println!("{name}: {now}");
        }
        return;
    }
    let mut failures = Vec::new();
    for (&(name, _, bound), now) in BOUNDS.iter().zip(counts) {
        if now * 100 > bound * (100 + TOLERANCE_PERCENT) {
            failures.push(format!(
                "the {name} program took {now} steps, over the recorded {bound} by more than {TOLERANCE_PERCENT}%"
            ));
        } else if now * 100 < bound * (100 - TOLERANCE_PERCENT) {
            eprintln!(
                "note: the {name} program took {now} steps, more than {TOLERANCE_PERCENT}% under the recorded {bound}: lower BOUNDS"
            );
        }
    }
    assert!(
        failures.is_empty(),
        "{}\n\nChecking a program that imports std got dearer. Find the new or changed proof \
         (`git log -p -- crates/elab/src/std` for the namespace; heavy `omega`, `decide` or `simp` \
         proofs are the usual cause, SW-3221; `STITCHWORT_TIMINGS=decls` shows steps per \
         declaration) and make it cheaper, or, if the cost is worth it, update BOUNDS in \
         crates/driver/tests/library/import_cost.rs with the reason in the commit.",
        failures.join("\n")
    );
}
