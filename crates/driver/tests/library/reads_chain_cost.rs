//! Guards the checker steps of a two-step `readsThen` proof (`readsTwo`)
//! against a miniature parser library, generic over what it reads and over
//! characters only (`reads_chain/`). Each lemma's result type is compared
//! with the goal before its arguments are checked, solving the lemma's
//! unknowns from the arguments of the two `Reads` calls where the plain
//! comparison can't. Without that, the comparison fails, the ability's
//! parameter `t` stays unknown while the arguments are checked, and the
//! proof takes about seven times its bound generic and five times over
//! characters (SW-3281).
//!
//! Only the proof's own steps are counted: the program without it is loaded
//! first and its steps taken away, in a session that has loaded the library
//! files both need already.

use stitchwort_driver::driver::{Session, par_map};

const STACK: usize = 64 * 1024 * 1024;

/// How far a count may stray from its recorded bound, in percent.
const TOLERANCE_PERCENT: u64 = 25;

/// `(name, program, steps of its readsTwo)`. To update after a deliberate
/// change: `READS_CHAIN_PRINT=1 task test:one -- reads_chain` prints them.
const BOUNDS: &[(&str, &str, u64)] = &[
    ("generic", include_str!("reads_chain/generic.sw"), 38452),
    (
        "characters",
        include_str!("reads_chain/characters.sw"),
        32406,
    ),
];

/// The steps `program`'s last declaration, `readsTwo`, takes to check.
fn proof_steps(program: &str) -> u64 {
    let at = program
        .find("theorem readsTwo")
        .expect("the program ends with readsTwo");
    let imports: String = program
        .lines()
        .take_while(|l| l.starts_with("import") || l.starts_with("--"))
        .map(|l| format!("{l}\n"))
        .collect();
    let mut session = Session::for_stack(STACK);
    load(&mut session, &imports);
    let mark = session.mark();
    let without = load(&mut session, &program[..at]);
    session.rewind(&mark);
    let with = load(&mut session, program);
    with - without
}

/// Loads `text` into `session`: the steps it took.
fn load(session: &mut Session, text: &str) -> u64 {
    let before = session.elab.kernel.machine.budget.total_work();
    if let Err(ds) = session.load("reads_chain.sw", text) {
        let text: String = ds
            .iter()
            .map(|d| format!("{}: {}\n", d.code, d.message))
            .collect();
        panic!("the program doesn't check:\n{text}");
    }
    session.elab.kernel.machine.budget.total_work() - before
}

#[test]
fn reads_chain_proofs_stay_within_recorded_step_counts() {
    let counts = par_map(STACK, BOUNDS, |&(_, program, _)| proof_steps(program));
    if std::env::var_os("READS_CHAIN_PRINT").is_some() {
        for (&(name, ..), now) in BOUNDS.iter().zip(counts) {
            println!("{name}: {now}");
        }
        return;
    }
    let mut failures = Vec::new();
    for (&(name, _, bound), now) in BOUNDS.iter().zip(counts) {
        if now * 100 > bound * (100 + TOLERANCE_PERCENT) {
            failures.push(format!(
                "{name}: readsTwo took {now} steps, over its bound of {bound} by more than {TOLERANCE_PERCENT}%"
            ));
        } else if now * 100 < bound * (100 - TOLERANCE_PERCENT) {
            println!(
                "{name}: readsTwo took {now} steps, well under its bound of {bound}: worth recording"
            );
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
