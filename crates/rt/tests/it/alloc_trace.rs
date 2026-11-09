//! The bring-up allocation trace (docs/proposals/native-compilation.md,
//! "Bring-up trace (N1 to N4)"; `stitchwort_rt::alloc_trace`): a small
//! program's trace pinned as a snapshot, and no cell left unfreed when a
//! run ends, by finishing or by an error escaping mid-map.

use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_rt::alloc_trace::{self, Trace};
use stitchwort_rt::{Limits, Policy, lower_main, run_main_with};

const STACK: usize = 256 * 1024 * 1024;

/// A list built, mapped (each cell is rebuilt in place, as nothing else
/// holds the list) and printed, then dropped.
const MAPPED: &str = r#"import Std (IO, List, Nat, Text)

def main(): {IO} () :=
  IO.print (Text.join ((List.range 0 3).map Nat.toText) ',')
"#;

/// The same, with a `Fail` that escapes `main` from the middle of the map.
const FAILING: &str = r#"import Std (Fail, IO, List, Nat, Text)

def show (x: Nat): {Fail} Text :=
  if x == 1 then Fail.fail "one" else Nat.toText x

def main(): {IO, Fail} () :=
  IO.print (Text.join ((List.range 0 3).map show) ',')
"#;

/// A record whose list field is mapped by a record update, three times in
/// a loop: nothing else holds the record, so the update takes it apart
/// before the map runs, and the list's cells and the record's are reused
/// as in the version written with a `match` ([`TAKEN_APART`]).
const UPDATED: &str = r#"import Std (IO, List, Nat, Text)

type Tally = { items: List Nat, steps: Nat }

def Tally.step (t: Tally): Tally := { t | items = t.items.map (x => x + 1), steps = t.steps + 1 }

def Tally.run (t: Tally): Nat → Tally
  | Zero => t
  | Succ rest => t.step.run rest

def main(): {IO} () :=
  let t: Tally := { items = List.range 0 3, steps = 0 }
  let done := t.run 3
  IO.print "${done.steps} ${Text.join (done.items.map Nat.toText) ','}"
"#;

/// [`UPDATED`] with the record taken apart by hand.
const TAKEN_APART: &str = r#"import Std (IO, List, Nat, Text)

type Tally = { items: List Nat, steps: Nat }

def Tally.step (t: Tally): Tally :=
  match t with
    | { items, steps } => { items = items.map (x => x + 1), steps = steps + 1 }

def Tally.run (t: Tally): Nat → Tally
  | Zero => t
  | Succ rest => t.step.run rest

def main(): {IO} () :=
  let t: Tally := { items = List.range 0 3, steps = 0 }
  let done := t.run 3
  IO.print "${done.steps} ${Text.join (done.items.map Nat.toText) ','}"
"#;

/// Runs `main` of `source` on the machine, recording from before the
/// program is lowered: the trace, what `main` printed, and the failure
/// message if it failed.
fn traced(source: &str) -> (Trace, String, Option<String>) {
    let source = source.to_string();
    with_stack(STACK, move || {
        let mut session = Session::for_stack(STACK);
        session
            .load("test.sw", &source)
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let main = session.main().expect("`main` has the right type");
        let program = lower_main(
            &session.elab.ev(),
            session.elab.options.limits,
            main.term(),
            main.row,
        )
        .expect("lowers");
        let mut output = Vec::new();
        alloc_trace::start();
        let result = run_main_with(
            &program,
            Limits::from_core(session.elab.options.limits),
            &Policy::default(),
            &mut "".as_bytes(),
            &mut output,
        );
        let trace = alloc_trace::finish();
        let failure = match result {
            Ok(_) => None,
            Err(stitchwort_rt::host::RunError::Failed(message)) => Some(message),
            Err(other) => panic!("{other}"),
        };
        (trace, String::from_utf8(output).expect("text"), failure)
    })
}

/// Every cell allocated is freed by the time the run has ended.
fn assert_no_leaks(trace: &Trace) {
    assert_eq!(
        trace.leaks(),
        Vec::<u32>::new(),
        "leaked cells:\n{}",
        trace.render()
    );
}

#[test]
fn a_mapped_list_is_reused_in_place_and_freed() {
    let (trace, output, failure) = traced(MAPPED);
    assert_eq!((output.as_str(), failure), ("0,1,2\n", None));
    assert_no_leaks(&trace);
    assert!(
        trace.count("reuse") > 0,
        "no cell was reused:\n{}",
        trace.render()
    );
    insta::assert_snapshot!(trace.render());
}

#[test]
fn a_failure_escaping_mid_map_frees_everything() {
    let (trace, _, failure) = traced(FAILING);
    assert_eq!(failure.as_deref(), Some("one"));
    assert!(trace.count("alloc") > 0, "{}", trace.render());
    assert_no_leaks(&trace);
}

#[test]
fn the_same_program_gives_the_same_text_twice() {
    // Identities are renumbered by first appearance, not addresses.
    assert_eq!(traced(MAPPED).0.render(), traced(MAPPED).0.render());
}

#[test]
fn a_record_update_of_a_unique_record_reuses_its_field_in_place() {
    let (updated, output, failure) = traced(UPDATED);
    assert_eq!((output.as_str(), failure), ("3 3,4,5\n", None));
    assert_no_leaks(&updated);
    let (by_hand, output, _) = traced(TAKEN_APART);
    assert_eq!(output, "3 3,4,5\n");
    assert_eq!(
        (updated.count("alloc"), updated.count("reuse")),
        (by_hand.count("alloc"), by_hand.count("reuse")),
        "the update allocates more than the match:\n{}\nagainst\n{}",
        updated.render(),
        by_hand.render()
    );
}
