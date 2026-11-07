//! The profiler's accounting (`stitchwort_rt::profile`, `run --profile`),
//! on small programs sampled at every frame entry, so every count is
//! exact: calls, self and total per definition, through recursion, nested
//! calls, tail calls and lambdas.

use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_driver::run::NoTerminal;
use stitchwort_rt::profile::{Row, Sampling};

const STACK: usize = 256 * 1024 * 1024;

/// Runs `main` of `source`, profiled at every entry: what it printed, and
/// the profile's rows.
fn profiled(source: &str) -> (String, Vec<Row>) {
    let source = source.to_string();
    with_stack(STACK, move || {
        let mut session = Session::for_stack(STACK);
        session
            .load("test.sw", &source)
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let main = session.main().expect("`main` has the right type");
        let mut output = Vec::new();
        let (result, profile) = session.run_main_fast_profiling_on(
            &main,
            Sampling::EachEntry,
            &mut "".as_bytes(),
            &mut output,
            &mut NoTerminal,
            |_| {},
        );
        result.expect("runs");
        let rows = profile.expect("lowered").rows();
        (String::from_utf8(output).expect("text"), rows)
    })
}

/// The row named `name`, as (calls, self, total).
fn row(rows: &[Row], name: &str) -> (u64, u64, u64) {
    let found = rows.iter().find(|row| row.name == name);
    let row = found.unwrap_or_else(|| panic!("no row `{name}` in {rows:#?}"));
    (row.calls, row.self_time, row.total_time)
}

#[test]
fn recursion_counts_each_call_but_each_sample_once() {
    let (output, rows) = profiled(
        r#"import Std (IO, Nat, Text)

def fact (n: Nat): Nat :=
  match n with
    | 0 => 1
    | Succ m => n * fact m

def main(): {IO} () := IO.print (fact 5).toText
"#,
    );
    assert_eq!(output, "120\n");
    // Six calls, each a sample with `fact` on top; with up to six `fact`
    // frames pending, its total still counts each sample once.
    assert_eq!(row(&rows, "Main.fact"), (6, 6, 6));
}

#[test]
fn a_callee_s_time_is_in_its_caller_s_total() {
    let (output, rows) = profiled(
        r#"import Std (IO, Nat, Text)

def countDown (n: Nat): Nat :=
  match n with
    | 0 => 0
    | Succ m => countDown m

-- Recursive, so not inlined: entered once, with `countDown` below it.
def outer (k: Nat) (n: Nat): Nat :=
  match k with
    | 0 => countDown n + 1
    | Succ j => outer j n

def main(): {IO} () := IO.print (outer 0 9).toText
"#,
    );
    assert_eq!(output, "1\n");
    // `countDown`'s ten entries (nine of them tail calls) are its own...
    assert_eq!(row(&rows, "Main.countDown"), (10, 10, 10));
    // ... and in `outer`'s total, with `outer`'s own entry.
    assert_eq!(row(&rows, "Main.outer"), (1, 1, 11));
}

#[test]
fn a_tail_call_leaves_its_caller_on_the_stack() {
    let (output, rows) = profiled(
        r#"import Std (IO, Nat, Text)

def countDown (n: Nat): Nat :=
  match n with
    | 0 => 0
    | Succ m => countDown m

-- Its call of `countDown` is a tail call, which replaces its frame.
def viaTail (k: Nat) (n: Nat): Nat :=
  match k with
    | 0 => countDown n
    | Succ j => viaTail j n

def main(): {IO} () := IO.print (viaTail 0 9 + 1).toText
"#,
    );
    assert_eq!(output, "1\n");
    assert_eq!(row(&rows, "Main.countDown"), (10, 10, 10));
    assert_eq!(row(&rows, "Main.viaTail"), (1, 1, 11));
}

#[test]
fn a_lambda_is_charged_to_the_definition_that_makes_it() {
    let (output, rows) = profiled(
        r#"import Std (IO, List, Nat, Text)

def shifted (by: Nat) (xs: List Nat): List Nat := xs.map (x => x + by)

def main(): {IO} () :=
  let xs := List.range 0 4
  IO.print (shifted xs.length xs).sum.toText
"#,
    );
    assert_eq!(output, "22\n");
    let (calls, own, total) = row(&rows, "Main.shifted.λ");
    assert_eq!(calls, 4, "{rows:#?}");
    assert_eq!((own, total), (4, 4));
}

#[test]
fn self_times_add_up_to_the_samples() {
    let (_, rows) = profiled(
        r#"import Std (IO, List, Nat, Text)

def main(): {IO} () := IO.print (List.range 0 50).sum.toText
"#,
    );
    let samples: u64 = rows.iter().map(|row| row.self_time).sum();
    assert!(samples > 0);
    for row in &rows {
        assert!(row.total_time <= samples, "{row:?} over {samples}");
        assert!(row.self_time <= row.total_time, "{row:?}");
    }
    // Every entry is a sample.
    assert_eq!(samples, rows.iter().map(|row| row.calls).sum::<u64>());
}
