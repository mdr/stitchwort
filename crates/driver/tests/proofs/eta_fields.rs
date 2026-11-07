//! Record eta's rule 2 on a glued call (`value::eta_fields`): a field of a
//! call is forced once, however deep the calls nest. A `Map` built by
//! folding over the one before it, `n` times on an unknown list, is compared
//! with itself through another name: each level's `m.raw` is a field of the
//! call below, and forcing it used to unfold that call's folded body again,
//! doubling the work at every level (SW-1829: AoC 2024 day 11's
//! `part2Correct`, 75 levels, never finished). At 24 levels that would take hours;
//! now it's a fraction of a second beyond loading the library.

use stitchwort_driver::driver::Session;

const PROGRAM: &str = r#"
import Std (List, Map, Nat)

def blinkCounts (counts: Map Nat Nat): Map Nat Nat :=
  counts.foldLeft Map.empty (blinked stone count => blinked.insertWith stone count Nat.add)

def countAfter (blinks: Nat) (stones: List Nat): Nat :=
  blinks.iterate blinkCounts (Map.counts stones) |> .values |> .sum

def solve (stones: List Nat): Nat := countAfter 24 stones

theorem same (stones: List Nat): solve stones = countAfter 24 stones := rfl
"#;

#[test]
fn nested_fields_of_calls_are_forced_once() {
    let mut session = Session::eager();
    if let Err(e) = session.load("nested.sw", PROGRAM) {
        panic!("{e:?}");
    }
}
