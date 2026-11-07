//! Arrays on the machine (docs/proposals/arrays.md §4.2): a `set`, `push` or
//! `pop` on an array nothing else holds changes it in place, and one on an
//! array something else holds copies it first, so that what the other holder
//! sees never changes. The copy counter counts exactly those copies.

use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_rt::{ArrayCopies, Limits, array_copies, lower_main, run_main};

const STACK: usize = 256 * 1024 * 1024;

/// What `main` in `source` prints on the machine, and the copies it made.
fn run(source: &str) -> (String, ArrayCopies) {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load("test.sw", &format!("import Std (Array)\n\n{source}"))
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
        run_main(
            &program,
            Limits::from_core(session.elab.options.limits),
            &mut "".as_bytes(),
            &mut output,
        )
        .expect("runs");
        (
            String::from_utf8(output)
                .expect("text")
                .trim_end()
                .to_string(),
            array_copies(),
        )
    })
}

fn show(parts: &[&str]) -> String {
    parts
        .iter()
        .map(|p| format!("Show.toText ({p})"))
        .collect::<Vec<_>>()
        .join(" ++ \" \" ++ ")
}

/// The soundness test: changing an array that another variable still holds
/// leaves that variable's array as it was, and is one counted copy.
#[test]
fn a_shared_array_is_copied_not_changed() {
    let (out, copies) = run(&format!(
        "def main (): {{IO}} () :=\n  let a := Array.replicate (count := 5) 0\n  \
         let b := a.set 0 1\n  let c := a.push 7\n  \
         IO.print ({})\n",
        show(&[
            "a.toList",
            "b.toList",
            "c.toList",
            "a.pop.map (.snd)",
            "a.size"
        ])
    ));
    assert_eq!(
        out,
        "[0, 0, 0, 0, 0] [1, 0, 0, 0, 0] [0, 0, 0, 0, 0, 7] Some 0 5"
    );
    // `set`, `push` and `pop` each found `a` held by later uses.
    assert_eq!(copies.count, 3, "{copies:?}");
    assert_eq!(copies.largest, 5);
}

/// A loop that passes its array on changes it in place: no copies, however
/// many steps.
#[test]
fn a_threaded_array_is_changed_in_place() {
    let (out, copies) = run("def fill: (n: Nat) → (array: Array Nat) → Array Nat\n  \
         | Zero, array => array\n  \
         | Succ k, array => fill k ((array.set k (k * 2)).push k)\n\n\
         def drain: (n: Nat) → (array: Array Nat) → Nat → Nat\n  \
         | Zero, array, acc => acc\n  \
         | Succ k, array, acc => match array.pop with\n    \
         | Some (rest, x) => drain k rest (acc + x)\n    \
         | None => acc\n\n\
         def main (): {IO} () :=\n  \
         let filled := fill 100000 (Array.replicate (count := 100000) 0)\n  \
         IO.print (Show.toText (filled.getOr 99999 0) ++ \" \" ++ Show.toText filled.size ++ \" \" ++ Show.toText (drain 100000 filled 0))\n");
    assert_eq!(out, "199998 200000 4999950000");
    assert_eq!(copies, ArrayCopies::default());
}

/// The natives work as function values too (the machine's `enter`), and
/// still change an unshared array in place.
#[test]
fn natives_as_function_values() {
    let (out, copies) = run(&format!(
        "def main (): {{IO}} () :=\n  \
         let a := [1, 2, 3].foldLeft (Array.empty: Array Nat) Array.push\n  \
         let sizes := [a, a].map Array.size\n  \
         IO.print ({})\n",
        show(&[
            "a.toList",
            "sizes",
            "[1, 2, 3].toArray.getLt 2",
            "a.get 3",
            "(a.set 9 0).toList"
        ])
    ));
    assert_eq!(out, "[1, 2, 3] [3, 3] 3 None [1, 2, 3]");
    assert_eq!(copies.count, 0, "{copies:?}");
}

/// An array kept in a record and changed as the record is rebuilt, as 2020
/// day 15's `Game.say` does (arrays.md §5, item 2): the field's read is the
/// record's last use, so the array is moved out of it and changed in place.
#[test]
fn an_array_in_a_record_is_changed_in_place() {
    let (out, copies) = run("type Game = { turn: Nat, last: Nat, seen: Array Nat }\n\n\
         def Game.say (game: Game) (number: Nat): Game :=\n  \
         { turn = game.turn + 1, last = number, seen = game.seen.set game.last game.turn }\n\n\
         def Game.reply (game: Game): Nat :=\n  \
         let before := game.seen.getOr game.last 0\n  \
         if before == 0 then 0 else game.turn - before\n\n\
         def play: (n: Nat) → (game: Game) → Game\n  \
         | Zero, game => game\n  \
         | Succ k, game => play k (game.say game.reply)\n\n\
         def main (): {IO} () :=\n  \
         let game := play 20000 { turn = 1, last = 0, seen = Array.replicate (count := 20010) 0 }\n  \
         IO.print (Show.toText game.last)\n");
    assert_eq!(out, "7");
    assert_eq!(copies, ArrayCopies::default());
}
