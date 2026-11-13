--| Day 15 proved, about the input text: for every input the parser reads,
--| it is the starting numbers written out (Parse.sw), and the number the
--| program gives for any turn is the one the spec's game speaks on that
--| turn (Turns.sw, with each turn's step in Game.sw). Part 1 is turn 2020
--| and part 2 turn 30000000; the theorem is stated for every turn, not for
--| those two, because the counterexample search on a statement naming turn
--| 30000000 computes the spec's game that far and never finishes
--| (aoc/NOTES-2020.md, day 15).

namespace Aoc.Year2020.Day15.Proofs
import Aoc.Year2020.Day15 (..)
import Aoc.Year2020.Day15 (Spec)
import Std (Fail, List, Result, Text)

theorem correct ∀ (input: Text) (starting: Starting) (parsed: Fail.toResult (() => parseStarting input) = Ok starting) (turn: Nat):
    (∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending ∧ Spec.StartingWritten read starting ∧ ending.all (char => char == '\n' ∨ char == '\r') = True)
      ∧ Spec.Answer starting turn (starting.numberSpoken turn) :=
  Both (parseWritten input starting parsed) (numberSpokenSpec starting turn)
