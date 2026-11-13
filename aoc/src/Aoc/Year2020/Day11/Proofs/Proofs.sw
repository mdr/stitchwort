--| Day 11 proved, about the input text: for every input the parser reads,
--| its lines are the layout's rows written out (Parse.sw); a round of the
--| program is the spec's round for each part (Rounds.sw, Sight.sw,
--| Plan.sw); so each answer is the occupied seats of the layout the spec's
--| rounds settle on (Settle.sw, Parts.sw), and there is one such answer.
--| Nothing bounds the rounds: each part answers exactly when the spec's
--| rounds settle within `roundLimit` rounds.

namespace Aoc.Year2020.Day11.Proofs
import Aoc.Year2020.Day11 (..)
import Aoc.Year2020.Day11 (Spec)
import Std (Fail, List, Result, Text)

theorem part1Correct ∀ (input: Text) (layout: Layout) (parsed: Fail.toResult (() => parseLayout input) = Ok layout) (answer: Nat)
    (solved: layout.settledOccupied adjacentRule = Some answer):
    List.All2 Spec.RowWritten (input.lines.map Text.toList) layout.grid.rows ∧ Spec.Part1 layout answer :=
  Both (And.left (parseWritten input layout parsed)) (part1Rules layout answer solved)

theorem part2Correct ∀ (input: Text) (layout: Layout) (parsed: Fail.toResult (() => parseLayout input) = Ok layout) (answer: Nat)
    (solved: layout.settledOccupied layout.sightRule = Some answer):
    List.All2 Spec.RowWritten (input.lines.map Text.toList) layout.grid.rows ∧ Spec.Part2 layout answer :=
  Both (And.left (parseWritten input layout parsed)) (part2Rules layout answer solved)
