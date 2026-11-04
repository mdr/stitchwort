--| Day 11's tests: the puzzle's examples and unit tests.
-- Kept apart from the program, so `stitchwort run Aoc.Year2021.Day11.main`
-- doesn't check them.

namespace Aoc.Year2021.Day11.Tests
import Aoc.Year2021.Day11 (..)
import Aoc.Year2021.Day11.Spec (..)
import Aoc.Common (Position, touching)
import Aoc.Year2021.Day11.Proofs (flashedAfter, flashedCount, flashersCorrect)
import Std (Bool, Fail, List, Text)

def parsed (input: Text): Result (List (List Nat)) Text := Fail.toResult (() => parseLevels input)

def at (row: Nat) (column: Nat): Position := { row, column }

def levelsOf (input: Text): List (List Nat) := Fail.orElse [] (() => parseLevels input)

def small: List (List Nat) := levelsOf "11111\n19991\n19191\n19991\n11111\n"

def example: List (List Nat) :=
  levelsOf "5483143223\n2745854711\n5264556173\n6141336146\n6357385478\n4167524645\n2176841721\n6882881134\n4846848554\n5283751526\n"

test "parse the small example" := small == [[1, 1, 1, 1, 1], [1, 9, 9, 9, 1], [1, 9, 1, 9, 1], [1, 9, 9, 9, 1], [1, 1, 1, 1, 1]]
test "a short row" := parsed "123\n45\n" == Err "line 2: expected 3 cells, as on the first line, got 2"
test "a letter" := parsed "123\n4x6\n" == Err "line 2, column 2: expected a digit or the end of the line, got 'x'"

test "the small example, one step" := step small == levelsOf "34543\n40004\n50005\n40004\n34543\n" ∧ zeros (step small) == 9
test "the small example, two steps" := step (step small) == levelsOf "45654\n51115\n61116\n51115\n45654\n" ∧ zeros (step (step small)) == 0
test "the spec's levels after a step, with the program's flashers" := after small (flashedAt (flashers small)) == step small
test "the example, 10 steps" := flashesIn example 10 == 204
test "example, part 1" := solvePart1 example == 1656
test "example, part 2" := solvePart2 example == Some 195

test "touching" := touching (at 1 1) (at 0 0) ∧ touching (at 1 1) (at 2 1) ∧ not (touching (at 1 1) (at 1 1)) ∧ not (touching (at 1 1) (at 3 1))

--| Two adjacent 8s: each would be above 9 if both flashed, but neither
--| reaches 10 on its own, so nothing flashes.
test "a pair of 8s doesn't start itself" := step [[8, 8]] == [[9, 9]]
test "a 9 sets off its neighbour" := step [[9, 8]] == [[0, 0]] ∧ zeros (step [[9, 8]]) == 2
test "an empty grid" := step [] == ([]: List (List Nat)) ∧ solvePart2 [] == Some 1
test "a ragged grid" := step [[9], [8, 8]] == [[0], [0, 0]]

--| Why the spec's flashers are the least closed set: with two 8s, "both
--| flash" is closed (each would be at 10), but it isn't the flashers.
theorem eightsClosed: Closed [[8, 8]] (q => True) := q level member above => rfl

theorem eightsNotFlashers: ¬(Flashers [[8, 8]] (at => True)) :=
  both => Bool.falseNotTrue (And.right both (flashedAt (flashers [[8, 8]])) (And.left (flashersCorrect [[8, 8]])) (at 0 0) rfl)

--| The hypotheses of `onGridAfter`, `grows` and `stableOfCount` (an
--| octopus has flashed after some rounds; and a round added nobody), which
--| the counterexample search may not meet, can hold.
theorem flashedAfterOneRound: flashedAt (flashedAfter [[9]] 1) (at 0 0) = True := rfl

theorem stableAfterOneRound: flashedCount [[9]] 2 ≤ flashedCount [[9]] 1 ∧ flashedAt (flashedAfter [[9]] 2) (at 0 0) = True := Both (omega [(rfl: flashedCount [[9]] 2 = 1), (rfl: flashedCount [[9]] 1 = 1)]) rfl
