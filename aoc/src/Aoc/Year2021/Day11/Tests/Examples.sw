--| Day 11's tests: the puzzle's examples and unit tests.
-- Kept apart from the program, so `stitchwort run Aoc.Year2021.Day11.main`
-- doesn't check them.

namespace Aoc.Year2021.Day11.Tests
import Aoc.Year2021.Day11 (..)
import Aoc.Year2021.Day11.Spec (..)
import Aoc.Common (Grid, Position, firstWidth, touching)
import Aoc.Year2021.Day11.Proofs (flashedAfter, flashedCount, flashersCorrect)
import Std (Bool, Fail, List, Text)

def parsed (input: Text): Result Cavern Text := Fail.toResult (() => parseCavern input)

def at (row column: Nat): Position := { row, column }

--| A cavern of these levels, row by row; the first row has an octopus.
def levelsOf (rows: List (List Nat)) [auto nonEmpty: (firstWidth rows == 0) = False]: Cavern := { grid = Grid.of rows }

def cavernOf (input: Text): Cavern := Fail.orElse (levelsOf [[0]]) (() => parseCavern input)

def small: Cavern := cavernOf """
  11111
  19991
  19191
  19991
  11111
  """

def example: Cavern := cavernOf """
  5483143223
  2745854711
  5264556173
  6141336146
  6357385478
  4167524645
  2176841721
  6882881134
  4846848554
  5283751526
  """

test "parse the small example" :=
  small.grid.rows == [[1, 1, 1, 1, 1], [1, 9, 9, 9, 1], [1, 9, 1, 9, 1], [1, 9, 9, 9, 1], [1, 1, 1, 1, 1]]
test "a short row" := parsed "123\n45\n" == Err "line 2: expected 3 cells, as on the first line, got 2"
test "a letter" := parsed "123\n4x6\n" == Err "line 2, column 2: expected a digit or the end of the line, got 'x'"

test "the small example, one step" := small.step == cavernOf """
  34543
  40004
  50005
  40004
  34543
  """ ∧ small.step.zeros == 9
test "the small example, two steps" := small.step.step == cavernOf """
  45654
  51115
  61116
  51115
  45654
  """ ∧ small.step.step.zeros == 0
test "the spec's cavern after a step, with the program's flashers" := after small small.flashers.has == small.step
test "the example, 10 steps" := example.flashesIn 10 == 204
test "example, part 1" := example.solvePart1 == 1656
test "example, part 2" := example.solvePart2 == Some 195

test "touching" :=
  touching (at 1 1) (at 0 0)
    ∧ touching (at 1 1) (at 2 1)
    ∧ not (touching (at 1 1) (at 1 1))
    ∧ not (touching (at 1 1) (at 3 1))

--| Two adjacent 8s: each would be above 9 if both flashed, but neither
--| reaches 10 on its own, so nothing flashes.
test "a pair of 8s doesn't start itself" := (levelsOf [[8, 8]]).step == levelsOf [[9, 9]]
test "a 9 sets off its neighbour" := (levelsOf [[9, 8]]).step == levelsOf [[0, 0]] ∧ (levelsOf [[9, 8]]).step.zeros == 2
test "a ragged cavern" := (levelsOf [[9], [8, 8]]).step == levelsOf [[0], [0, 0]]

--| Why the spec's flashers are the least closed set: with two 8s, "both
--| flash" is closed (each would be at 10), but it isn't the flashers.
theorem eightsClosed: Closed (levelsOf [[8, 8]]) (q => True) := q level member above => rfl

theorem eightsNotFlashers: ¬(Flashers (levelsOf [[8, 8]]) (at => True)) := both =>
  Bool.falseNotTrue
    (And.right both (levelsOf [[8, 8]]).flashers.has (And.left (flashersCorrect (levelsOf [[8, 8]]))) (at 0 0) rfl)

--| The hypotheses of `onGridAfter`, `grows` and `stableOfCount` (an
--| octopus has flashed after some rounds; and a round added nobody), which
--| the counterexample search may not meet, can hold.
theorem flashedAfterOneRound: (flashedAfter (levelsOf [[9]]) 1).has (at 0 0) = True := rfl

theorem stableAfterOneRound: flashedCount (levelsOf [[9]]) 2 ≤ flashedCount (levelsOf [[9]]) 1
      ∧ (flashedAfter (levelsOf [[9]]) 2).has (at 0 0) = True :=
  Both (omega [(rfl: flashedCount (levelsOf [[9]]) 2 = 1), (rfl: flashedCount (levelsOf [[9]]) 1 = 1)]) rfl
