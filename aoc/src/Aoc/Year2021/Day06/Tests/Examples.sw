-- Day 6's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Year2021.Day06.main` doesn't check them.

namespace Aoc.Year2021.Day06.Tests
import Aoc.Year2021.Day06 (..)
import Aoc.Year2021.Day06.Spec (..)
import Std (Fail, List, Text)

def exampleTimers: List Nat := [3, 4, 3, 1, 2]

def parsed (input: Text): Result (List Nat) Text := Fail.toResult (() => parseTimers input)

test "parse the example" := parsed "3,4,3,1,2\n" == Ok exampleTimers
test "a timer above 8" := parsed "3,9,1" == Err "timer 2 is above 8"
test "a space after a comma" := parsed "3, 4" == Err "column 3: expected a number, got ' '"
test "no timers" := parsed "" == Err "column 1: expected a number, got the end of the line"

test "the example's first days, fish by fish" :=
  afterDays 1 exampleTimers == [2, 3, 2, 0, 1] ∧ afterDays 2 exampleTimers == [1, 2, 1, 6, 0, 8]
test "the example after 18 days, fish by fish" :=
  afterDays 18 exampleTimers == [6, 0, 6, 4, 5, 6, 0, 1, 1, 2, 6, 0, 1, 1, 1, 2, 2, 3, 3, 4, 6, 7, 8, 8, 8, 8]
test "the example after 18 days" := fishAfter 18 exampleTimers == 26 ∧ fishCount 18 exampleTimers == 26
test "the example after 80 days, both ways" := solvePart1 exampleTimers == 5934 ∧ fishCount 80 exampleTimers == 5934
test "example, part 2" := solvePart2 exampleTimers == 26984457539

test "a fish at 0 spawns on the first day" := fishAfter 1 [0] == 2 ∧ fishAfter 7 [0] == 2 ∧ fishAfter 8 [0] == 3
test "a new fish spawns on its ninth day" := fishAfter 8 [8] == 1 ∧ fishAfter 9 [8] == 2
test "no fish" := fishAfter 256 [] == 0
test "the counts after a day" :=
  (Counts.ofTimers [0, 0, 7, 8]).nextDay.total == 6 ∧ (Counts.ofTimers [0, 0, 7, 8]).nextDay.t6 == 3

-- The examples, proved by computing them.
theorem exampleAfter18: fishAfter 18 exampleTimers = 26 := rfl
theorem examplePart1: solvePart1 exampleTimers = 5934 := rfl
