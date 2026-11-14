--| Day 7's tests: the example from the puzzle and unit tests.
-- Kept apart from the program, so `stitchwort run Aoc.Year2021.Day07.main`
-- doesn't check them.

namespace Aoc.Year2021.Day07.Tests
import Aoc.Year2021.Day07 (..)
import Aoc.Year2021.Day07.Spec (..)
import Std (Fail, List, Text)

def example: Text := "16,1,2,0,4,2,7,1,2,14\n"

def exampleCrabs: List Nat := [16, 1, 2, 0, 4, 2, 7, 1, 2, 14]

def parsed (input: Text): Result (List Nat) Text := Fail.toResult (() => parseCrabs input)

test "parse the example" := parsed example == Ok exampleCrabs
test "example, part 1" := solvePart1 exampleCrabs == 37
test "example, part 2" := solvePart2 exampleCrabs == 168

--| The puzzle's worked positions: part 1 is cheapest at 2 (1, 3 and 10 cost
--| 41, 39 and 71), part 2 at 5 (2 costs 206).
test "example, part 1's positions" :=
  (
    totalFuel part1Fuel exampleCrabs 2,
    totalFuel part1Fuel exampleCrabs 1,
    totalFuel part1Fuel exampleCrabs 3,
    totalFuel part1Fuel exampleCrabs 10
  )
    == (37, 41, 39, 71)
test "example, part 2's positions" :=
  (totalFuel part2Fuel exampleCrabs 5, totalFuel part2Fuel exampleCrabs 2) == (168, 206)
test "the example's ends" := (leftmost exampleCrabs, rightmost exampleCrabs) == (0, 16)

test "the spec's distance either way" := (distance 16 5, distance 1 5, distance 5 5) == (11, 4, 0)
test "part 2's fuel is 1 + 2 + … + n" := (List.range 0 30).all (n => growingFuel n == part2Fuel n)
test "16 to 5 costs 66 in part 2" := part2Fuel 11 == 66

test "no crabs need no fuel" := (solvePart1 [], solvePart2 []) == (0, 0)
test "one crab doesn't move" := (solvePart1 [7], solvePart2 [7]) == (0, 0)
test "two crabs meet anywhere between" := solvePart1 [3, 9] == 6
test "part 2 meets in the middle" := solvePart2 [0, 10] == 30

test "a space after a comma" := parsed "1, 2" == Err "line 1, column 3: expected a number, got ' '"
test "a missing number" := parsed "1,,2" == Err "line 1, column 3: expected a number, got ','"
test "nothing" := parsed "" == Err "line 1, column 1: expected a number, got the end of the input"

--| The examples, proved by computing them.
theorem examplePart1: solvePart1 exampleCrabs = 37 := rfl
theorem examplePart2: solvePart2 exampleCrabs = 168 := rfl
