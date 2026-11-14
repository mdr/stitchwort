--| Day 3's tests: the example from the puzzle and unit tests.
-- Kept apart from the program, so `stitchwort run Aoc.Year2021.Day03.main`
-- doesn't check them.

namespace Aoc.Year2021.Day03.Tests
import Aoc.Common (Bits)
import Aoc.Year2021.Day03 (..)
import Aoc.Year2021.Day03.Spec (..)
import Std (Fail, List, Text)

def example: Text := """
  00100
  11110
  10110
  10111
  10101
  01111
  00111
  11100
  10000
  11001
  00010
  01010
  """

def exampleReport: List Bits := Fail.orElse [] (() => parseReport example)

--| A report of numbers written as lists of bits.
def report (rows: List (List Bool)): List Bits := rows.map (bits => { bits })

def parsed (input: Text): Result (List Bits) Text := Fail.toResult (() => parseReport input)

test "parse the example" :=
  exampleReport.length == 12 ∧ exampleReport.headOr Bits.empty == { bits = [False, False, True, False, False] }
test "example, part 1" := solvePart1 exampleReport == 198
test "example, part 2" := solvePart2 exampleReport == Some 230
test "example, the rates" := (gammaRate exampleReport, epsilonRate exampleReport) == (22, 9)
test "example, the ratings" :=
  (oxygenGeneratorRating exampleReport, co2ScrubberRating exampleReport) == (Some 23, Some 10)
test "example, as the puzzle states it" :=
  (powerConsumption exampleReport, lifeSupportRating exampleReport) == (198, Some 230)

test "not a bit" := parsed "0101\n0121" == Err "line 2, column 3: expected 0 or 1 or the end of the line, got '2'"
test "an empty line" := parsed "01\n\n10" == Err "line 2, column 1: expected 0 or 1, got the end of the line"
test "a number with too few bits" := parsed "0101\n011\n1100" == Err "line 2: 3 bits, but the first line has 4"
test "no lines" := parsed "" == Ok []

--| Ties: the most common bit is 1, the least common 0.
test "a tie, part 1" :=
  (gammaRate (report [[True], [False]]), epsilonRate (report [[True], [False]]), solvePart1 (report [[True], [False]]))
    == (1, 0, 0)
test "a tie keeps 1s for oxygen and 0s for CO2" :=
  (
    oxygenGeneratorRating (report [[False, True], [True, False]]),
    co2ScrubberRating (report [[False, True], [True, False]])
  )
    == (Some 2, Some 1)

--| Every number left has a 1 there: the least common bit is 0, and no number
--| is kept, so there is no CO2 scrubber rating.
test "no number left" :=
  (co2ScrubberRating (report [[True, False], [True, True]]), solvePart2 (report [[True, False], [True, True]]))
    == (None, None)
--| The same number twice: no bit tells them apart, so more than one is left.
test "the same number twice" :=
  (oxygenGeneratorRating (report [[True], [True]]), solvePart2 (report [[True], [True]])) == (None, None)
--| One number is its own rating, with no filtering at all.
test "one number" := solvePart2 (report [[True, True, False]]) == Some 36
test "no numbers" := (solvePart1 [], solvePart2 [], lifeSupportRating []) == (0, None, None)

--| The examples, proved by computing them.
theorem examplePart1: solvePart1 exampleReport = 198 := rfl
theorem examplePart2: solvePart2 exampleReport = Some 230 := rfl
