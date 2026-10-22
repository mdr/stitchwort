-- Day 6's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Day06.main` doesn't check them.

namespace Aoc.Day06.Tests
import Aoc.Day06 (..)
import Std (Char, List, Text)

-- (The lines end in spaces, as in the puzzle.)
def example: List Text := """
  123 328  51 64 
   45 64  387 23 
    6 98  215 314
  *   +   *   +  
  """.lines

test "blank column" := isBlank [' ', ' '] && not (isBlank [' ', '7'])
test "blocks" := blocks ["1 23", "+ *"] == [[['1', '+']], [['2', '*'], ['3', ' ']]]
test "blocks of a short line" := blocks ["12", "+"] == [[['1', '+'], ['2', ' ']]]
test "example problems" :=
  (parseWorksheet example).map (p => (p.rowNumbers, p.columnNumbers))
    == [ ([123, 45, 6], [1, 24, 356]), ([328, 64, 98], [369, 248, 8])
       , ([51, 387, 215], [32, 581, 175]), ([64, 23, 314], [623, 431, 4]) ]
test "example operators" :=
  (parseWorksheet example).map (p => p.operator) == [Some Multiply, Some Add, Some Multiply, Some Add]
test "no operator" := (parseWorksheet ["1", "2", " "]).map (p => p.operator) == [None]
test "read number" := (readNumber [' ', '4', '5'], readNumber ['3', ' ', ' '], readNumber [' ']) == (45, 3, 0)
test "example part 1" := solvePart1 (parseWorksheet example) == 4277556
test "example part 2" := solvePart2 (parseWorksheet example) == 3263827
test "no problems" := (solvePart1 [], solvePart2 []) == (0, 0)

-- The same worksheet with every trailing space removed.
def trimmedExample: List Text := ["123 328  51 64", " 45 64  387 23", "  6 98  215 314", "*   +   *   +"]

test "trimmed example" := (solvePart1 (parseWorksheet trimmedExample), solvePart2 (parseWorksheet trimmedExample)) == (4277556, 3263827)
