--| Day 5's puzzle examples, and the parser's errors.

namespace Aoc.Year2020.Day05.Tests
import Aoc.Year2020.Day05 (..)
import Std (Fail, List, Option, Result, Text)

def parsed (input: Text): Result (List Pass) Text := Fail.toResult (() => parsePasses input)

def ids (input: Text): Result (List Nat) Text := (parsed input).map (passes => passes.map .seatId)

test "example" := ids "FBFBBFFRLR" == Ok [357]
test "the other examples" := ids """
  BFFFBBFRRR
  FFFBBBFRRR
  BBFFBBFRLL""" == Ok [567, 119, 820]
test "example, part 1" := (parsed """
  BFFFBBFRRR
  FFFBBBFRRR
  BBFFBBFRLL""").map solvePart1 == Ok (Some 820)
test "the first and last seats" := ids """
  FFFFFFFLLL
  BBBBBBBRRR""" == Ok [0, 1023]

test "the gap between two passes" := gap [3, 5] == Some 4 ∧ gap [1, 2, 3] == None ∧ gap [1, 1, 3, 3] == Some 2
test "part 2 sorts first" := (parsed """
  FFFFFFFRRR
  FFFFFFBLLR
  FFFFFFFRRL""").map solvePart2 == Ok (Some 8)
test "no passes" := (parsed "").map (passes => (solvePart1 passes, solvePart2 passes)) == Ok (None, None)

test "a row letter among the columns" := parsed "FBFBBFFRLB" == Err "line 1, column 10: expected 'L' or 'R', got 'B'"
test "a short pass" := parsed "FBFBBFFRL" == Err "line 1, column 10: expected 'L' or 'R', got the end of the line"
test "a long pass" := parsed "FBFBBFFRLRL" == Err "line 1, column 11: expected the end of the line, got 'L'"
