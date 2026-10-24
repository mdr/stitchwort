-- Day 6's strict reader: the malformed worksheets it rejects (and what it
-- says), and the layouts it must still accept.

namespace Aoc.Day06.Tests
import Aoc.Day06 (..)
import Std (Fail, IO, List, Nat, Pair, Result, Text)

-- The totals of an accepted worksheet, or the reason it was rejected.
def checked (lines: List Text): Result (Nat, Nat) Text :=
  Result.map (problems => (solvePart1 problems, solvePart2 problems)) (checkWorksheet lines)

test "a stray character in a number" := checked ["1x2", "3 4", "+"] == Err "line 1, column 2: expected a digit or a space, got 'x'"
test "a stray character in a later number row" := checked ["12", "3-", "+"] == Err "line 2, column 2: expected a digit or a space, got '-'"
test "two operators under one block" := checked ["12", "34", "+*"] == Err "the problem starting at column 1 has 2 operators, expected one"
test "a block without an operator" := checked ["1 2", "3 4", "+  "] == Err "the problem starting at column 3 has no operator"
test "a block's column is where it starts" :=
  checked ["1  22", "3  44", "+  *+"] == Err "the problem starting at column 4 has 2 operators, expected one"
test "a stray character in the operator row" := checked ["12", "34", "+x"] == Err "line 3, column 2: expected + or * or a space, got 'x'"
test "a digit in the operator row" := checked ["12", "34", "+ 1"] == Err "line 3, column 3: expected + or * or a space, got '1'"
test "a trailing blank line" := checked ["12", "34", "+", ""] == Err "line 4: expected the operator row, got a blank line"
test "a trailing line of spaces" := checked ["12", "34", "+", "  "] == Err "line 4: expected the operator row, got a blank line"
test "only an operator row" := checked ["*"] == Err "expected number rows followed by an operator row, got 1 lines"
test "no lines" := checked [] == Err "expected number rows followed by an operator row, got 0 lines"

-- The layouts that are fine.
test "the example" := checked example == Ok (4277556, 3263827)
test "the trimmed example" := checked trimmedExample == Ok (4277556, 3263827)
test "leading and trailing blank columns" := checked ["  12  ", "  34  ", "  +   "] == Ok (46, 37)
test "several separator columns" := checked ["1    2", "3    4", "+    *"] == Ok (12, 37)
test "a first row shorter than a later row" := checked ["1", "2 3", "+ *"] == Ok (3, 15)
test "an operator row trimmed past a block" := checked ["1", "2 3", "+"] == Err "the problem starting at column 3 has no operator"
test "the worksheet is what the parser reads" := checkWorksheet example == Ok (parseWorksheet example)

-- What `main` prints and how it ends.
def ran (lines: List Text): Pair (List Text) (Result Bool Text) :=
  IO.simulate lines (() => Result.map (u => True) (Fail.toResult main))

test "main on a malformed worksheet" := ran ["1x2", "+"] == MkPair [] (Err "line 1, column 2: expected a digit or a space, got 'x'")
test "main on a worksheet" := ran ["12", "3", "+"] == MkPair ["Part 1: 15", "Part 2: 15"] (Ok True)
