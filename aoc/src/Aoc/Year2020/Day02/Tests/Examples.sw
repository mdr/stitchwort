--| Day 2's tests: the example from the puzzle and unit tests.
--
-- Kept apart from the program, so `stitchwort run Aoc.Year2020.Day02.main`
-- doesn't check them.

namespace Aoc.Year2020.Day02.Tests
import Aoc.Year2020.Day02 (..)
import Std (Fail, List, Result, Text)

def example: Text := """
  1-3 a: abcde
  1-3 b: cdefg
  2-9 c: ccccccccc
  """

def parsed (input: Text): Result (List Entry) Text := Fail.toResult (() => parseEntries input)

def exampleEntries: Result (List Entry) Text := parsed example

def valid (entries: Result (List Entry) Text) (check: Entry → Bool): Result (List Bool) Text := entries.map (.map check)

test "example" := exampleEntries.map (entries => (solvePart1 entries, solvePart2 entries)) == Ok (2, 1)
test "example, part 1, entry by entry" := valid exampleEntries Entry.validByCount == Ok [True, False, True]
test "example, part 2, entry by entry" := valid exampleEntries Entry.validByPosition == Ok [True, False, False]
test "an entry parsed" :=
  parsed "13-14 f: ffffffffnfffvv" == Ok [{ low = 13, high = 14, letter = 'f', password = "ffffffffnfffvv" }]
test "an uppercase letter" := parsed "1-3 A: abc" == Err "line 1, column 5: expected a lowercase letter, got 'A'"
test "a missing password" := parsed "1-3 a: " == Err "line 1, column 8: expected a password, got the end of the line"
test "a space in the password" := parsed "1-3 a: ab c" == Err "line 1, column 10: expected the end of the line, got ' '"

def policy (low high: Nat) (password: Text): Entry := { low, high, letter = 'a', password }

test "part 2 counts from 1" := (policy 1 2 "ab").validByPosition ∧ not (policy 0 1 "ba").validByPosition
test "part 2, both positions hold the letter" := not (policy 1 2 "aa").validByPosition
test "part 2, a position past the end" := (policy 1 5 "ab").validByPosition ∧ not (policy 4 5 "ab").validByPosition
test "part 2, the same position twice" := not (policy 1 1 "a").validByPosition
test "part 1, the bounds are inclusive" := (policy 2 2 "aab").validByCount ∧ not (policy 3 4 "aab").validByCount
