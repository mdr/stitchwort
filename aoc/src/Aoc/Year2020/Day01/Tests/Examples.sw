--| Day 1's tests: the example from the puzzle and unit tests.
--
-- Kept apart from the program, so `stitchwort run Aoc.Year2020.Day01.main`
-- doesn't check them.

namespace Aoc.Year2020.Day01.Tests
import Aoc.Year2020.Day01 (..)
import Std (Fail, List, Option, Result, Text)

def example: Text := """
  1721
  979
  366
  299
  675
  1456
  """

def parsed (input: Text): Result (List Nat) Text := Fail.toResult (() => parseEntries input)

def exampleEntries: Result (List Nat) Text := parsed example

test "example" :=
  exampleEntries.map (entries => (solvePart1 entries, solvePart2 entries)) == Ok (Some 514579, Some 241861950)
test "example, the entries found" :=
  exampleEntries.map (entries => (findPair 2020 entries, findTriple 2020 entries))
    == Ok (Some (1721, 299), Some (979, 366, 675))
test "a line that isn't a number" := parsed "1721\nabc" == Err "line 2, column 1: expected a number, got 'a'"
test "spaces around an entry" := parsed " 1721 \n299\n" == Ok [1721, 299]

test "one entry isn't a pair, even half of 2020" := findPair 2020 [1010] == None
test "two equal entries are a pair" := findPair 2020 [1010, 5, 1010] == Some (1010, 1010)
test "an entry over 2020 has no partner" := findPair 2020 [3000, 0] == None
test "no pair" := findPair 2020 [1, 2, 3] == None
test "three entries, and two aren't three" :=
  findTriple 2020 [1000, 20, 1000] == Some (1000, 20, 1000) ∧ findTriple 2020 [1000, 20] == None
