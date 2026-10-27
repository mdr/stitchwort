-- Advent of Code 2024, day 1: two lists of location ids, side by side. Part 1
-- pairs the smallest of each list, then the second smallest, and so on, and
-- adds up how far apart each pair is. Part 2 adds up each left id times how
-- often it appears in the right list.
--
--   $ cd aoc-2024 && stitchwort run Aoc.Day01.main < inputs/day01.txt
--
-- The proofs are in `Aoc.Day01.Proofs` (Proofs/) and the tests in
-- `Aoc.Day01.Tests` (Tests/); `run` checks neither.

namespace Aoc.Day01
import Std (Fail, IO, List, Map, Nat, Text)
import Std.Fail (fail)

def main(): {IO, Fail} () :=
  let lists := parseLocationLists IO.readAllLines()
  IO.print "Part 1: ${solvePart1 lists}"
  IO.print "Part 2: ${solvePart2 lists}"

-- The two columns of the input.
type LocationLists = { left: List Nat, right: List Nat }

-- One pair of ids per line, separated by spaces: "3   4". Anything else fails,
-- naming the line.
def parseLocationLists (lines: List Text): {Fail} LocationLists :=
  let (left, right) :=
    lines
      |> .mapWithIndex (index line => Fail.context "line ${index + 1}" (() => parseIdPair line))
      |> .unzip
  { left, right }

def parseIdPair (line: Text): {Fail} (Nat, Nat) :=
  match line.words.map Text.toNat with
    | [Some left, Some right] => (left, right)
    | _ => fail "expected two location ids like '3   4', got '${line}'"

-- Part 1: the lists in increasing order, paired up, and the distances added.
def solvePart1 (lists: LocationLists): Nat :=
  lists.left.sort
    |> .zipWith lists.right.sort Nat.absDiff
    |> .sum

-- Part 2: count each id of the right list once, then look each left id up.
def solvePart2 (lists: LocationLists): Nat :=
  let rightCounts := Map.counts lists.right
  lists.left.sumBy (id => id * rightCounts.getOr id 0)
