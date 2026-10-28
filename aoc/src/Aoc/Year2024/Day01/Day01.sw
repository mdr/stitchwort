-- Advent of Code 2024, day 1: two lists of location ids, side by side. Part 1
-- pairs the smallest of each list, then the second smallest, and so on, and
-- adds up how far apart each pair is. Part 2 adds up each left id times how
-- often it appears in the right list.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day01.main < inputs/2024/day01.txt
--
-- The proofs are in `Aoc.Year2024.Day01.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day01.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day01
import Std (Fail, IO, List, Map, Nat, Parse, Text)
import Std.Parse (nat, token)

def main(): {IO, Fail} () :=
  let lists := parseLocationLists IO.readAll()
  IO.print "Part 1: ${solvePart1 lists}"
  IO.print "Part 2: ${solvePart2 lists}"

-- The two columns of the input.
type LocationLists = { left: List Nat, right: List Nat }

-- One pair of ids per line, separated by spaces: "3   4". Anything else fails,
-- naming the line and column.
def parseLocationLists (input: Text): {Fail} LocationLists :=
  let (left, right) := Parse.eachLine input idPair |> .unzip
  { left, right }

-- "3   4" is (3, 4). Two numbers next to each other must have spaces
-- between them, or they would be one number.
def idPair(): {Parse} (Nat, Nat) :=
  let left := token nat
  let right := token nat
  (left, right)

-- Part 1: the lists in increasing order, paired up, and the distances added.
def solvePart1 (lists: LocationLists): Nat :=
  lists.left.sort
    |> .zipWith lists.right.sort Nat.absDiff
    |> .sum

-- Part 2: count each id of the right list once, then look each left id up.
def solvePart2 (lists: LocationLists): Nat :=
  let rightCounts := Map.counts lists.right
  lists.left.sumBy (id => id * rightCounts.getOr id 0)
