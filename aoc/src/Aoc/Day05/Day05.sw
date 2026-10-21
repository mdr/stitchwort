-- Advent of Code 2025, day 5: a list of fresh ingredient id ranges (a-b,
-- both ends included), a blank line, then a list of ingredient ids. Part 1
-- counts the ids inside some range. Part 2 counts the numbers covered by
-- the ranges together, whether or not they appear in the list of ids.
--
--   $ cd aoc && stitchwort run Aoc.Day05.main < inputs/day05.txt
--
-- The puzzle input is committed in aoc/inputs/ (D119).
--
-- Part 1 checks every id against every range. Part 2 can't list the numbers
-- (there are about 4 * 10^14), so it merges the ranges instead: sorted by
-- start, a range either overlaps or touches the previous merged range (and
-- extends it) or starts a new one. The merged ranges are disjoint, so their
-- sizes add up. `Aoc.Day05.Proofs.solvePart2Correct` (Proofs/Part2.sw) proves
-- that, for every database: part 2 is the brute-force count of the ids some
-- range holds. `run` does not check it.

namespace Aoc.Day05
import Aoc.Common (Range)

def main(): {IO} () :=
  let database := parseDatabase (IO.readAllLines())
  IO.print "Part 1: ${solvePart1 database}"
  IO.print "Part 2: ${solvePart2 database}"

-- The fresh ranges, and the available ids.
type Database = { fresh: List Range, available: List Nat }

-- A line is a range if it reads as one, an id if it reads as a number, and
-- is skipped otherwise (the blank line).
def parseDatabase (lines: List Text): Database :=
  { fresh = lines.filterMap Range.parse, available = lines.filterMap Text.toNat }

def example: List Text :=
  [ "3-5", "10-14", "16-20", "12-18", "", "1", "5", "8", "11", "17", "32" ]

test "example parse" := (parseDatabase example).available == [1, 5, 8, 11, 17, 32]

-- Part 1: the available ids that are fresh.
def solvePart1 (db: Database): Nat :=
  db.available.count (id => db.fresh.any (r => r.contains id))

test "example part 1" := solvePart1 (parseDatabase example) == 3

-- Part 2: every id the fresh ranges cover.
def solvePart2 (db: Database): Nat := merge db.fresh |> .sumBy Range.size

test "example part 2" := solvePart2 (parseDatabase example) == 14
test "no ranges" := solvePart2 { fresh = [], available = [] } == 0

-- Merge ranges that overlap or touch. The list is sorted by start, then
-- folded into a list of merged ranges with the latest first.
def merge (ranges: List Range): List Range :=
  ranges
    |> .sortBy (a b => Nat.compare a.from b.from)
    |> .foldLeft absorb []
    |> .reverse

test "example merged" := merge (parseDatabase example).fresh == [{ from = 3, to = 5 }, { from = 10, to = 20 }]
test "touching ranges merge" := merge [{ from = 4, to = 6 }, { from = 1, to = 3 }] == [{ from = 1, to = 6 }]
test "nested range" := merge [{ from = 1, to = 9 }, { from = 2, to = 3 }] == [{ from = 1, to = 9 }]
test "gap stays" := merge [{ from = 1, to = 2 }, { from = 4, to = 5 }] == [{ from = 1, to = 2 }, { from = 4, to = 5 }]

-- Add a range, starting no earlier than the ones already merged, to them.
def absorb (merged: List Range) (r: Range): List Range :=
  match merged with
    | Nil => [r]
    | Cons last earlier =>
      if r.from <= last.to + 1
      then Cons { from = last.from, to = Nat.max last.to r.to } earlier
      else Cons r merged
