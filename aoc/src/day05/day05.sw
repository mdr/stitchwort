-- Advent of Code 2025, day 5: a list of fresh ingredient id ranges (a-b,
-- both ends included), a blank line, then a list of ingredient ids. Part 1
-- counts the ids inside some range. Part 2 counts the numbers covered by
-- the ranges together, whether or not they appear in the list of ids.
--
--   $ cd aoc && stitchwort run Aoc.Day05.main < inputs/day05.txt
--
-- The puzzle input is not in git (aoc/inputs/ is ignored).
--
-- Part 1 checks every id against every range. Part 2 can't list the numbers
-- (there are about 4 * 10^14), so it merges the ranges instead: sorted by
-- start, a range either overlaps or touches the previous merged range (and
-- extends it) or starts a new one. The merged ranges are disjoint, so their
-- sizes add up.

namespace Aoc.Day05
import Aoc.Common (Range)

def main(): {IO} () :=
  let database := parseDatabase (IO.readAllLines())
  print "Part 1: ${solvePart1 database}"
  print "Part 2: ${solvePart2 database}"

-- The fresh ranges, and the available ids.
type Database = { fresh: List Range, available: List Nat }

-- A line is a range if it reads as one, an id if it reads as a number, and
-- is skipped otherwise (the blank line).
def parseDatabase (lines: List Text): Database :=
  { fresh = lines.mapMaybe Range.parse, available = lines.mapMaybe Text.toNat }

def example: List Text :=
  [ "3-5", "10-14", "16-20", "12-18", "", "1", "5", "8", "11", "17", "32" ]

test "example parse" := (parseDatabase example).available == [1, 5, 8, 11, 17, 32]

-- Part 1: the available ids that are fresh.
def solvePart1 (db: Database): Nat :=
  db.available.count (\id => db.fresh.any (\r => r.contains id))

test "example part 1" := solvePart1 (parseDatabase example) == 3

-- Part 2: every id the fresh ranges cover.
def solvePart2 (db: Database): Nat := merge db.fresh |> .sumBy Range.size

test "example part 2" := solvePart2 (parseDatabase example) == 14
test "no ranges" := solvePart2 { fresh = [], available = [] } == 0

-- Merge ranges that overlap or touch. The list is sorted by start, then
-- folded into a list of merged ranges with the latest first.
def merge (ranges: List Range): List Range :=
  ranges
    |> .sortBy (\a b => Nat.compare a.lo b.lo)
    |> .foldLeft absorb []
    |> .reverse

test "example merged" := merge (parseDatabase example).fresh == [{ lo = 3, hi = 5 }, { lo = 10, hi = 20 }]
test "touching ranges merge" := merge [{ lo = 4, hi = 6 }, { lo = 1, hi = 3 }] == [{ lo = 1, hi = 6 }]
test "nested range" := merge [{ lo = 1, hi = 9 }, { lo = 2, hi = 3 }] == [{ lo = 1, hi = 9 }]
test "gap stays" := merge [{ lo = 1, hi = 2 }, { lo = 4, hi = 5 }] == [{ lo = 1, hi = 2 }, { lo = 4, hi = 5 }]

-- Merging keeps exactly the covered ids, on the example (every id up to 21).
test "merging keeps coverage" :=
  (List.range 22).map (\id => (merge (parseDatabase example).fresh).any (\r => r.contains id))
    == (List.range 22).map (\id => (parseDatabase example).fresh.any (\r => r.contains id))

-- Add a range, starting no earlier than the ones already merged, to them.
def absorb (merged: List Range) (r: Range): List Range :=
  match merged with
    | Nil => [r]
    | Cons last earlier =>
      if r.lo <= last.hi + 1
      then Cons { lo = last.lo, hi = Nat.max last.hi r.hi } earlier
      else Cons r merged
