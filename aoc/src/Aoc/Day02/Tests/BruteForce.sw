-- Day 2's cross-check against brute force: both parts compared with the obvious
-- method on many small ranges, looking at every id's digits. (Both are also
-- proved, in `Aoc.Day02.Proofs`: part 1 in Proofs/Part1.sw, part 2 in
-- Proofs/Part2.sw.) Kept apart from the program, so
-- `stitchwort run Aoc.Day02.main` doesn't check it.

namespace Aoc.Day02.Tests
import Aoc.Common (Range)
import Aoc.Day02 (..)
import Std (Bool, List, Nat)

test "written as" := (writtenAs [1, 2, 1, 2] 2 2, writtenAs [1, 2, 1, 2] 1 4, writtenAs [1, 1, 1] 1 3) == (True, False, True)

def bruteSum (invalid: Nat -> Bool) (r: Range): Nat :=
  r.ids |> .filter invalid |> .sum

def agrees (r: Range): Bool :=
  sumOfInvalidIdsInRange r == bruteSum doubled r && sumRepeated r == (bruteSum repeats r).toInt

-- Ranges of 40 ids starting every 13 up to 2000, and some that cross into
-- more digits.
def checkRanges: List Range :=
  (List.rangeFrom 154 0 |> .map (i => range (13 * i) (13 * i + 39)))
    ++ [range 95 115, range 990 1010, range 9990 10010, range 99990 100010, range 111100 111200, range 999990 1000010]

test "brute force agrees" := checkRanges.all agrees

-- Ids of 11 to 20 digits, around 1 written 11, 12 and 13 times, 12 written 6
-- times, 1234 written 3 times, 17 ones, 10 written 10 times, and across into
-- 12 digits: part 2 against walking the ids.
def longRanges: List Range :=
  [range 11111111100 11111111120, range 111111111101 111111111121, range 1111111111100 1111111111120,
   range 121212121202 121212121222, range 123412341224 123412341244, range 99999999989 100000000009,
   range 11111111111111101 11111111111111121, range 10101010101010101000 10101010101010101020]

test "long ids" := longRanges.all (r => sumRepeated r == (bruteSum repeats r).toInt)
test "long ids found" := List.map sumRepeated longRanges == [11111111111, 111111111111, 1111111111111, 121212121212, 123412341234, 99999999999, 11111111111111111, 10101010101010101010]
