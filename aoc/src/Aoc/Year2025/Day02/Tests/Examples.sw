-- Day 2's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Year2025.Day02.main` doesn't check them.

namespace Aoc.Year2025.Day02.Tests
import Aoc.Common (Range)
import Aoc.Year2025.Day02 (..)
import Aoc.Year2025.Day02.Spec (..)
import Std (Fail, List, Nat, Text)

def example: Text := "11-22,95-115,998-1012,1188511880-1188511890,222220-222224,1698522-1698528,446443-446449,38593856-38593862,565653-565659,824824821-824824827,2121212118-2121212124"

def range (from to: Nat): Range := { from, to }

def parsed (t: Text): Result (List Range) Text := Fail.toResult (() => parseRanges t)

def exampleRanges: List Range := Fail.orElse [] (() => parseRanges example)

test "example" := (solvePart1 exampleRanges, solvePart2 exampleRanges) == (1227775554, 4174379265)
test "part 1 spec" := part1Spec exampleRanges == 1227775554
test "part 2 spec" := part2Spec exampleRanges == 4174379265
test "parse" := parsed "4-14,1490-3407\n" == Ok [range 4 14, range 1490 3407]
test "a field that isn't a range" := parsed "11-22,bad" == Err "line 1, column 7: expected a number, got 'b'"
test "a space after a comma" := parsed "11-22, 33-33" == Ok [range 11 22, range 33 33]
test "spaces around the numbers" := parsed " 11 - 22 \n" == Ok [range 11 22]
test "a missing number" := parsed "11-" == Err "line 1, column 4: expected a number, got the end of the input"
test "a trailing comma" := parsed "11-22," == Err "line 1, column 7: expected a number, got the end of the input"
test "backwards" := parsed "22-11" == Err "line 1, column 6: the range 22-11 ends before it starts"

test "weights" := (List.rangeFrom 11 2).map copiesWeight == [1, 1, 0, 1, -1, 1, 0, 0, -1, 1, 0]

test "single range" := sumOfIdsWrittenTwice (range 11 22) == 33
test "no double counting" := sumOfIdsWrittenRepeatedly (range 111110 111112) == 111111
test "period three" := sumOfIdsWrittenRepeatedly (range 998 1012) == 999 + 1010
test "empty overlap" := sumOfIdsWrittenRepeatedly (range 12 21) == 0

test "12 written 3 times" := RepetitionTemplate.sumIn { blockLength = 2, copies = 3 } { from = 0, to = 1000000 } == 10101 * ((10 + 99) * 90 / 2)
