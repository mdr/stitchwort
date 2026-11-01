--| Day 9's tests: the examples from the puzzle and unit tests.
--
-- Kept apart from the program, so `stitchwort run Aoc.Year2024.Day09.main`
-- doesn't check them.

namespace Aoc.Year2024.Day09.Tests
import Aoc.Year2024.Day09 (..)
import Aoc.Year2024.Day09.Spec (compactOneAtATime, compactWholeFiles, filesystemChecksum, hasGap, moveLastBlock, moveWholeFile, part1, part2)
import Std (Fail, List, Nat, Option, Result, Text)

def example: Text := "2333133121414131402"

def parsed (input: Text): Result (List Nat) Text := Fail.toResult (() => parseDiskMap input)

--| A function of the parsed disk map, or why it didn't parse: a parse failure fails the test.
def onDisk (input: Text) (f: List Nat -> a): Result a Text := parsed input |> .map f

--| The blocks as the puzzle draws them: a file block as its file's number,
--| free space as `.`.
def picture (blocks: List (Option Nat)): Text :=
  Text.joinWith (blocks.map (block => block.map (id => "${id}") |> .getOrElse ".")) ""

--| The pictures after each of part 1's moves, until there are no gaps.
def movePictures (blocks: List (Option Nat)): List Text :=
  List.range (blocks.length + 1) |> .map (moves => picture (compactOneAtATime moves blocks)) |> .dedup

--| Both parts agree with the spec.
def agrees (input: Text): Result Bool Text :=
  onDisk input (diskMap => solvePart1 diskMap == part1 diskMap && solvePart2 diskMap == part2 diskMap)

test "example, part 1" := onDisk example solvePart1 == Ok 1928
test "example, part 2" := onDisk example solvePart2 == Ok 2858
test "example, the blocks" := onDisk example (diskMap => picture (blocks diskMap)) == Ok "00...111...2...333.44.5555.6666.777.888899"
test "small example, the blocks" := onDisk "12345" (diskMap => picture (blocks diskMap)) == Ok "0..111....22222"
test "90909, the blocks" := onDisk "90909" (diskMap => picture (blocks diskMap)) == Ok "000000000111111111222222222"

test "small example, part 1's moves" :=
  onDisk "12345" (diskMap => movePictures (blocks diskMap)) == Ok ["0..111....22222", "02.111....2222.", "022111....222..", "0221112...22...", "02211122..2....", "022111222......"]

test "example, part 1's last move" :=
  onDisk example (diskMap => picture (compactBlocks (blocks diskMap))) == Ok "0099811188827773336446555566.............."

test "example, part 2's moves" :=
  onDisk example (diskMap => [9, 8, 7, 6, 5, 4, 3, 2, 1, 0].scanLeft (blocks diskMap) moveWholeFile |> .map picture |> .dedup) == Ok [
    "00...111...2...333.44.5555.6666.777.888899",
    "0099.111...2...333.44.5555.6666.777.8888..",
    "0099.1117772...333.44.5555.6666.....8888..",
    "0099.111777244.333....5555.6666.....8888..",
    "00992111777.44.333....5555.6666.....8888.."
  ]

test "example, the checksum" := onDisk example (diskMap => filesystemChecksum (compactBlocks (blocks diskMap))) == Ok 1928
test "small example" := onDisk "12345" (diskMap => (solvePart1 diskMap, solvePart2 diskMap)) == Ok (60, 132)
test "example, the spec agrees" := (agrees example, agrees "12345") == (Ok True, Ok True)

test "parse" := parsed "12345\n" == Ok [1, 2, 3, 4, 5]
test "parse without a final line break" := parsed "2333" == Ok [2, 3, 3, 3]
test "nothing" := parsed "" == Err "line 1, column 1: expected a digit, got the end of the input"
test "a bad character" := parsed "12x3" == Err "line 1, column 3: expected a digit or the end of the line, got 'x'"
test "two lines" := parsed "12\n34\n" == Err "line 2, column 1: expected the end of the input, got '3'"

test "one file" := (onDisk "3" (diskMap => (picture (compactBlocks (blocks diskMap)), solvePart1 diskMap)), agrees "3") == (Ok ("000", 0), Ok True)
test "no free space" := (onDisk "90909" (diskMap => solvePart1 diskMap == solvePart2 diskMap), agrees "90909") == (Ok True, Ok True)
test "free space at the end" := (onDisk "1919" (diskMap => picture (compactBlocks (blocks diskMap))), agrees "1919") == (Ok "01..................", Ok True)
test "a file that fits exactly" := picture (compactWholeFiles [1, 2, 1, 1, 2] (blocks [1, 2, 1, 1, 2])) == "0221..."
test "a file too big for any span stays" := picture (compactWholeFiles [1, 1, 3] (blocks [1, 1, 3])) == "0.111" && agrees "113" == Ok True
test "a file only moves left" := picture (compactWholeFiles [2, 0, 1, 3, 1] (blocks [2, 0, 1, 3, 1])) == "0012..." && agrees "20131" == Ok True
test "free space after a file isn't used" := agrees "21212" == Ok True
test "a file of length 0" := (agrees "101", agrees "11023") == (Ok True, Ok True)
test "free spans either side of a file of length 0 join" :=
  picture (compactWholeFiles [1, 1, 0, 2, 3] (blocks [1, 1, 0, 2, 3])) == "0222..." && onDisk "11023" solvePart2 == Ok 12
test "more examples agree with the spec" :=
  ["2333133121414131402", "1010101010101010101", "9999999", "123456789", "987654321", "11111111111", "31415926535"].all (input => agrees input == Ok True)

test "the checksum skips free space" := checksum [Some 1, None, Some 2] == 0 * 1 + 2 * 2
