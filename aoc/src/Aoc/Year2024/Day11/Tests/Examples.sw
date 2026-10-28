-- Day 11's tests: the examples from the puzzle and unit tests. Kept apart
-- from the program, so `stitchwort run Aoc.Year2024.Day11.main` doesn't
-- check them.

namespace Aoc.Year2024.Day11.Tests
import Aoc.Year2024.Day11 (..)
import Aoc.Year2024.Day11.Spec (blink, blinkTimes, change)
import Std (Fail, List, Map, Nat, Result, Text)

def parsed (input: Text): Result (List Nat) Text := Fail.toResult (() => parseStones input)

def example: List Nat := [125, 17]

test "example, part 1" := solvePart1 example == 55312
test "example, part 2" := solvePart2 example == 65601038650482

-- The longer example's line after each of its six blinks.
test "example, blink by blink" :=
  [1, 2, 3, 4, 5, 6].map (blinks => blinkTimes blinks example) == [
    [253000, 1, 7],
    [253, 0, 2024, 14168],
    [512072, 1, 20, 24, 28676032],
    [512, 72, 2024, 2, 0, 2, 4, 2867, 6032],
    [1036288, 7, 2, 20, 24, 4048, 1, 4048, 8096, 28, 67, 60, 32],
    [2097446912, 14168, 4048, 2, 0, 2, 4, 40, 48, 2024, 40, 48, 80, 96, 2, 8, 6, 7, 6, 0, 3, 2]
  ]

test "example, 22 stones after six blinks" := countAfter 6 example == 22 && (blinkTimes 6 example).length == 22
test "example, the spec's line after 25 blinks" := (blinkTimes 25 example).length == 55312

-- "0 1 10 99 999" after one blink.
test "the five-stone example" := blink [0, 1, 10, 99, 999] == [1, 2024, 1, 0, 9, 9, 2021976]

test "0 becomes 1" := changeStone 0 == [1]
test "an odd number of digits is multiplied by 2024" := changeStone 1 == [2024] && changeStone 999 == [2021976]
test "two digits split" := changeStone 10 == [1, 0] && changeStone 99 == [9, 9]
test "leading zeros are dropped" := changeStone 1000 == [10, 0] && changeStone 100000 == [100, 0] && changeStone 1001 == [10, 1]
test "a long number splits" := changeStone 2097446912 == [20974, 46912]
test "the spec agrees on the edge cases" := [0, 1, 10, 99, 999, 1000, 1001, 100000, 2097446912].all (stone => change stone == changeStone stone)

test "counts merge equal stones" := blinkCounts (Map.counts [0, 0, 10]) |> .toList == [(0, 1), (1, 3)]
test "no blinks" := countAfter 0 [3, 3, 3] == 3
test "no stones" := countAfter 75 [] == 0

test "parse" := parsed "125 17\n" == Ok [125, 17]
test "parse without a final line break" := parsed "0 1 10" == Ok [0, 1, 10]
test "nothing" := parsed "" == Err "line 1, column 1: expected a number, got the end of the input"
test "a bad stone" := parsed "12 x\n" == Err "line 1, column 4: expected a number, got 'x'"
test "two spaces" := parsed "12  3\n" == Ok [12, 3]
