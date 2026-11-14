--| Day 9's puzzle example (a preamble of 5), the window check's edge cases,
--| and the sliding run's.

namespace Aoc.Year2020.Day09.Tests
import Aoc.Year2020.Day09 (..)
import Std (Fail, List, Option, Result, Text)

def parsed (input: Text): Result XmasData Text := Fail.toResult (() => parseData input)

def part1 (input: Text) (preamble: Nat): Result (Option Nat) Text :=
  (parsed input).map (data => data.firstInvalid preamble)

def part2 (input: Text) (preamble: Nat): Result (Option Nat) Text :=
  (parsed input).map (data => data.firstInvalid preamble |> .flatMap data.weakness)

def window (numbers: List Nat): Window := { numbers }

def example: Text := """
  35
  20
  15
  25
  47
  40
  62
  55
  65
  95
  102
  117
  150
  182
  127
  219
  299
  277
  309
  576
  """

test "example, the numbers" := (parsed example).map (data => data.numbers.take 3) == Ok [35, 20, 15]
test "example, part 1" := part1 example (preamble := 5) == Ok (Some 127)
test "example, the run" := (parsed example).map (data => data.runSumming 127) == Ok (Some [15, 25, 47, 40])
test "example, part 2" := part2 example (preamble := 5) == Ok (Some 62)

-- The puzzle's own cases, with the numbers 1 to 25 before.
test "26 is 1 plus 25" := (window (1 ..= 25)).sumsTo 26
test "49 is 24 plus 25" := (window (1 ..= 25)).sumsTo 49
test "100 is no sum of two" := not ((window (1 ..= 25)).sumsTo 100)
test "50 would need 25 twice" := not ((window (1 ..= 25)).sumsTo 50)
test "a number and 0 sum to it" := (window [0, 7]).sumsTo 7
test "two equal numbers still don't count" := not ((window [4, 4]).sumsTo 8)
test "every number valid" := part1 "1\n2\n3\n5" (preamble := 2) == Ok None
test "the preamble itself is never checked" := part1 "1\n100\n101" (preamble := 2) == Ok None

test "a run needs two numbers, not the target alone" :=
  ({ numbers = [3, 9, 4, 5] }: XmasData).runSumming 9 == Some [4, 5]
test "a run at the very start" := ({ numbers = [2, 7, 1] }: XmasData).runSumming 9 == Some [2, 7]
test "a run at the very end" := ({ numbers = [5, 1, 2] }: XmasData).runSumming 3 == Some [1, 2]
test "no run" := ({ numbers = [5, 1, 2] }: XmasData).runSumming 4 == None
test "zeros in a run" := ({ numbers = [9, 0, 0, 3] }: XmasData).runSumming 3 == Some [0, 0, 3]
test "the weakness is the run's smallest plus largest" :=
  ({ numbers = [8, 1, 5, 3, 2] }: XmasData).weakness 11 == Some 6

test "not a number" := parsed "12\nx" == Err "line 2, column 1: expected a number, got 'x'"
