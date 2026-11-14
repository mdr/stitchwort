--| Day 10's two puzzle examples, and edge cases of the chain and the count.

namespace Aoc.Year2020.Day10.Tests
import Aoc.Year2020.Day10 (..)
import Aoc.Year2020.Day10 (Spec)
import Std (Fail, List, Option, Result, Text)

def parsed (input: Text): Result Bag Text := Fail.toResult (() => parseBag input)

def part1 (input: Text): Result (Option Nat) Text := (parsed input).map (.distribution)

def part2 (input: Text): Result (Option Nat) Text := (parsed input).map (.arrangements)

def bag (adapters: List Nat): Bag := { adapters }

def example: Text := """
  16
  10
  15
  5
  1
  11
  7
  19
  6
  12
  4
  """

def largerExample: Text := """
  28
  33
  18
  42
  31
  14
  46
  20
  48
  47
  24
  23
  49
  45
  19
  38
  39
  11
  1
  32
  25
  35
  8
  17
  7
  9
  4
  2
  34
  10
  3
  """

test "example, the adapters" := (parsed example).map (b => b.adapters.take 3) == Ok [16, 10, 15]
test "example, the device" := (parsed example).map (.device) == Ok (Some 22)
test "example, part 1" := part1 example == Ok (Some 35)
test "example, part 2" := part2 example == Ok (Some 8)
test "larger example, part 1" := part1 largerExample == Ok (Some 220)
test "larger example, part 2" := part2 largerExample == Ok (Some 19208)

test "an empty bag has no device" :=
  (bag []).device == None && (bag []).distribution == None && (bag []).arrangements == None
test "one adapter, 3 jolts up" := (bag [3]).distribution == Some 0 && (bag [3]).arrangements == Some 1
test "one adapter, 1 jolt up" := (bag [1]).distribution == Some 1 && (bag [1]).arrangements == Some 1
test "a gap of 4 breaks the chain" := (bag [1, 5]).distribution == None && (bag [1, 5]).arrangements == Some 0
test "listed out of order" := (bag [3, 1, 2]).distribution == (bag [1, 2, 3]).distribution
test "three adapters 1 apart: skip any but the last" := (bag [1, 2, 3]).arrangements == Some 4
test "the outlet can feed an adapter 3 up" := (bag [1, 3]).arrangements == Some 2
test "differences of 2 count toward neither" := (bag [2, 4]).distribution == Some 0

-- The program's count against the spec's, which lists every subsequence.
def specCount (adapters: List Nat): Option Nat :=
  (bag adapters).device |> .map (device => (Spec.subsequences adapters.sort).count (kept => Spec.Connects kept device))

test "the count agrees with the spec's on the example" :=
  (parsed example).map (b => b.arrangements == specCount b.adapters) == Ok True
test "the count agrees with the spec's, small bags" :=
  [[1, 2, 3, 4, 5, 6, 7], [2, 3, 5, 6, 9], [1, 4, 5, 6, 7, 10, 11, 12], [3, 6, 7, 8]].all (adapters =>
    (bag adapters).arrangements == specCount adapters)

test "not a number" := parsed "12\nx" == Err "line 2, column 1: expected a number, got 'x'"
