--| Day 15's puzzle examples and the parser.

namespace Aoc.Year2020.Day15.Tests
import Aoc.Year2020.Day15 (..)
import Std (Fail, List, NonEmptyList, Result, Text)

def parsed (input: Text): Result Starting Text := Fail.toResult (() => parseStarting input)

def spoken (input: Text) (turn: Nat): Result Nat Text := (parsed input).map (starting => starting.numberSpoken turn)

test "the example's starting numbers" := (parsed "0,3,6\n").map (starting => starting.numbers.toList) == Ok [0, 3, 6]

test "the example's first ten turns" :=
  (parsed "0,3,6").map (starting => (1 ..= 10).map starting.numberSpoken) == Ok [0, 3, 6, 0, 3, 3, 1, 0, 4, 0]

test "turn 0 says nothing" := spoken "0,3,6" 0 == Ok 0

test "the example, part 1" := spoken "0,3,6" 2020 == Ok 436
test "1,3,2, part 1" := spoken "1,3,2" 2020 == Ok 1
test "2,1,3, part 1" := spoken "2,1,3" 2020 == Ok 10
test "1,2,3, part 1" := spoken "1,2,3" 2020 == Ok 27
test "2,3,1, part 1" := spoken "2,3,1" 2020 == Ok 78
test "3,2,1, part 1" := spoken "3,2,1" 2020 == Ok 438
test "3,1,2, part 1" := spoken "3,1,2" 2020 == Ok 1836

test "no starting numbers is an error" := not (parsed "").isOk
test "a starting number is a number" := not (parsed "0,x,6").isOk
