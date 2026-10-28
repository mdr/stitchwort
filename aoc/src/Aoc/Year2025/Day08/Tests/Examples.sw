-- Day 8's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Year2025.Day08.main` doesn't check them.

namespace Aoc.Year2025.Day08.Tests
import Aoc.Year2025.Day08 (..)
import Std (Fail, List, Map, Nat, Option, Result, Text)

-- The puzzle's 20 boxes (also in aoc/examples/2025/day08.txt), or why they
-- didn't parse.
def example: Result Boxes Text := Fail.toResult (() => parseBoxes (include "../../../../../examples/2025/day08.txt"))

def box (x: Nat) (y: Nat) (z: Nat): Point := { x, y, z }

def pointsOf (input: Text): Result (List Point) Text := Fail.toResult (() => parsePoints input)

test "parse a point" := pointsOf "162,817,812" == Ok [box 162 817 812]
test "parse rejects other lines" := pointsOf "1,2,3\n1,b,3" == Err "line 2, column 3: expected a number, got 'b'"
test "parse rejects too few and too many" :=
  (pointsOf "1,2", pointsOf "1,2,3,4") == (Err "line 1, column 4: expected ',', got the end of the line", Err "line 1, column 6: expected the end of the line, got ','")
test "parse rejects a blank line" := pointsOf "1,2,3\n\n" == Err "line 2, column 1: expected a number, got the end of the line"
test "parse allows spaces" := pointsOf " 1, 2 ,3 " == Ok [box 1 2 3]
test "the example loads" := example.isOk
test "example has 20 boxes" := example.map (boxes => boxes.points.length) == Ok 20
test "squared distance" := (box 0 0 0).squaredDistance (box 1 2 2) == 9 ∧ (box 5 5 5).squaredDistance (box 2 9 5) == 25
def connection (distance: Nat) (first: Nat) (second: Nat): Connection := { distance, first, second }

test "closest first" := closestFirst [box 0 0 0, box 10 0 0, box 1 0 0] == [connection 1 0 2, connection 81 1 2, connection 100 0 1]
test "equal distances come in box order" :=
  closestFirst [box 0 0 0, box 1 0 0, box 2 0 0, box 3 0 0]
    == [connection 1 0 1, connection 1 1 2, connection 1 2 3, connection 4 0 2, connection 4 1 3, connection 9 0 3]
test "the closest pair in the example" := example.map (boxes => boxes.pairs.take 1) == Ok [connection 100427 0 19]
test "all pairs are there" := example.map (boxes => boxes.pairs.length) == Ok 190
test "separate circuits" := (Circuits.separate 3).sizes 3 == [1, 1, 1] ∧ (Circuits.separate 3).count == 3
test "join" :=
  let joined := (Circuits.separate 4).join 0 1 |> .join 2 1
  (joined.count, joined.sizes 4, joined.labelOf 0 == joined.labelOf 2, joined.labelOf 3 == joined.labelOf 0) == (2, [3, 1], True, False)
test "sizes come in the order of the labels" := ((Circuits.separate 3).join 0 2).sizes 3 == [1, 2]
test "joining boxes in one circuit changes nothing" := (((Circuits.separate 3).join 0 1).join 1 0).count == 2
test "example part 1" := example.map (solvePart1 10) == Ok 40
test "example part 2" := example.map solvePart2 == Ok (Some 25272)
test "part 1 counts pairs already in one circuit" := solvePart1 3 (Boxes.of [box 0 0 0, box 1 0 0, box 2 0 0, box 50 0 0]) == 3 * 1 * 1
test "part 1 with no connections" := solvePart1 0 (Boxes.of [box 0 0 0, box 1 0 0]) == 1
test "part 1 with more connections than pairs" := solvePart1 100 (Boxes.of [box 0 0 0, box 1 0 0, box 2 0 0, box 50 0 0]) == 4
test "boxes at the same place are different boxes" :=
  let boxes := Boxes.of [box 1 1 1, box 1 1 1, box 9 9 9]
  (boxes.pairs.take 1, solvePart1 1 boxes, solvePart2 boxes) == ([connection 0 0 1], 2 * 1, Some (1 * 9))
test "part 2 of two boxes" := solvePart2 (Boxes.of [box 3 0 0, box 8 0 0]) == Some 24
test "part 2 can be 0" := solvePart2 (Boxes.of [box 0 0 0, box 10 0 0, box 11 0 0]) == Some (0 * 10)
test "part 2 of one box" := solvePart2 (Boxes.of [box 3 0 0]) == None
test "part 2 of no boxes" := solvePart2 (Boxes.of []) == None
