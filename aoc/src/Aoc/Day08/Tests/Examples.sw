-- Day 8's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Day08.main` doesn't check them.

namespace Aoc.Day08.Tests
import Aoc.Day08 (..)
import Std (List, Map, Nat, Option, Text)

-- The puzzle's 20 boxes (also in aoc/examples/day08.txt).
def example: Boxes := parseBoxes (include "../../../../examples/day08.txt").lines

def box (x: Nat) (y: Nat) (z: Nat): Point := { x, y, z }

test "parse a point" := parsePoint "162,817,812" == Some (box 162 817 812)
test "parse rejects other lines" := (parsePoint "", parsePoint "1,2", parsePoint "1,2,3,4", parsePoint "1,b,3") == (None, None, None, None)
test "parse skips a blank last line" := (parsePoints ["1,2,3", ""]).length == 1
test "example has 20 boxes" := example.points.length == 20
test "squared distance" := (box 0 0 0).squaredDistance (box 1 2 2) == 9 && (box 5 5 5).squaredDistance (box 2 9 5) == 25
test "closest first" := closestFirst [box 0 0 0, box 10 0 0, box 1 0 0] == [(1, 0, 2), (81, 1, 2), (100, 0, 1)]
test "equal distances come in box order" := closestFirst [box 0 0 0, box 1 0 0, box 2 0 0, box 3 0 0] == [(1, 0, 1), (1, 1, 2), (1, 2, 3), (4, 0, 2), (4, 1, 3), (9, 0, 3)]
test "the closest pair in the example" := example.pairs.take 1 == [(100427, 0, 19)]
test "all pairs are there" := example.pairs.length == 190
test "separate circuits" := (Circuits.separate 3).sizes 3 == [1, 1, 1] && (Circuits.separate 3).count == 3
test "join" :=
  let joined := (Circuits.separate 4).join 0 1 |> .join 2 1
  (joined.count, joined.sizes 4, joined.labelOf 0 == joined.labelOf 2, joined.labelOf 3 == joined.labelOf 0) == (2, [3, 1], True, False)
test "joining boxes in one circuit changes nothing" := (((Circuits.separate 3).join 0 1).join 1 0).count == 2
test "example part 1" := solvePart1 10 example == 40
test "example part 2" := solvePart2 example == Some 25272
test "part 1 counts pairs already in one circuit" := solvePart1 3 (Boxes.of [box 0 0 0, box 1 0 0, box 2 0 0, box 50 0 0]) == 3 * 1 * 1
test "part 1 with no connections" := solvePart1 0 (Boxes.of [box 0 0 0, box 1 0 0]) == 1
test "part 2 of two boxes" := solvePart2 (Boxes.of [box 3 0 0, box 8 0 0]) == Some 24
test "part 2 of one box" := solvePart2 (Boxes.of [box 3 0 0]) == None
test "part 2 of no boxes" := solvePart2 (Boxes.of []) == None
