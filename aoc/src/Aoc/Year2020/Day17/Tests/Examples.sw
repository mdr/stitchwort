--| Day 17's puzzle example: the slice, its cubes in three and four
--| dimensions, the first cycles and both answers, and the program's cycle
--| against the spec's, cube by cube, around the example.

namespace Aoc.Year2020.Day17.Tests
import Aoc.Year2020.Day17 (..)
import Aoc.Year2020.Day17 (Spec)
import Std (Fail, Int, List, Nat, Result, Set, Text)

def parsed (input: Text): Result Slice Text := Fail.toResult (() => parseSlice input)

--| The active cubes after `cycles` cycles, in `dimensions` dimensions.
def activeAfter (input: Text) (dimensions cycles: Nat): Result Nat Text :=
  (parsed input).map (slice => Nat.iterate cycles Pocket.cycle (slice.pocket dimensions) |> .activeCount)

def example: Text := """
  .#.
  ..#
  ###
  """

test "the example's slice is 3 by 3" :=
  (parsed example).map (slice => (slice.grid.height, slice.grid.width)) == Ok (3, 3)

test "the example's active cubes, in three dimensions" :=
  (parsed example).map (slice => (slice.pocket (dimensions := 3)).active.toList.map (.coordinates))
    == Ok [[0, 2, 0], [1, 0, 0], [1, 2, 0], [2, 1, 0], [2, 2, 0]]

test "the example's active cubes, in four dimensions" :=
  (parsed example).map (slice => (slice.pocket (dimensions := 4)).active.toList.map (.coordinates))
    == Ok [[0, 2, 0, 0], [1, 0, 0, 0], [1, 2, 0, 0], [2, 1, 0, 0], [2, 2, 0, 0]]

test "a cube has 26 neighbours in three dimensions" := ({ coordinates = [0, 0, 0] }: Cube).neighbours.length == 26
test "a cube has 80 neighbours in four dimensions" := ({ coordinates = [0, 0, 0, 0] }: Cube).neighbours.length == 80

--| "After 1 cycle", "After 2 cycles", "After 3 cycles": 11, 21 and 38
--| active cubes in the puzzle's pictures.
test "the example's first three cycles, in three dimensions" :=
  (1 ..= 3).map (activeAfter example 3) == [Ok 11, Ok 21, Ok 38]

--| The puzzle's part 2 pictures: 29 cubes after one cycle, 60 after two.
test "the example's first two cycles, in four dimensions" := (1 ..= 2).map (activeAfter example 4) == [Ok 29, Ok 60]

test "the example, part 1" := (parsed example).map (slice => slice.pocket 3 |> .boot |> .activeCount) == Ok 112
test "the example, part 2" := (parsed example).map (slice => slice.pocket 4 |> .boot |> .activeCount) == Ok 848

test "a row of another width is an error" := not (parsed ".#.\n..\n###\n").isOk
test "a cube is # or ." := not (parsed ".#.\n.x#\n###\n").isOk

--| Every cube with coordinates from -2 to 4, in three dimensions.
def box: List Cube :=
  let range := (0 ..= 6).map (n => n.toInt - 2)
  range.flatMap (x => range.flatMap (y => range.map (z => ({ coordinates = [x, y, z] }: Cube))))

test "the spec's cycle agrees with the program's around the example, twice" :=
  (parsed example).map (slice =>
    let start := slice.pocket 3
    let once := start.cycle
    box.all (cube => once.active.contains cube == Spec.activeAfter start.active cube)
      && box.all (cube => once.cycle.active.contains cube == Spec.activeAfter once.active cube))
    == Ok True
