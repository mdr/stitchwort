--| Day 20's puzzle example (aoc/examples/2020/day20.txt): its tiles, the
--| corners and part 1, the orientations, the assembled image, its two sea
--| monsters and part 2.

namespace Aoc.Year2020.Day20.Tests
import Aoc.Year2020.Day20 (..)
import Std (Fail, List, Nat, Option, Result, Set, Text)

def parsed (input: Text): Result Jigsaw Text := Fail.toResult (() => parseJigsaw input)

def example: Text := include "../../../../../examples/2020/day20.txt"

def assembled (input: Text): Result Image Text := Fail.toResult (() => parseJigsaw input |> .assemble)

test "the example has nine tiles of 10 by 10" :=
  (parsed example).map (jigsaw => jigsaw.tiles.map (tile => (tile.image.rows.length, tile.image.columns.length)))
    == Ok (List.replicate 9 (10, 10))

test "the example's tile ids" :=
  (parsed example).map (jigsaw => jigsaw.tiles.map (.id)) == Ok [2311, 1951, 1171, 1427, 1489, 2473, 2971, 2729, 3079]

test "the example's corners" := (parsed example).map (jigsaw => jigsaw.corners.map (.id)) == Ok [1951, 1171, 2971, 3079]
test "the example, part 1" := (parsed example).map (.cornerProduct) == Ok 20899048083289

--| A tile's edges, clockwise from the top; tile 2311's, as the puzzle draws it.
test "tile 2311's top and left edges" :=
  (parsed example).map (jigsaw =>
    jigsaw.tiles.headOr { id = 0, image = { rows = [] } }
      |> (tile => [tile.image.top, tile.image.left].map (edge => edge.pixels.map (.symbol) |> .joinWith "")))
    == Ok ["..##.#..#.", ".#####..#."]

def image3: Image := { rows = [[Rough, Calm, Calm], [Calm, Calm, Calm], [Calm, Calm, Calm]] }

test "a quarter turn moves the top left corner to the top right" :=
  image3.rotate.rows == [[Calm, Calm, Rough], [Calm, Calm, Calm], [Calm, Calm, Calm]]

test "four quarter turns are none" := image3.rotate.rotate.rotate.rotate == image3
test "flipping twice is nothing" := image3.flip.flip == image3

test "every tile of the example has eight different orientations" :=
  (parsed example).map (jigsaw =>
    jigsaw.tiles.all (tile =>
      let all := tile.image.orientations
      all.withIndex.all (((i, one)) => all.withIndex.all (((j, other)) => i == j || one != other))))
    == Ok True

test "the example's arrangement is 3 by 3, with the corners at the corners" :=
  (Fail.toResult (() => parseJigsaw example |> .arrange)).map (arrangement =>
    let ids := arrangement.rows.map (row => row.map (.id))
    (
      ids.map (.length),
      [
        ids.headOr [] |> .headOr 0,
        ids.headOr [] |> .last |> .getOrElse 0,
        ids.last |> .getOrElse [] |> .headOr 0,
        ids.last |> .getOrElse [] |> .last |> .getOrElse 0
      ].sort
    ))
    == Ok ([3, 3, 3], [1171, 1951, 2971, 3079])

test "the example's image is 24 by 24" :=
  (assembled example).map (image => (image.rows.length, image.columns.length)) == Ok (24, 24)

--| The puzzle finds two sea monsters, of 15 pixels each.
test "the example has two sea monsters" :=
  (assembled example).map (image =>
    seaMonster.orientations.map (monster => (image.monsterPixels monster).size) |> .sort)
    == Ok [0, 0, 0, 0, 0, 0, 0, 30]

test "a sea monster has 15 rough pixels" := seaMonster.roughAt.length == 15
test "the example, part 2" := (assembled example).map (.roughness) == Ok 273

test "a pixel is # or ." := not (parsed "Tile 1:\n#x\n..\n").isOk

--| What `Proofs.matchedOriented` needs of the tiles.
test "the example's tiles are rectangles" := (parsed example).map (.rectangular) == Ok True

test "a tile with a short row isn't a rectangle" := not ({ rows = [[Rough, Calm], [Rough]] }: Image).isRectangle
