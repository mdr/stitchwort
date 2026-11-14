--| Day 15's tests: the puzzle's examples and unit tests.
--
-- Kept apart from the program, so `stitchwort run Aoc.Year2024.Day15.main`
-- doesn't check them.

namespace Aoc.Year2024.Day15.Tests
import Aoc.Common (Direction)
import Aoc.Year2024.Day15 (..)
import Std (Fail, Int, List, Nat, Option, Result, Set, Text)

--| The smaller example of part 1.
def smallExample: Text := """
  ########
  #..O.O.#
  ##@.O..#
  #...O..#
  #.#.O..#
  #...O..#
  #......#
  ########

  <^^>>>vv<v>>v<<
  """

--| The larger example, as in examples/2024/day15.txt.
def largeExample: Text := """
  ##########
  #..O..O.O#
  #......O.#
  #.OO..O.O#
  #..O@..O.#
  #O#..O...#
  #O..O..O.#
  #.OO.O.OO#
  #....O...#
  ##########

  <vv>^<v^>v>^vv^v>v<>v^v<v<^vv<<<^><<><>>v<vvv<>^v^>^<<<><<v<<<v^vv^v>^
  vvv<<^>^v^^><<>>><>^<<><^vv^^<>vvv<>><^^v>^>vv<>v<<<<v<^v>^<^^>>>^<v<v
  ><>vv>v^v^<>><>>>><^^>vv>v<^^^>>v^v^<^^>v^^>v^<^v>v<>>v^v^<v>v^^<^^vv<
  <<v<^>>^^^^>>>v^<>vvv^><v<<<>^^^vv^<vvv>^>v<^^^^v<>^>vvvv><>>v^<<^^^^^
  ^><^><>>><>^^<<^^v>>><^<v>^<vv>>v>>>^v><>^v><<<<v>>v<v<v>vvv>^<><<>^><
  ^>><>^v<><^vvv<^^<><v<<<<<><^v<<<><<<^^<v<^^^><^>>^<v^><<<^>>^v<v^v<v^
  >^>>^v>vv>^<<^v<>><<><<v<<v><>v<^vv<<<>^^v^>^^>>><<^v>>v^v><^^>>^<>vv^
  <><^^>^^^<><vvvvv^v<v<<>^v<v>v<<^><<><<><<<^^<<<^<<>><<><^^^>^^<>^>v<>
  ^^>vv<^v^v<vv>^<><v<^v>^^^>>>^^vvv^>vvv<>>>^<^>>>>>^<<^v>^vvv<>^<><<v>
  v^^>>><<^^<>>^v^<v^vv<>v^<<>^<^v^v><^<<<><<^<v><v<>vv>>v><v^<vv<>v^<<^
  """

--| The small example of part 2.
def wideExample: Text := """
  #######
  #...#.#
  #.....#
  #..OO@#
  #..O..#
  #.....#
  #######

  <vv<<^^<<^^
  """

def parsed (input: Text): Result Document Text := Fail.toResult (() => parseDocument input)

def documentOf (input: Text): Result Document Text := parsed input

--| A warehouse drawn as the puzzle draws it, in a map whose rows are `rows`,
--| with no moves: for edge cases.
def warehouseOf (rows: Text): Result Warehouse Text :=
  documentOf "${rows}\n\n<\n" |> .map (document => document.warehouse)

def at (row column: Int): Cell := { rows = row, columns = column }

--| The boxes, row by row.
def boxesOf (warehouse: Warehouse): List Cell := warehouse.boxes.toList

--| The puzzle's map of a warehouse, `wide` for part 2's boxes.
def draw (wide: Bool) (warehouse: Warehouse) (height width: Nat): List Text :=
  List.range 0 height
    |> .map (row =>
      List.range 0 width
        |> .map (column =>
          let here := at row.toInt column.toInt
          if here == warehouse.robot then '@'
          else if warehouse.walls.contains here then '#'
          else if warehouse.boxes.contains here then if wide then '[' else 'O'
          else if wide && warehouse.boxes.contains (here.step Left) then ']'
          else '.')
        |> Text.fromList)

test "small example, part 1" := documentOf smallExample |> .map solvePart1 == Ok 2028
test "large example, part 1" := documentOf largeExample |> .map solvePart1 == Ok 10092
test "large example, part 2" := documentOf largeExample |> .map solvePart2 == Ok 9021
test "wide example, part 2" := documentOf wideExample |> .map solvePart2 == Ok 618

test "large example, the final map" :=
  documentOf largeExample |> .map (document => draw False (document.warehouse.moveAll document.moves) 10 10)
    == Ok ["##########", "#.O.O.OOO#", "#........#", "#OO......#", "#OO@.....#", "#O#.....O#", "#O.....OO#",
      "#O.....OO#", "#OO....OO#", "##########"]

test "large example, the widened map" :=
  documentOf largeExample |> .map (document => draw True document.warehouse.widen 10 20)
    == Ok ["####################", "##....[]....[]..[]##", "##............[]..##", "##..[][]....[]..[]##",
      "##....[]@.....[]..##", "##[]##....[]......##", "##[]....[]....[]..##", "##..[][]..[]..[][]##",
      "##........[]......##", "####################"]

test "large example, part 2's final map" :=
  documentOf largeExample |> .map (document => draw True (document.warehouse.widen.moveAllWide document.moves) 10 20)
    == Ok ["####################", "##[].......[].[][]##", "##[]...........[].##", "##[]........[][][]##",
      "##[]......[]....[]##", "##..##......[]....##", "##..[]............##", "##..@......[].[][]##",
      "##......[][]..[]..##", "####################"]

--| The small example's moves, one at a time: the maps after each.
test "small example, each move" :=
  documentOf smallExample
    |> .map (document =>
      let maps :=
        document.moves.scanLeft document.warehouse Warehouse.move |> .map (warehouse => draw False warehouse 8 8)
      (maps.get 4, maps.get 7, maps.get 15))
    == Ok (
      Some ["########", "#..@OO.#", "##..O..#", "#...O..#", "#.#.O..#", "#...O..#", "#......#", "########"],
      Some ["########", "#....OO#", "##..@..#", "#...O..#", "#.#.O..#", "#...O..#", "#...O..#", "########"],
      Some ["########", "#....OO#", "##.....#", "#.....O#", "#.#O@..#", "#...O..#", "#...O..#", "########"]
    )

--| The wide example's moves, one at a time.
test "wide example, each move" :=
  documentOf wideExample
    |> .map (document =>
      let maps :=
        document.moves.scanLeft document.warehouse.widen Warehouse.moveWide
          |> .map (warehouse => draw True warehouse 7 14)
      (maps.get 0, maps.get 1, maps.get 6, maps.get 7 == maps.get 6, maps.get 11))
    == Ok (
      Some ["##############", "##......##..##", "##..........##", "##....[][]@.##", "##....[]....##", "##..........##",
        "##############"],
      Some ["##############", "##......##..##", "##..........##", "##...[][]@..##", "##....[]....##", "##..........##",
        "##############"],
      Some ["##############", "##......##..##", "##...[][]...##", "##....[]....##", "##.....@....##", "##..........##",
        "##############"],
      True,
      Some ["##############", "##...[].##..##", "##...@.[]...##", "##....[]....##", "##..........##", "##..........##",
        "##############"]
    )

--| Edge cases, part 1.
test "walking into a wall" := warehouseOf "#@." |> .map (warehouse => warehouse.move Left == warehouse) == Ok True
test "walking onto the floor" := warehouseOf "#@." |> .map (warehouse => (warehouse.move Right).robot) == Ok (at 0 2)
test "pushing one box" := warehouseOf "@O." |> .map (warehouse => boxesOf (warehouse.move Right)) == Ok [at 0 2]
test "pushing a chain of boxes" :=
  warehouseOf "@OOO.#" |> .map (warehouse => boxesOf (warehouse.move Right)) == Ok [at 0 2, at 0 3, at 0 4]
test "pushing a chain into a wall" :=
  warehouseOf "@OOO#" |> .map (warehouse => warehouse.move Right == warehouse) == Ok True
test "a chain stops at the first gap" :=
  warehouseOf "@OO.O#" |> .map (warehouse => boxesOf (warehouse.move Right)) == Ok [at 0 2, at 0 3, at 0 4]
test "pushing up" := warehouseOf """
  .
  O
  @""" |> .map (warehouse => boxesOf (warehouse.move Up)) == Ok [at 0 0]
test "pushing up into a wall" := warehouseOf """
  #
  O
  @""" |> .map (warehouse => warehouse.move Up == warehouse) == Ok True
test "the GPS of a box" := (at 1 4).gps == 104

--| Edge cases, part 2.
def wideOf (rows: Text): Result Warehouse Text := warehouseOf rows |> .map (warehouse => warehouse.widen)

test "widening" := wideOf "#O@." |> .map (warehouse => draw True warehouse 1 8) == Ok ["##[]@..."]
test "pushing a wide box left" :=
  wideOf ".O@" |> .map (warehouse => draw True (warehouse.moveWide Left |> .moveWide Left) 1 6) == Ok ["[]@..."]
test "pushing a wide box right" :=
  wideOf "@O.." |> .map (warehouse => draw True (warehouse.moveWide Right) 1 8) == Ok [".@[]...."]
--| A box under two others, the robot under its right half, and `walls`: the
--| push up meets both boxes above.
def stacked (walls: List Cell): Warehouse :=
  { walls = walls.toSet, boxes = [at 1 2, at 1 4, at 2 3].toSet, robot = at 3 4 }

test "pushing a box up pushes both boxes on it" :=
  draw True ((stacked []).moveWide Up) 4 8 == ["..[][]..", "...[]...", "....@...", "........"]
test "a push up blocked above the right box moves nothing" := (stacked [at 0 5]).moveWide Up == stacked [at 0 5]
test "a push up blocked above the left box moves nothing" := (stacked [at 0 2]).moveWide Up == stacked [at 0 2]
test "a push up beside a wall moves" := (stacked [at 0 1]).moveWide Up |> .robot == at 2 4
test "the right half of a box is pushed too" := wideOf """
  ..
  O.
  .@""" |> .map (wide => boxesOf ({ wide | robot = at 2 1 }.moveWide Up)) == Ok [at 0 0]
test "the GPS of a wide box is its left half's" := (at 1 5).gps == 105

--| Parsing.
test "parse" := parsed """
  #@O.

  <>
  ^v
  """ |> .map (document => document.moves) == Ok [Left, Right, Up, Down]
test "parse the positions" := parsed """
  #@O.

  <
  """ |> .map (document => (document.warehouse.robot, boxesOf document.warehouse)) == Ok (at 0 1, [at 0 2])
test "no robot" := parsed "#.O.\n\n<\n" == Err "expected a robot (@) on the map, found none"
test "two robots" := parsed "@.@.\n\n<\n" == Err "expected one robot (@) on the map, found several"
test "a bad tile" :=
  parsed "#@x.\n\n<\n" == Err "line 1, column 3: expected '#', 'O', '@', '.', a line break or a blank line, got 'x'"
test "a bad move" :=
  parsed "#@.\n\n<x\n" == Err "line 3, column 2: expected '^', 'v', '<', '>' or the end of the line, got 'x'"
test "no moves" :=
  parsed "#@.\n" == Err "line 2, column 1: expected '#', 'O', '@', '.' or a blank line, got the end of the input"
