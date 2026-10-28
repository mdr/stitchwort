-- Advent of Code 2024, day 15: a warehouse map of walls (#), boxes (O) and
-- a robot (@), then the moves the robot attempts (<, ^, >, v), over several
-- lines. Moving into boxes pushes the line of them, unless that would push
-- a box or the robot into a wall, when nothing moves. Part 1 adds up the
-- boxes' GPS coordinates (100 times the row plus the column) after every
-- move; part 2 does the same in a warehouse twice as wide, whose boxes are
-- two cells wide, so a push up or down can move a whole tree of them.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day15.main < examples/2024/day15.txt
--
-- The proofs are in `Aoc.Year2024.Day15.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day15.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day15
import Std (Fail, IO, Int, List, Nat, Option, Parse, Set, Text)
import Std.Parse (grid, lines, many1, pick, section)

def main(): {IO, Fail} () :=
  let document := parseDocument IO.readAll()
  IO.print "Part 1: ${solvePart1 document}"
  IO.print "Part 2: ${solvePart2 document}"

type Position = { row: Int, column: Int }

type Direction =
  | Up
  | Down
  | Left
  | Right

-- The neighbouring position in `direction`.
def Position.step (position: Position) (direction: Direction): Position :=
  match direction with
    | Up => { position | row = position.row - 1 }
    | Down => { position | row = position.row + 1 }
    | Left => { position | column = position.column - 1 }
    | Right => { position | column = position.column + 1 }

-- The walls, the boxes and the robot. In the wide warehouse of part 2 a box
-- is where its left half is, and also covers the cell to its right.
type Warehouse = { walls: Set Position, boxes: Set Position, robot: Position }

-- The warehouse as first mapped, and the moves the robot attempts.
type Document = { warehouse: Warehouse, moves: List Direction }

-- What one character of the map shows.
type Tile =
  | Wall
  | Box
  | Robot
  | Floor

def tile(): {Parse} Tile := pick [("#", Wall), ("O", Box), ("@", Robot), (".", Floor)]

def move(): {Parse} Direction := pick [("^", Up), ("v", Down), ("<", Left), (">", Right)]

-- The map, a blank line, then the moves, over as many lines as they take.
def document(): {Parse} (List (List Tile), List Direction) :=
  let rows := section (() => many1 tile)
  let moves := lines (() => many1 move) |> .concat
  (rows, moves)

-- The positions of every `wanted` tile, row by row.
def positionsOf (rows: List (List Tile)) (wanted: Tile): List Position :=
  rows.gridCells
    |> .filter (((position, here)) => here == wanted)
    |> .map ((((row, column), here)) => ({ row = row.toInt, column = column.toInt }: Position))

def parseDocument (input: Text): {Fail} Document :=
  let (rows, moves) := Parse.all input document
  let robot :=
    match positionsOf rows Robot with
      | [start] => start
      | [] => Fail.fail "expected a robot (@) on the map, found none"
      | _ => Fail.fail "expected one robot (@) on the map, found several"
  let warehouse: Warehouse := { walls = Set.fromList (positionsOf rows Wall), boxes = Set.fromList (positionsOf rows Box), robot }
  { warehouse, moves }

-- The first position from `position` on, going `direction`, without a box:
-- `None` if there are more than `fuel` boxes in a line.
def firstFree (boxes: Set Position) (direction: Direction) (position: Position): (fuel: Nat) → Option Position
  | Zero => None
  | Succ fuel => if boxes.contains position then firstFree boxes direction (position.step direction) fuel else Some position

-- One attempted move. The line of boxes in front of the robot moves one
-- step, which leaves the same boxes as moving the first box to the free
-- position past the last; with no box in front, inserting and removing the
-- free position changes nothing. A line longer than the boxes there are
-- can't happen.
def Warehouse.move (warehouse: Warehouse) (direction: Direction): Warehouse :=
  let next := warehouse.robot.step direction
  match firstFree warehouse.boxes direction next (warehouse.boxes.size + 1) with
    | Some free =>
      if warehouse.walls.contains free then warehouse
      else { warehouse | boxes = warehouse.boxes.insert free |> .remove next, robot = next }
    | None => warehouse

-- Every move in turn.
def Warehouse.moveAll (warehouse: Warehouse) (moves: List Direction): Warehouse := moves.foldLeft warehouse Warehouse.move

-- 100 times the distance from the top edge plus the distance from the left.
def Position.gps (box: Position): Int := 100 * box.row + box.column

def Warehouse.gpsSum (warehouse: Warehouse): Int := warehouse.boxes.toList.sumBy .gps

def solvePart1 (document: Document): Int := document.warehouse.moveAll document.moves |> .gpsSum

-- Part 2.

-- The cells a box covers: where it is, and the cell to the right.
def cellsOf (box: Position): List Position := [box, box.step Right]

-- Where a tile's left half is in the map twice as wide.
def Position.widen (position: Position): Position := { position | column = 2 * position.column }

-- The warehouse twice as wide: each tile becomes two, the robot the left.
def Warehouse.widen (warehouse: Warehouse): Warehouse := {
  walls = warehouse.walls.toList.flatMap (wall => cellsOf wall.widen) |> Set.fromList,
  boxes = warehouse.boxes.map Position.widen,
  robot = warehouse.robot.widen
}

-- The boxes covering `cell`.
def Warehouse.boxesAt (warehouse: Warehouse) (cell: Position): List Position :=
  [cell, cell.step Left] |> .filter (box => warehouse.boxes.contains box)

-- The cells a box moves into when it moves `direction`, other than its own.
def frontOf (box: Position) (direction: Direction): List Position :=
  cellsOf (box.step direction) |> .filter (cell => cell ∉ cellsOf box)

-- The boxes that move with `group` when the cells in `pending` must be
-- emptied: `None` if one of those cells is a wall, or after `fuel` cells.
def Warehouse.gather (warehouse: Warehouse) (direction: Direction) (group: Set Position): (pending: List Position) → (fuel: Nat) → Option (Set Position)
  | Nil, fuel => Some group
  | Cons cell rest, Zero => None
  | Cons cell rest, Succ fuel =>
    if warehouse.walls.contains cell then None
    else
      let found := warehouse.boxesAt cell |> .filter (box => !group.contains box)
      warehouse.gather direction (found.foldLeft group Set.insert) (found.flatMap (box => frontOf box direction) ++ rest) fuel

-- One attempted move in the wide warehouse: the boxes the robot pushes,
-- and those they push in turn, move one step, unless one would hit a wall.
-- Each box adds at most two cells to empty, so the fuel is enough.
def Warehouse.moveWide (warehouse: Warehouse) (direction: Direction): Warehouse :=
  let next := warehouse.robot.step direction
  match warehouse.gather direction Set.empty [next] (2 * warehouse.boxes.size + 1) with
    | Some group =>
      let moved := group.map (box => box.step direction)
      { warehouse | boxes = warehouse.boxes.difference group |> .union moved, robot = next }
    | None => warehouse

def Warehouse.moveAllWide (warehouse: Warehouse) (moves: List Direction): Warehouse := moves.foldLeft warehouse Warehouse.moveWide

def solvePart2 (document: Document): Int := document.warehouse.widen.moveAllWide document.moves |> .gpsSum
