--| Tests for the shared grid code.
-- Kept apart from the code, so that running a day doesn't check them.

namespace Aoc.Common.Tests
import Aoc.Common (..)
import Std (Fail, Graph, List, Map, Option, Parse)
import Std.Parse (digit)

def at (row column: Nat): Position := { row, column }

test "turning" :=
  Direction.turnRight Up == Right
    ∧ Direction.turnLeft Up == Left
    ∧ Direction.opposite Left == Right
    ∧ directions.map Direction.turnRight == [Right, Down, Left, Up]
test "steps" :=
  (at 0 0).step Up == None
    ∧ (at 0 0).step Left == None
    ∧ (at 1 1).step Up == Some (at 0 1)
    ∧ (at 1 1).step Right == Some (at 1 2)
test "neighbours in a corner" := (at 0 0).neighbours == [at 0 1, at 1 0]
test "neighbours inside" := (at 2 3).neighbours == [at 1 3, at 2 4, at 3 3, at 2 2]
test "around a corner" := (at 0 0).around == [at 0 1, at 1 0, at 1 1]
test "around inside" := (at 1 1).around == [at 0 0, at 0 1, at 0 2, at 1 0, at 1 2, at 2 0, at 2 1, at 2 2]
test "adjacent" :=
  adjacent (at 2 3) (at 1 3)
    ∧ adjacent (at 2 3) (at 2 4)
    ∧ not (adjacent (at 2 3) (at 3 4))
    ∧ not (adjacent (at 2 3) (at 2 3))
test "touching" :=
  touching (at 1 1) (at 0 0)
    ∧ touching (at 1 1) (at 2 1)
    ∧ not (touching (at 1 1) (at 1 1))
    ∧ not (touching (at 1 1) (at 3 1))
test "a path" :=
  isPath (p => p.row == 0) (at 0 0) [at 0 1, at 0 2] (at 0 2) ∧ not (isPath (p => True) (at 0 0) [at 1 1] (at 1 1))
test "positions" := positions 2 3 == [at 0 0, at 0 1, at 0 2, at 1 0, at 1 1, at 1 2]

def small: Grid Nat := Grid.of [[1, 2, 3], [4, 5, 6]]

test "a grid's size" := small.height == 2 ∧ small.width == 3 ∧ small.positions == positions 2 3
test "cells" := small.cells == [(at 0 0, 1), (at 0 1, 2), (at 0 2, 3), (at 1 0, 4), (at 1 1, 5), (at 1 2, 6)]
test "cells of ragged rows" := cells [[7], [], [8, 9]] == [(at 0 0, 7), (at 2 0, 8), (at 2 1, 9)]
test "positionsWhere" := small.positionsWhere (n => n % 2 == 0) == [at 0 1, at 1 0, at 1 2]
test "positionsWhere, none" := small.positionsWhere (n => n > 6) == []
test "positionsWhere, rows of any lengths" := positionsWhere (cells [[7], [], [8, 9]]) (n => n > 7) == [at 2 0, at 2 1]
test "findOnly" := Fail.toResult (() => small.findOnly 5 "five") == Ok (at 1 1)
test "findOnly, none" := Fail.toResult (() => small.findOnly 7 "seven") == Err "no seven"
test "onlyCell, rows of any lengths" := Fail.toResult (() => onlyCell (cells [[7], [], [8, 9]]) 9 "nine") == Ok (at 2 1)
test "findOnly, several" := Fail.toResult (() => (Grid.of [[1, 2], [2, 3]]).findOnly 2 "two") == Err "more than one two"
test "at" := small.at (at 1 2) == Some 6 ∧ small.at (at 2 0) == None ∧ small.at (at 0 3) == None
test "lookup is at" :=
  (List.range 0 4 |> .all (r => List.range 0 5 |> .all (c => small.lookup (at r c) == small.at (at r c))))
test "map" := (small.map (p x => p.row * 10 + x)).rows == [[1, 2, 3], [14, 15, 16]]
test "a grid's step" :=
  small.step (at 1 2) Right == None ∧ small.step (at 1 2) Down == None ∧ small.step (at 1 1) Right == Some (at 1 2)

--| A grid of digits read from `text`.
def parsedGrid (text: Text): Result (Grid Nat) Text :=
  Fail.toResult (() => parseGrid text digit) |> .map (grid => grid.map (_ digit => digit.toNat))

test "parse a grid" := parsedGrid """
  123
  456
  """ == Ok small
test "parse a short row" := parsedGrid "123\n45\n" == Err "line 2: expected 3 cells, as on the first line, got 2"
test "parse a letter" :=
  parsedGrid "123\n4x6\n" == Err "line 2, column 2: expected a digit or the end of the line, got 'x'"
test "parse nothing" := parsedGrid "" == Err "expected a grid, got no cells"
test "an empty line has no cells" :=
  parsedGrid "\n\n" == Err "line 1, column 1: expected a digit, got the end of the line"

test "a rectangle" :=
  small.isRectangle ∧ not (Grid.of [[1, 2], [3]]).isRectangle ∧ not (Grid.of [[1], [2, 3]]).isRectangle

--| The cells a breadth-first search reaches from the top left, through
--| the cells that aren't 9.
def reached (grid: Grid Nat): List Position :=
  (grid.graph (p cell => if cell == 9 then None else Some 1)).breadthFirst [at 0 0] |> .keys

test "a grid's graph" :=
  reached (Grid.of [[1, 9, 1], [1, 9, 1], [1, 1, 1]]) == [at 0 0, at 0 2, at 1 0, at 1 2, at 2 0, at 2 1, at 2 2]
test "a wall" := reached (Grid.of [[1, 9, 1], [9, 9, 1]]) == [at 0 0]
test "a box's distances" := ((boxGraph 2 2 (p => p.row + p.column)).distances [(at 0 0, 0)]).get (at 1 1) == Some 3

test "a box's distances with its index" :=
  let graph := boxGraph 3 4 (p => p.row + p.column)
  graph.distances (index := boxIndex 3 4) [(at 0 0, 0)] |> .toList == (graph.distances [(at 0 0, 0)] |> .toList)

test "a box numbers its positions row by row" :=
  (boxIndex 3 4).number (at 2 1) == Some 9
    ∧ (boxIndex 3 4).number (at 1 4) == None
    ∧ (boxIndex 3 4).decode 9 == Some (at 2 1)
