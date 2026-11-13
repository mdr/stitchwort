--| Day 15 as the puzzle states it, over the program's cave (its rows of
--| digits, `height` and `width`). The proofs (Proofs/) show the program's
--| answers are these, for every cave the parser accepts.

namespace Aoc.Year2021.Day15.Spec
import Aoc.Year2021.Day15 (..)
import Aoc.Common (Position)
import Std (Fin, List, Nat, Option)

--| The puzzle's map: a rectangle of risk levels, with at least one. (The
--| parser guarantees it; Proofs/Parse.sw.)
def Rectangle (cave: Cave): Prop := 0 < cave.width ∧ (∀ (row: List (Fin 10)) => row ∈ cave.grid.rows → row.length = cave.width)

--| The risk level at a position: the digit in that row and column. A
--| position off the map has none.
def levelAt (cave: Cave) (position: Position): Option Nat := match cave.grid.rows.get position.row with
  | None => None
  | Some row => row.get position.column |> .map Fin.toNat

--| "You start in the top left position."
def topLeft: Position := { row = 0, column = 0 }

--| "Your destination is the bottom right position", of a map `height`
--| rows by `width` columns.
def bottomRight (height: Nat) (width: Nat): Position := { row = height - 1, column = width - 1 }

--| A path through a map whose levels are `levels`: the positions it
--| enters, in turn, from `from` to `to`. "You can't move diagonally": each
--| is `adjacent` to the one before (up, down, left or right; the shared
--| grid code's `Aoc.Common.isPath`). Each is on the map, with a level.
def isPath (levels: Position → Option Nat) (from: Position) (steps: List Position) (to: Position): Bool :=
  Aoc.Common.isPath (position => (levels position).isSome) from steps to

--| "The total risk of a path is the sum of the risk levels of each position
--| you enter (that is, don't count the risk level of your starting position
--| unless you enter it)."
def totalRisk (levels: Position → Option Nat) (steps: List Position): Nat := steps.sumBy (position => (levels position).getOrElse 0)

--| "The lowest total risk of any path from the top left to the bottom
--| right": some path from `topLeft` to `target` has total risk `answer`,
--| and none has less.
def LowestRisk (levels: Position → Option Nat) (target: Position) (answer: Nat): Prop :=
  (∃ (steps: List Position) => isPath levels topLeft steps target = True ∧ totalRisk levels steps = answer)
    ∧ (∀ (steps: List Position) => isPath levels topLeft steps target = True → answer ≤ totalRisk levels steps)

--| Part 1: the lowest total risk through the cave.
def Part1Answer (cave: Cave) (answer: Nat): Prop := LowestRisk (levelAt cave) (bottomRight cave.height cave.width) answer

--| "Each time the tile repeats to the right or downward, all of its risk
--| levels are 1 higher than the tile immediately up or left of it.
--| However, risk levels above 9 wrap back around to 1."
def raise (level: Nat): Nat := if level == 9 then 1 else level + 1

--| "The entire cave is actually five times larger in both dimensions": the
--| level at `position` of the full map. It is in the tile whose row and
--| column are the position's row and column divided by the cave's height
--| and width, and at the place in that tile given by the remainders. That
--| tile is as many tiles right of and below the first as its column and
--| row, and each tile raises the one up or left of it by 1, so the level is
--| the first tile's at that place, raised once per tile.
def tiledLevelAt (cave: Cave) (position: Position): Option Nat :=
  if tall: cave.height != 0 then
    if wide: cave.width != 0 then
      if position.row < 5 * cave.height && position.column < 5 * cave.width then
        levelAt cave { row = position.row % cave.height, column = position.column % cave.width }
          |> .map (level => (position.row / cave.height + position.column / cave.width).iterate raise level)
      else None
    else None
  else None

--| Part 2: the lowest total risk through the full cave.
def Part2Answer (cave: Cave) (answer: Nat): Prop := LowestRisk (tiledLevelAt cave) (bottomRight (5 * cave.height) (5 * cave.width)) answer
