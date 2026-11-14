--| Day 3 as the puzzle states it. The proofs (Proofs/) show the program's
--| counts are these.

namespace Aoc.Year2020.Day03.Spec
import Aoc.Common (Grid, Position)
import Aoc.Year2020.Day03 (Slope, Square)
import Std (List, Nat, Option)

--| "The same pattern repeats to the right many times": the square in
--| `column` of a row whose pattern is `pattern`. Past the pattern's end it
--| is the square a pattern's width to the left.
def repeatingAt (pattern: List Square) (column: Nat): Option Square
    decreasing column
:=
  if within: column < pattern.length then pattern.get column
  else if nonEmpty: pattern.length ≠ 0 then repeatingAt pattern (column - pattern.length) [decreasing := omega]
  else None

--| The square at `position` of the repeating map; none past the bottom.
def squareAt (map: Grid Square) (position: Position): Option Square := match map.rows.get position.row with
  | Some pattern => repeatingAt pattern position.column
  | None => None

--| "Right 3, down 1" from `position`.
def moved (position: Position) (slope: Slope): Position :=
  { row = position.row + slope.down, column = position.column + slope.right }

--| "Check the position that is right 3 and down 1. Then, check the position
--| that is right 3 and down 1 from there, and so on": `steps` positions,
--| each moved along `slope` from the one before.
def path (slope: Slope) (from: Position): (steps: Nat) → List Position
  | Zero => []
  | Succ more =>
    let next := moved from slope
    [next, ..path slope next more]

--| "From your starting position at the top-left, … and so on until you go
--| past the bottom of the map." A step goes at least one row down, so no
--| more steps than the map has rows are needed.
def visited (map: Grid Square) (slope: Slope): List Position :=
  path slope { row = 0, column = 0 } map.height |> .takeWhile (position => position.row < map.height)

--| "How many trees would you encounter?"
def treesEncountered (map: Grid Square) (slope: Slope): Nat :=
  (visited map slope |> .filter (position => squareAt map position == Some Tree)).length

--| "Starting at the top-left corner of your map and following a slope of
--| right 3 and down 1, how many trees would you encounter?"
def part1Answer (map: Grid Square): Nat := treesEncountered map { right = 3, down = 1 }

--| "Determine the number of trees you would encounter if, for each of the
--| following slopes, you start at the top-left corner and traverse the map
--| all the way to the bottom: Right 1, down 1. Right 3, down 1. (This is the
--| slope you already checked.) Right 5, down 1. Right 7, down 1. Right 1,
--| down 2."
def puzzleSlopes: List Slope := [
  { right = 1, down = 1 },
  { right = 3, down = 1 },
  { right = 5, down = 1 },
  { right = 7, down = 1 },
  { right = 1, down = 2 }
]

--| "What do you get if you multiply together the number of trees
--| encountered on each of the listed slopes?"
def part2Answer (map: Grid Square): Nat := puzzleSlopes.map (treesEncountered map) |> List.product
