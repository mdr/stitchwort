-- Day 4 the way most of the community writes it: the letters in a map by
-- position, and from each position a look along each of the eight
-- directions, where a step off the grid finds nothing. For timing and
-- reading beside Day04.sw's shifted lists.

namespace Scratch.MapGrid
import Std (Bool, IO, List, Map, Nat, Option, Text)

type Position = { row: Nat, column: Nat }

type Step =
  | Back
  | Stay
  | Ahead

-- `distance` steps from `start`; none before 0.
def moved (start: Nat) (step: Step) (distance: Nat): Option Nat :=
  match step with
    | Back => if distance ≤ start then Some (start - distance) else None
    | Stay => Some start
    | Ahead => Some (start + distance)

def directions: List (Step, Step) := [
  (Back, Back),
  (Back, Stay),
  (Back, Ahead),
  (Stay, Back),
  (Stay, Ahead),
  (Ahead, Back),
  (Ahead, Stay),
  (Ahead, Ahead)
]

-- The letter `distance` steps from `start`, `down` the rows and `across`.
def letterAlong (letters: Map Position Char) (start: Position) (down: Step) (across: Step) (distance: Nat): Option Char :=
  match moved start.row down distance, moved start.column across distance with
    | Some row, Some column => letters.get { row, column }
    | _, _ => None

def xmasFrom (letters: Map Position Char) (start: Position) (direction: (Step, Step)): Bool :=
  let (down, across) := direction
  ['X', 'M', 'A', 'S'].withIndex |> .all (((distance, letter)) => letterAlong letters start down across distance == Some letter)

-- One letter M and the other S.
def mas (one: Option Char) (other: Option Char): Bool :=
  (one == Some 'M' ∧ other == Some 'S') ∨ (one == Some 'S' ∧ other == Some 'M')

def crossAt (letters: Map Position Char) (centre: Position): Bool :=
  let at := (down across => letterAlong letters centre down across 1)
  letters.get centre == Some 'A' ∧ mas (at Back Back) (at Ahead Ahead) ∧ mas (at Back Ahead) (at Ahead Back)

def main(): {IO} () :=
  let rows := IO.readAllLines() |> .map Text.toList
  let letters: Map Position Char := Map.fromList (rows.gridCells |> .map ((((row, column), letter)) => (({ row, column }: Position), letter)))
  let positions := letters.keys
  IO.print "Part 1: ${positions.sumBy (start => directions.count (xmasFrom letters start))}"
  IO.print "Part 2: ${positions.count (crossAt letters)}"
