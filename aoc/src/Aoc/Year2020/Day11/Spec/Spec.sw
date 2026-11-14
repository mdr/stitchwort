--| Day 11 as the puzzle states it, about the seat layout (the program's
--| `Layout`, a grid of `Seat`s): a round of the rules, which seats each
--| passenger considers in each part, and the answer, the occupied seats of
--| the layout where a round changes nothing, reached from the start by
--| rounds. Cells and adjacency are the shared grid code's (`Grid.cells`,
--| `Grid.at`, `touching`); nothing else is shared with the program. The
--| proofs (Proofs/) show the program computes these.

namespace Aoc.Year2020.Day11.Spec
import Aoc.Year2020.Day11 (Layout, Seat)
import Aoc.Common (Offset, Position, touching)
import Std (Int, List, Nat, Option)

--| "The following rules are applied to every seat simultaneously: If a
--| seat is empty (L) and there are no occupied seats adjacent to it, the
--| seat becomes occupied. If a seat is occupied (#) and four or more seats
--| adjacent to it are also occupied, the seat becomes empty. Otherwise, the
--| seat's state does not change." `occupiedNear` is how many of the seats
--| it considers are occupied, and `crowded` how many are too many (four in
--| part 1, five in part 2). Floor is not a seat and never changes.
def becomes (seat: Seat) (occupiedNear crowded: Nat): Seat :=
  if seat == Empty && occupiedNear == 0 then Occupied
  else if seat == Occupied && crowded <= occupiedNear then Empty
  else seat

--| A round: every seat at once, from `considered`, the number of occupied
--| seats a passenger at a position considers, before the round.
def round (layout: Layout) (considered: Position → Nat) (crowded: Nat): Layout :=
  { grid = layout.grid.map (at seat => becomes seat (considered at) crowded) }

--| "How many seats end up occupied?"
def occupiedSeats (layout: Layout): Nat := layout.grid.cells.count (((_, seat)) => seat == Occupied)

--| The rounds from `start` reach `final`, and a round changes nothing
--| there: "at this point, people stop moving around".
def Settles (round: Layout → Layout) (start final: Layout): Prop :=
  ∃ (rounds: Nat) => Nat.iterate rounds round start = final ∧ round final = final

-- Part 1

--| "The number of occupied seats adjacent to a given seat... the eight
--| positions immediately up, down, left, right, or diagonal from the seat":
--| the cells of the layout touching `at` that hold an occupied seat.
def occupiedAdjacent (layout: Layout) (at: Position): Nat :=
  layout.grid.cells.count (((other, seat)) => touching at other && seat == Occupied)

--| Part 1's round: adjacent seats, and four or more occupied are too many.
def adjacentRound (layout: Layout): Layout := round layout (occupiedAdjacent layout) 4

--| "Simulate your seating area by applying the seating rules repeatedly
--| until no seats change state. How many seats end up occupied?"
def Part1 (start: Layout) (answer: Nat): Prop :=
  ∃ (final: Layout) => Settles adjacentRound start final ∧ answer = occupiedSeats final

-- Part 2

--| "Each of those eight directions (up, down, left, right, or diagonal)":
--| a step of at most one row and at most one column, either way, that
--| moves.
def directions: List Offset :=
  [-1, 0, 1].flatMap (rows => [-1, 0, 1].map (columns => ({ rows, columns }: Offset)))
    |> .filter (step => step != Offset.zero)

--| The cell `distance` steps from `at` in `direction`, with its position,
--| if that is on the layout.
def cellAlong (layout: Layout) (at: Position) (direction: Offset) (distance: Nat): Option (Position, Seat) :=
  at.offset (direction.times distance.toInt) |> .flatMap (there => layout.grid.at there |> .map (seat => (there, seat)))

--| What a passenger at `at` can see in `direction`: the cells 1, 2, 3, …
--| steps away, nearest first, up to the edge of the layout. Each step
--| moves a row or a column, so a line of sight leaves the layout within
--| its height plus its width steps.
def lineOfSight (layout: Layout) (at: Position) (direction: Offset): List (Position, Seat) :=
  List.range 1 (layout.grid.height + layout.grid.width + 1)
    |> .map (cellAlong layout at direction)
    |> .takeWhile (.isSome)
    |> .somes

--| "The first seat they can see in each of those eight directions": the
--| first cell along the line of sight that isn't floor.
def firstSeen (layout: Layout) (at: Position) (direction: Offset): Option (Position, Seat) :=
  (lineOfSight layout at direction).find (((_, seat)) => seat != Floor)

--| How many of the first seats seen from `at`, one in each direction, are
--| occupied.
def occupiedSeen (layout: Layout) (at: Position): Nat :=
  directions.count (direction => (firstSeen layout at direction).any (((_, seat)) => seat == Occupied))

--| Part 2's round: "it now takes five or more visible occupied seats for
--| an occupied seat to become empty (rather than four or more from the
--| previous rules)".
def sightRound (layout: Layout): Layout := round layout (occupiedSeen layout) 5

--| "Given the new visibility method and the rule change for occupied seats
--| becoming empty, once equilibrium is reached, how many seats end up
--| occupied?"
def Part2 (start: Layout) (answer: Nat): Prop :=
  ∃ (final: Layout) => Settles sightRound start final ∧ answer = occupiedSeats final

-- The input

--| "Each position is either floor (.), an empty seat (L), or an occupied
--| seat (#)."
def symbol: Seat → Char
  | Floor => '.'
  | Empty => 'L'
  | Occupied => '#'

--| A line of the input is its row of the layout, a position a character.
def RowWritten (line: List Char) (row: List Seat): Prop := line = row.map symbol
