-- Advent of Code 2024, day 12: a map of garden plots, each growing one plant
-- (a letter). Plots with the same plant touching up, down, left or right form
-- a region. Part 1 adds up, over the regions, area times perimeter; part 2
-- adds up area times the number of sides.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day12.main < examples/2024/day12.txt
--
-- The proofs are in `Aoc.Year2024.Day12.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day12.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day12
import Std (Bool, Char, DecEq, Fail, IO, List, Map, Nat, Option, Parse, Set, Text, Void)

def main(): {IO, Fail} () :=
  let garden := parseGarden IO.readAll()
  IO.print "Part 1: ${solvePart1 garden}"
  IO.print "Part 2: ${solvePart2 garden}"

type Position = { row: Nat, column: Nat }

-- The plant of each plot, by position.
type Garden = { plots: Map Position Char }

type Direction =
  | Up
  | Down
  | Left
  | Right

def directions: List Direction := [Up, Down, Left, Right]

-- One plot: its plant, a letter.
def plot(): {Parse} Char := Parse.satisfy "a letter" (char => char.isAsciiLetter)

-- One row per line, all as long as the first.
def parseGarden (input: Text): {Fail} Garden :=
  let rows := Parse.all input (() => Parse.grid plot)
  let width := rows.headOr [] |> .length
  rows.withIndex |> .map (((row, plants)) =>
    Fail.ensure (plants.length == width) "line ${row + 1}: expected ${width} plots, as on the first line, got ${plants.length}")
  let plots :=
    rows.withIndex
      |> .flatMap (((row, plants)) => plants.withIndex |> .map (((column, plant)) => (({ row, column }: Position), plant)))
  { plots = Map.fromList plots }

-- The plant at `position`; `None` off the map.
def Garden.plantAt (garden: Garden) (position: Position): Option Char := garden.plots.get position

-- Every plot of the map, row by row.
def Garden.positions (garden: Garden): List Position := garden.plots.keys

-- The grid point one step in `direction`; none above row 0 or left of column
-- 0.
def Position.step (position: Position): Direction → Option Position
  | Up =>
    match position.row with
      | Zero => None
      | Succ above => Some ({ position | row = above })
  | Down => Some ({ position | row = position.row + 1 })
  | Left =>
    match position.column with
      | Zero => None
      | Succ before => Some ({ position | column = before })
  | Right => Some ({ position | column = position.column + 1 })

-- Whether the plot one step in `direction` grows the same plant.
def Garden.sameAcross (garden: Garden) (position: Position) (direction: Direction): Bool :=
  (position.step direction |> .flatMap garden.plantAt) == garden.plantAt position

-- The neighbours growing `plant`.
def Garden.neighboursGrowing (garden: Garden) (plant: Char) (position: Position): List Position :=
  directions.filterMap position.step |> .filter (next => garden.plantAt next == Some plant)

-- How many positions the fill has still to visit: it gets smaller each time
-- the fill takes a plot.
def Garden.unvisited (garden: Garden) (visited: Set Position): Nat := garden.positions.count (position => !visited.contains position)

-- A position growing a plant is on the list.
theorem Garden.positionsComplete (garden: Garden) (position: Position) (plant: Char) (grows: garden.plantAt position = Some plant):
    position ∈ garden.positions :=
  Map.memKeysOfContains garden.plots position (Map.containsOfGet garden.plots position plant grows)

-- No more pass `kept` than `p` when `kept` implies `p`.
theorem countLe: (xs: List a) → (p: a → Bool) → (kept: a → Bool) → ((x: a) → kept x = True → p x = True) → xs.count kept ≤ xs.count p
  | Nil, p, kept, implies => rfl
  | Cons x rest, p, kept, implies =>
    rewrite List.countCons rest x kept, List.countCons rest x p in
      let fewer := countLe rest p kept implies
      match keeps: kept x with
        | True => rewrite implies x keeps in omega [fewer]
        | False => omega [fewer]

-- Fewer pass `kept` than `p` when `kept` implies `p` and some member passes
-- `p` but not `kept`.
theorem countFewer: (xs: List a) → (p: a → Bool) → (kept: a → Bool) → ((x: a) → kept x = True → p x = True) → (dropped: a) → dropped ∈ xs →
    p dropped = True → kept dropped = False → xs.count kept < xs.count p
  | Nil, p, kept, implies, dropped, member, passes, fails => Void.exfalso member
  | Cons x rest, p, kept, implies, dropped, Inl same, passes, fails =>
    rewrite List.countCons rest x kept, List.countCons rest x p, same, passes, fails in omega [countLe rest p kept implies]
  | Cons x rest, p, kept, implies, dropped, Inr later, passes, fails =>
    rewrite List.countCons rest x kept, List.countCons rest x p in
      let fewer := countFewer rest p kept implies dropped later passes fails
      match keeps: kept x with
        | True => rewrite implies x keeps in omega [fewer]
        | False => omega [fewer]

-- Taking a plot not yet visited leaves fewer to visit.
theorem Garden.unvisitedInsert (garden: Garden) (visited: Set Position) (position: Position) (plant: Char)
    (grows: garden.plantAt position = Some plant) (fresh: visited.contains position = False):
    garden.unvisited (visited.insert position) < garden.unvisited visited :=
  countFewer garden.positions (other => !visited.contains other) (other => !(visited.insert position).contains other)
    (other kept =>
      match same: visited.contains other with
        | True => rewrite Set.containsInsertMono visited position other same at kept in kept
        | False => rfl)
    position (garden.positionsComplete position plant grows) (rewrite fresh in rfl) (rewrite Set.containsInsert position visited in rfl)

-- The plots growing `plant` reachable from the stack, joined to `members`:
-- a depth-first flood fill. `visited` has the members, for quick lookup.
def Garden.fill (garden: Garden) (plant: Char) (stack: List Position) (visited: Set Position) (members: List Position): List Position
    decreasing (garden.unvisited visited, stack.length)
:=
  match stack with
    | Nil => members
    | Cons position rest =>
      match taken: visited.contains position with
        | True => Garden.fill garden plant rest visited members [decreasing := Nat.LexLess.Second rfl (omega)]
        | False =>
          match grows: garden.plantAt position == Some plant with
            | True =>
              Garden.fill garden plant (garden.neighboursGrowing plant position ++ rest) (visited.insert position) (Cons position members)
                [decreasing := Nat.LexLess.First (garden.unvisitedInsert visited position plant (DecEq.sound _ _ grows) taken)]
            | False => Garden.fill garden plant rest visited members [decreasing := Nat.LexLess.Second rfl (omega)]

-- The region containing `start`: the plots joined to it.
def Garden.regionOf (garden: Garden) (start: Position): List Position :=
  match garden.plantAt start with
    | Some plant => garden.fill plant [start] Set.empty Nil
    | None => Nil

-- The regions, each once, from the positions not yet in a region.
def Garden.regionsFrom (garden: Garden): (starts: List Position) → (seen: Set Position) → List (List Position)
  | Nil, seen => Nil
  | Cons start rest, seen =>
    if seen.contains start then garden.regionsFrom rest seen
    else
      let region := garden.regionOf start
      Cons region (garden.regionsFrom rest (region.foldLeft seen Set.insert))

def Garden.regions (garden: Garden): List (List Position) := garden.regionsFrom garden.positions Set.empty

-- A plot's sides with a fence: those not facing the same plant.
def Garden.fences (garden: Garden) (position: Position): Nat := directions.count (direction => !garden.sameAcross position direction)

def Garden.perimeter (garden: Garden) (region: List Position): Nat := region.sumBy garden.fences

-- The four corners of a plot: the side up or down, and the side left or
-- right.
def quadrants: List (Direction, Direction) := [(Up, Left), (Up, Right), (Down, Left), (Down, Right)]

-- A corner of the region's fence at a plot: outside, where neither side
-- faces the same plant, or inside, where both do but the plot diagonally
-- across doesn't.
def Garden.isCorner (garden: Garden) (position: Position) (quadrant: (Direction, Direction)): Bool :=
  let (vertical, horizontal) := quadrant
  let diagonal := position.step vertical |> .flatMap (next => next.step horizontal) |> .flatMap garden.plantAt
  match garden.sameAcross position vertical, garden.sameAcross position horizontal with
    | False, False => True
    | True, True => diagonal != garden.plantAt position
    | _, _ => False

-- The number of sides equals the number of corners.
def Garden.sides (garden: Garden) (region: List Position): Nat := region.sumBy (position => quadrants.count (garden.isCorner position))

def solvePart1 (garden: Garden): Nat := garden.regions |> .sumBy (region => region.length * garden.perimeter region)

def solvePart2 (garden: Garden): Nat := garden.regions |> .sumBy (region => region.length * garden.sides region)
