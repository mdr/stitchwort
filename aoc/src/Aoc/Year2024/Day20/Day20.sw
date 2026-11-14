--| Advent of Code 2024, day 20: a racetrack of track and walls from S to E.
--| Once in a race a program may cheat, passing through walls for a few
--| picoseconds and ending back on track. Part 1 counts the cheats of up to 2
--| picoseconds that save at least 100 picoseconds; part 2 those of up to 20.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2024.Day20.main < inputs/2024/day20.txt
--|   $ cd aoc && stitchwort run Aoc.Year2024.Day20.main -- 50 < examples/2024/day20.txt
--|
--| The proofs are in `Aoc.Year2024.Day20.Proofs` (Proofs/) and the tests in
--| `Aoc.Year2024.Day20.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day20
import Aoc.Common (Direction, Position, cells, directions, onlyCell, positionsWhere)
import Std (And, Bool, Eq, Exists, Fail, Graph, IO, List, Map, Nat, Option, Parse, Set, Text, Void)
import Std.Parse (grid, pick)

--| The least saving counted is 100 picoseconds, unless the arguments give
--| another: `-- 50` for the example.
def main(): {IO, Fail} () :=
  let threshold := thresholdFrom IO.args()
  let racetrack := parseRacetrack IO.readAll()
  IO.print "Part 1: ${solvePart1 threshold racetrack}"
  IO.print "Part 2: ${solvePart2 threshold racetrack}"

def thresholdFrom (args: List Text): {Fail} Nat :=
  let usage := "expected no arguments, or the least saving to count, such as `50`"
  match args with
    | [] => 100
    | [saving] => Fail.need saving.toNat usage
    | _ => Fail.fail usage

--| The track positions (S and E among them), the start and the end.
type Racetrack = { track: Set Position, start: Position, end: Position }

type Tile = | Wall | Track | Start | End

def tile(): {Parse} Tile := pick [("#", Wall), (".", Track), ("S", Start), ("E", End)]

--| One row of tiles per line, with one S and one E. A short row is walled
--| beyond its end.
def parseRacetrack (input: Text): {Fail} Racetrack :=
  let tiles := cells (Parse.all input (() => grid tile) |> .toList |> .map .toList)
  {
    track = positionsWhere tiles (!= Wall) |> .toSet,
    start = onlyCell tiles Start "S tile",
    end = onlyCell tiles End "E tile"
  }

-- Positions, directions and a step (none above the top row or left of
-- the left column) are the shared grid code's (`Aoc.Common`).

def Racetrack.isTrack (racetrack: Racetrack) (position: Position): Bool := racetrack.track.contains position

--| The position one step in `direction`, if it's track.
def Racetrack.move (racetrack: Racetrack) (position: Position) (direction: Direction): Option Position :=
  match position.step direction with
    | Some next => if racetrack.isTrack next then Some next else None
    | None => None

--| The track positions one step away, each taking one picosecond.
def Racetrack.edges (racetrack: Racetrack) (position: Position): List (Position, Nat) :=
  directions.filterMap (direction => racetrack.move position direction |> .map (next => (next, 1)))

--| Edges lead onto track.
theorem Racetrack.edgeOnTrack ∀ (racetrack: Racetrack) (position next: Position) (weight: Nat)
    (edge: (next, weight) ∈ racetrack.edges position):
    racetrack.isTrack next = True :=
  let found :=
    List.memFilterMapElim
      (direction => racetrack.move position direction |> .map (other => (other, 1)))
      (next, weight)
      directions
      edge
  Exists.elim
    (List.anyMember
      (direction => (racetrack.move position direction |> .map (other => (other, 1))) = Some (next, weight))
      directions
      found)
    (direction both =>
      match stepped: position.step direction with
        | None => Void.exfalso (Option.noneNotSome (next, weight) (And.right both))
        | Some ahead =>
          match onIt: racetrack.isTrack ahead with
            | False => Void.exfalso (Option.noneNotSome (next, weight) (And.right both))
            | True => rewrite <- Eq.cong Pair.fst (Option.someInjective (And.right both)) in onIt)

--| The track as a graph for std's search. Every step can be taken back, so
--| the same graph gives the times to the end.
def Racetrack.graph (racetrack: Racetrack): Graph Position := {
  edges = racetrack.edges,
  states = racetrack.track.toList,
  listed = position next weight edge =>
    Map.memKeysOfContains racetrack.track.items next (racetrack.edgeOnTrack position next weight edge)
}

--| The fewest picoseconds from the start to each track position.
def Racetrack.fromStart (racetrack: Racetrack): Map Position Nat := racetrack.graph.breadthFirst [racetrack.start]

--| The fewest picoseconds from each track position to the end.
def Racetrack.toEnd (racetrack: Racetrack): Map Position Nat := racetrack.graph.breadthFirst [racetrack.end]

--| The picoseconds from one position to another through walls: the
--| Manhattan distance.
def Position.distance (position other: Position): Nat :=
  position.row.absDiff other.row + position.column.absDiff other.column

--| Every position at most `length` picoseconds from `position` through
--| walls: a diamond, row by row.
def Position.diamond (position: Position) (length: Nat): List Position :=
  List.range (position.row - length) (position.row + length + 1)
    |> .flatMap (row =>
      let spare := length - row.absDiff position.row
      List.range (position.column - spare) (position.column + spare + 1)
        |> .map (column => ({ row, column }: Position)))

--| Whether a cheat from `start`, `before` picoseconds into the race, to `end`
--| makes the race at least `threshold` picoseconds shorter than `honest`:
--| the time to the start, the cheat, then the time from the end.
def savesFrom (toEnd: Map Position Nat) (honest threshold: Nat) (start: Position) (before: Nat) (end: Position): Bool :=
  match toEnd.get end with
    | Some after => before + start.distance end + after + threshold ≤ honest
    | None => False

--| How many cheats of up to `length` picoseconds from `start` save at least
--| `threshold`; none if the start can't be reached.
def cheatsFrom (fromStart toEnd: Map Position Nat) (honest length threshold: Nat) (start: Position): Nat :=
  match fromStart.get start with
    | Some before => start.diamond length |> .count (savesFrom toEnd honest threshold start before)
    | None => 0

--| How many cheats of up to `length` picoseconds save at least `threshold`.
def Racetrack.countCheats (racetrack: Racetrack) (length threshold: Nat): Nat :=
  let fromStart := racetrack.fromStart
  match fromStart.get racetrack.end with
    | Some honest => racetrack.track.toList |> .sumBy (cheatsFrom fromStart racetrack.toEnd honest length threshold)
    | None => 0

def solvePart1 (threshold: Nat) (racetrack: Racetrack): Nat := racetrack.countCheats 2 threshold

def solvePart2 (threshold: Nat) (racetrack: Racetrack): Nat := racetrack.countCheats 20 threshold
