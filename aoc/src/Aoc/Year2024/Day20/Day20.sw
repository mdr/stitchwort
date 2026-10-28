-- Advent of Code 2024, day 20: a racetrack of track and walls from S to E.
-- Once in a race a program may cheat, passing through walls for a few
-- picoseconds and ending back on track. Part 1 counts the cheats of up to 2
-- picoseconds that save at least 100 picoseconds; part 2 those of up to 20.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day20.main < inputs/2024/day20.txt
--   $ cd aoc && stitchwort run Aoc.Year2024.Day20.main -- 50 < examples/2024/day20.txt
--
-- The proofs are in `Aoc.Year2024.Day20.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day20.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day20
import Aoc.Year2024.Day16 (Graph)
import Std (Bool, Fail, IO, List, Map, Nat, Option, Parse, Set, Text)
import Std.Parse (grid, pick)

-- The least saving counted is 100 picoseconds, unless the arguments give
-- another: `-- 50` for the example.
def main(): {IO, Fail} () :=
  let threshold := thresholdFrom IO.args()
  let racetrack := parseRacetrack IO.readAll()
  IO.print "Part 1: ${solvePart1 threshold racetrack}"
  IO.print "Part 2: ${solvePart2 threshold racetrack}"

def thresholdFrom (args: List Text): {Fail} Nat :=
  let usage := "expected no arguments, or the least saving to count, such as `50`"
  match args with
    | Nil => 100
    | Cons saving Nil =>
      match saving.toNat with
        | Some least => least
        | None => Fail.fail usage
    | _ => Fail.fail usage

type Position = { row: Nat, column: Nat }

-- The track positions (S and E among them), the start and the end.
type Racetrack = { track: Set Position, start: Position, end: Position }

type Tile =
  | Wall
  | Track
  | Start
  | End

def tile(): {Parse} Tile := pick [("#", Wall), (".", Track), ("S", Start), ("E", End)]

-- The one position holding `wanted`.
def onlyTile (tiles: List (Position, Tile)) (wanted: Tile) (name: Text): {Fail} Position :=
  match tiles.filter (entry => entry.snd == wanted) |> .map (entry => entry.fst) with
    | Cons position Nil => position
    | Nil => Fail.fail "no ${name} tile"
    | _ => Fail.fail "more than one ${name} tile"

-- One row of tiles per line, with one S and one E.
def parseRacetrack (input: Text): {Fail} Racetrack :=
  let tiles :=
    Parse.all input (() => grid tile)
      |> .gridCells
      |> .map ((((row, column), kind)) => (({ row, column }: Position), kind))
  {
    track = tiles.filter (entry => entry.snd != Wall) |> .map (entry => entry.fst) |> Set.fromList,
    start = onlyTile tiles Start "S",
    end = onlyTile tiles End "E"
  }

type Direction =
  | Up
  | Down
  | Left
  | Right

def directions: List Direction := [Up, Down, Left, Right]

-- The position one step in `direction`; none above the top row or left of
-- the left column.
def Position.step (position: Position): Direction → Option Position
  | Down => Some ({ position | row = Succ position.row })
  | Right => Some ({ position | column = Succ position.column })
  | Up =>
    match position.row with
      | Zero => None
      | Succ above => Some ({ position | row = above })
  | Left =>
    match position.column with
      | Zero => None
      | Succ before => Some ({ position | column = before })

def Racetrack.isTrack (racetrack: Racetrack) (position: Position): Bool := racetrack.track.contains position

-- The position one step in `direction`, if it's track.
def Racetrack.move (racetrack: Racetrack) (position: Position) (direction: Direction): Option Position :=
  match position.step direction with
    | Some next => if racetrack.isTrack next then Some next else None
    | None => None

-- The track positions one step away, each taking one picosecond.
def Racetrack.edges (racetrack: Racetrack) (position: Position): List (Position, Nat) :=
  directions.filterMap (direction => racetrack.move position direction |> .map (next => (next, 1)))

-- The track as a graph for day 16's search. Every step can be taken back,
-- so the same graph gives the times to the end.
def Racetrack.graph (racetrack: Racetrack): Graph Position := {
  edges = racetrack.edges,
  within = racetrack.isTrack,
  states = racetrack.track.toList,
  listed = position onTrack => Map.memKeysOfContains racetrack.track.items position onTrack
}

-- The fewest picoseconds from the start to each track position.
def Racetrack.fromStart (racetrack: Racetrack): Map Position Nat := racetrack.graph.distances [(racetrack.start, 0)]

-- The fewest picoseconds from each track position to the end.
def Racetrack.toEnd (racetrack: Racetrack): Map Position Nat := racetrack.graph.distances [(racetrack.end, 0)]

-- The picoseconds from one position to another through walls: the
-- Manhattan distance.
def Position.distance (position: Position) (other: Position): Nat :=
  Nat.absDiff position.row other.row + Nat.absDiff position.column other.column

-- Every position at most `length` picoseconds from `position` through
-- walls: a diamond, row by row.
def Position.around (position: Position) (length: Nat): List Position :=
  List.between (position.row - length) (position.row + length)
    |> .flatMap (row =>
      let spare := length - Nat.absDiff row position.row
      List.between (position.column - spare) (position.column + spare) |> .map (column => ({ row, column }: Position)))

-- Whether a cheat from `start`, `before` picoseconds into the race, to `end`
-- makes the race at least `threshold` picoseconds shorter than `honest`:
-- the time to the start, the cheat, then the time from the end.
def savesFrom (toEnd: Map Position Nat) (honest: Nat) (threshold: Nat) (start: Position) (before: Nat) (end: Position): Bool :=
  match toEnd.get end with
    | Some after => before + start.distance end + after + threshold ≤ honest
    | None => False

-- How many cheats of up to `length` picoseconds from `start` save at least
-- `threshold`; none if the start can't be reached.
def cheatsFrom (fromStart: Map Position Nat) (toEnd: Map Position Nat) (honest: Nat) (length: Nat) (threshold: Nat) (start: Position): Nat :=
  match fromStart.get start with
    | Some before => start.around length |> .count (savesFrom toEnd honest threshold start before)
    | None => 0

-- How many cheats of up to `length` picoseconds save at least `threshold`.
def countCheats (length: Nat) (threshold: Nat) (racetrack: Racetrack): Nat :=
  let fromStart := racetrack.fromStart
  match fromStart.get racetrack.end with
    | Some honest => racetrack.track.toList |> .sumBy (cheatsFrom fromStart racetrack.toEnd honest length threshold)
    | None => 0

def solvePart1 (threshold: Nat) (racetrack: Racetrack): Nat := countCheats 2 threshold racetrack

def solvePart2 (threshold: Nat) (racetrack: Racetrack): Nat := countCheats 20 threshold racetrack
