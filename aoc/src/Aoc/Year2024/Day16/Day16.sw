-- Advent of Code 2024, day 16: a maze of walls and open tiles. A reindeer
-- starts on S facing east; moving forward one tile costs 1 point and
-- turning 90 degrees costs 1000. Part 1 is the lowest score from S to E;
-- part 2 counts the tiles on at least one path with that score.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day16.main < examples/2024/day16.txt
--
-- The proofs are in `Aoc.Year2024.Day16.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day16.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day16
import Std (Bool, DecEq, Eq, Exists, Fail, Graph, IO, List, Map, Nat, Option, Parse, Set, Text, Void)
import Std.Parse (char)

def main(): {IO, Fail} () :=
  let maze := parseMaze IO.readAll()
  let fromStart := maze.fromStart
  IO.print "Part 1: ${part1From maze fromStart}"
  IO.print "Part 2: ${part2From maze fromStart}"

type Position = { row: Nat, column: Nat }

-- The open tiles (S, E and `.`), the start and the end.
type Maze = { openTiles: Set Position, start: Position, end: Position }

type Tile =
  | Wall
  | Floor
  | Start
  | End

def tile(): {Parse} Tile :=
  Parse.pick [("#", Wall), (".", Floor), ("S", Start), ("E", End)]

-- The one position holding `wanted`.
def onlyTile (tiles: List (Position, Tile)) (wanted: Tile) (name: Text): {Fail} Position :=
  match tiles.filter (entry => entry.snd == wanted) |> .map (entry => entry.fst) with
    | Cons position Nil => position
    | Nil => Fail.fail "no ${name} tile"
    | _ => Fail.fail "more than one ${name} tile"

-- One row per line, all as long as the first, with one S and one E.
def parseMaze (input: Text): {Fail} Maze :=
  let rows := Parse.all input (() => Parse.grid tile)
  let width := rows.headOr [] |> .length
  rows.withIndex |> .forEach (((row, tiles)) =>
    Fail.ensure (tiles.length == width) "line ${row + 1}: expected ${width} tiles, as on the first line, got ${tiles.length}")
  let tiles :=
    rows.withIndex
      |> .flatMap (((row, line)) => line.withIndex |> .map (((column, kind)) => (({ row, column }: Position), kind)))
  {
    openTiles = tiles.filter (entry => entry.snd != Wall) |> .map (entry => entry.fst) |> Set.fromList,
    start = onlyTile tiles Start "S",
    end = onlyTile tiles End "E"
  }

type Direction =
  | East
  | South
  | West
  | North

def directions: List Direction := [East, South, West, North]

def Direction.clockwise: Direction → Direction
  | East => South
  | South => West
  | West => North
  | North => East

def Direction.counterclockwise: Direction → Direction
  | East => North
  | North => West
  | West => South
  | South => East

def Direction.opposite: Direction → Direction
  | East => West
  | West => East
  | North => South
  | South => North

-- The grid point one step in `direction`; none above row 0 or left of
-- column 0.
def Position.step (position: Position): Direction → Option Position
  | East => Some ({ position | column = Succ position.column })
  | South => Some ({ position | row = Succ position.row })
  | West =>
    match position.column with
      | Zero => None
      | Succ before => Some ({ position | column = before })
  | North =>
    match position.row with
      | Zero => None
      | Succ above => Some ({ position | row = above })

-- Where the reindeer is and which way it faces.
type Reindeer = { position: Position, facing: Direction }

def Maze.isOpen (maze: Maze) (position: Position): Bool := maze.openTiles.contains position

def Maze.holds (maze: Maze) (reindeer: Reindeer): Bool := maze.isOpen reindeer.position

-- Every way the reindeer can stand on an open tile.
def Maze.reindeer (maze: Maze): List Reindeer :=
  maze.openTiles.toList |> .flatMap (position => directions.map (facing => ({ position, facing }: Reindeer)))

def Reindeer.turned (reindeer: Reindeer) (facing: Direction): Reindeer := { reindeer | facing }

-- The reindeer one tile forward, if that tile is open.
def Maze.forward (maze: Maze) (reindeer: Reindeer): List Reindeer :=
  match reindeer.position.step reindeer.facing with
    | Some next => if maze.isOpen next then [{ reindeer | position = next }] else Nil
    | None => Nil

-- The reindeer one tile back, if that tile is open.
def Maze.backward (maze: Maze) (reindeer: Reindeer): List Reindeer :=
  match reindeer.position.step reindeer.facing.opposite with
    | Some previous => if maze.isOpen previous then [{ reindeer | position = previous }] else Nil
    | None => Nil

-- The two turns, each costing 1000.
def Reindeer.turns (reindeer: Reindeer): List (Reindeer, Nat) :=
  [(reindeer.turned reindeer.facing.clockwise, 1000), (reindeer.turned reindeer.facing.counterclockwise, 1000)]

-- What one move leads to, with its cost.
def Maze.after (maze: Maze) (reindeer: Reindeer): List (Reindeer, Nat) :=
  (maze.forward reindeer |> .map (next => (next, 1))) ++ reindeer.turns

-- What one move comes from, with its cost.
def Maze.before (maze: Maze) (reindeer: Reindeer): List (Reindeer, Nat) :=
  (maze.backward reindeer |> .map (previous => (previous, 1))) ++ reindeer.turns

-- The four ways to stand on the end tile.
def Maze.endReindeer (maze: Maze): List Reindeer := directions.map (facing => ({ position = maze.end, facing }: Reindeer))

def Maze.startReindeer (maze: Maze): Reindeer := { position = maze.start, facing = East }

theorem directionsComplete: (facing: Direction) → facing ∈ directions
  | East => Inl rfl
  | South => Inr (Inl rfl)
  | West => Inr (Inr (Inl rfl))
  | North => Inr (Inr (Inr (Inl rfl)))

-- A way of standing on an open tile is on the list.
theorem Maze.holdsListed (maze: Maze): (reindeer: Reindeer) → maze.holds reindeer = True → reindeer ∈ maze.reindeer
  | { position, facing }, holds =>
    List.memFlatMapIntro (place => directions.map (way => ({ position = place, facing = way }: Reindeer))) position
      ({ position, facing }: Reindeer) maze.openTiles.toList (Map.memKeysOfContains maze.openTiles.items position holds)
      (List.memMap directions facing (directionsComplete facing) (way => ({ position, facing = way }: Reindeer)))

-- What `forward` gives stands on an open tile...
theorem Maze.forwardHolds (maze: Maze): (reindeer: Reindeer) → (next: Reindeer) → next ∈ maze.forward reindeer → maze.holds next = True
  | { position, facing }, next, member =>
    match stepped: position.step facing with
      | None => Void.exfalso member
      | Some ahead =>
        match open: maze.isOpen ahead with
          | False => Void.exfalso member
          | True =>
            match member with
              | Inl here => rewrite <- here in open
              | Inr none => Void.exfalso none

-- ...and so does what `backward` gives.
theorem Maze.backwardHolds (maze: Maze): (reindeer: Reindeer) → (next: Reindeer) → next ∈ maze.backward reindeer → maze.holds next = True
  | { position, facing }, next, member =>
    match stepped: position.step facing.opposite with
      | None => Void.exfalso member
      | Some behind =>
        match open: maze.isOpen behind with
          | False => Void.exfalso member
          | True =>
            match member with
              | Inl here => rewrite <- here in open
              | Inr none => Void.exfalso none

-- Steps onto open tiles and turns, from an open tile, end on one.
theorem Maze.stepsHold (maze: Maze) (moved: List Reindeer) (movedHold: (other: Reindeer) → other ∈ moved → maze.holds other = True):
    (reindeer: Reindeer) → maze.holds reindeer = True → (next: Reindeer) → (weight: Nat) →
      (next, weight) ∈ (moved.map (other => (other, 1))) ++ reindeer.turns → maze.holds next = True
  | { position, facing }, holds, next, weight, edge =>
    match List.memAppend (next, weight) _ _ edge with
      | Inl stepped =>
        Exists.elim (List.memMapElim (other => (other, 1)) (next, weight) moved stepped) (other both =>
          rewrite <- Eq.cong Pair.fst (And.right both) in movedHold other (And.left both))
      | Inr (Inl turn) => rewrite <- Eq.cong Pair.fst turn in holds
      | Inr (Inr (Inl turn)) => rewrite <- Eq.cong Pair.fst turn in holds
      | Inr (Inr (Inr none)) => Void.exfalso none

-- The moves out of a way of standing on an open tile, with their costs, or
-- into it if `backwards`; none from anywhere else.
def Maze.moves (maze: Maze) (backwards: Bool) (reindeer: Reindeer): List (Reindeer, Nat) :=
  if maze.holds reindeer then (if backwards then maze.before reindeer else maze.after reindeer) else Nil

-- The moves lead to ways of standing on open tiles.
theorem Maze.movesListed (maze: Maze) (backwards: Bool) (reindeer: Reindeer) (next: Reindeer) (weight: Nat)
    (edge: (next, weight) ∈ maze.moves backwards reindeer): next ∈ maze.reindeer :=
  match holds: maze.holds reindeer with
    | False => Void.exfalso edge
    | True =>
      match backwards with
        | True =>
          maze.holdsListed next
            (maze.stepsHold (maze.backward reindeer) (other member => maze.backwardHolds reindeer other member) reindeer holds next weight edge)
        | False =>
          maze.holdsListed next
            (maze.stepsHold (maze.forward reindeer) (other member => maze.forwardHolds reindeer other member) reindeer holds next weight edge)

-- The maze's moves forward and turns, between the ways to stand on its open
-- tiles; `backwards` follows each move the other way.
def Maze.graph (maze: Maze) (backwards: Bool): Graph Reindeer := {
  edges = maze.moves backwards,
  states = maze.reindeer,
  listed = reindeer next weight edge => maze.movesListed backwards reindeer next weight edge
}

-- The lowest score from the start to each reachable way of standing.
def Maze.fromStart (maze: Maze): Map Reindeer Nat := (maze.graph False).distances [(maze.startReindeer, 0)]

-- The lowest score from each way of standing to the end, facing any way.
def Maze.toEnd (maze: Maze): Map Reindeer Nat := (maze.graph True).distances (maze.endReindeer |> .map (reindeer => (reindeer, 0)))

-- The lowest score at the end, facing any way, from the start's scores.
def Maze.lowestScore (maze: Maze) (fromStart: Map Reindeer Nat): Option Nat := maze.endReindeer.filterMap fromStart.get |> .minimum

-- The tiles where the reindeer stands, some way, with its lowest scores
-- from the start and to the end adding up to `best`.
def tilesScoring (fromStart: Map Reindeer Nat) (toEnd: Map Reindeer Nat) (best: Nat): Set Position :=
  fromStart.toList
    |> .filter (entry => toEnd.get entry.fst |> .map (rest => entry.snd + rest == best) |> .getOrElse False)
    |> .map (entry => entry.fst.position)
    |> Set.fromList

-- The tiles on best paths, from the start's scores.
def Maze.bestTilesFrom (maze: Maze) (fromStart: Map Reindeer Nat): Set Position :=
  match maze.lowestScore fromStart with
    | Some best => tilesScoring fromStart maze.toEnd best
    | None => Set.empty

def Maze.bestTiles (maze: Maze): Set Position := maze.bestTilesFrom maze.fromStart

-- Each part from the start's scores, so `main` searches forward once.
def part1From (maze: Maze) (fromStart: Map Reindeer Nat): Nat := maze.lowestScore fromStart |> .getOrElse 0

def part2From (maze: Maze) (fromStart: Map Reindeer Nat): Nat := (maze.bestTilesFrom fromStart).size

def solvePart1 (maze: Maze): Nat := part1From maze maze.fromStart

def solvePart2 (maze: Maze): Nat := part2From maze maze.fromStart
