-- Day 16's tests: the examples from the puzzle and unit tests. Kept apart
-- from the program, so `stitchwort run Aoc.Year2024.Day16.main` doesn't
-- check them.

namespace Aoc.Year2024.Day16.Tests
import Aoc.Year2024.Day16 (..)
import Aoc.Year2024.Day16.Spec (Move, follow, score, startingReindeer)
import Std (Fail, List, Map, Nat, Option, Result, Set, Text)

def first: Text := """
  ###############
  #.......#....E#
  #.#.###.#.###.#
  #.....#.#...#.#
  #.###.#####.#.#
  #.#.#.......#.#
  #.#.#####.###.#
  #...........#.#
  ###.#.#####.#.#
  #...#.....#.#.#
  #.#.#.###.#.#.#
  #.....#...#.#.#
  #.###.#.#.#.#.#
  #S..#.....#...#
  ###############
  """

def second: Text := """
  #################
  #...#...#...#..E#
  #.#.#.#.#.#.#.#.#
  #.#.#.#...#...#.#
  #.#.#.#.###.#.#.#
  #...#.#.#.....#.#
  #.#.#.#.#.#####.#
  #.#...#.#.#.....#
  #.#.#####.#.###.#
  #.#.#.......#...#
  #.#.###.#####.###
  #.#.#...#.....#.#
  #.#.#.#####.###.#
  #.#.#.........#.#
  #.#.#.#########.#
  #S#.............#
  #################
  """

-- Forward, a turn to the north, forward.
def oneTurn: Text := """
  ####
  ##E#
  #S.#
  ####
  """

def parsed (input: Text): Result Maze Text := Fail.toResult (() => parseMaze input)

def maze (input: Text): Maze := Fail.orElse { openTiles = Set.empty, start = at 0 0, end = at 0 0 } (() => parseMaze input)

def at (row: Nat) (column: Nat): Position := { row, column }

test "first example, part 1" := solvePart1 (maze first) == 7036
test "second example, part 1" := solvePart1 (maze second) == 11048
test "first example, part 2" := solvePart2 (maze first) == 45
test "second example, part 2" := solvePart2 (maze second) == 64

test "start next to the end, facing it" :=
  let nextTo := maze "####\n#SE#\n####\n"
  solvePart1 nextTo == 1 && solvePart2 nextTo == 2
test "start next to the end, facing away" :=
  let behind := maze "####\n#ES#\n####\n"
  solvePart1 behind == 2001 && solvePart2 behind == 2
test "one turn" := solvePart1 (maze oneTurn) == 1002 && solvePart2 (maze oneTurn) == 3
test "a turn first" := solvePart1 (maze "###\n#E#\n#S#\n###\n") == 1001
test "two equal paths round a pillar" :=
  let loop := maze "#####\n#...#\n#S#E#\n#...#\n#####\n"
  solvePart1 loop == 3004 && solvePart2 loop == 8
test "no way to the end" :=
  let walled := maze "#####\n#S#E#\n#####\n"
  solvePart1 walled == 0 && solvePart2 walled == 0

test "the spec's moves on the one-turn maze" :=
  let turned := maze oneTurn
  let moves: List Move := [Forward, Counterclockwise, Forward]
  (follow turned (startingReindeer turned) moves |> .map (standings => standings.map (standing => standing.position)))
    == Some [at 2 1, at 2 2, at 2 2, at 1 2]
    && score moves == 1002
test "the spec's moves stop at a wall" :=
  let turned := maze oneTurn
  follow turned (startingReindeer turned) [Clockwise, Forward] == None

test "steps" :=
  (at 0 0).step North == None && (at 0 0).step West == None && (at 0 0).step East == Some (at 0 1) && (at 0 0).step South == Some (at 1 0)
    && (at 3 4).step North == Some (at 2 4) && (at 3 4).step West == Some (at 3 3)
test "turns" :=
  directions.map (facing => facing.clockwise) == [South, West, North, East]
    && directions.map (facing => facing.counterclockwise) == [North, East, South, West]
    && directions.map (facing => facing.opposite) == [West, North, East, South]
test "moves out of the start of the one-turn maze" :=
  let turned := maze oneTurn
  let start := turned.startReindeer
  (turned.after start |> .map (edge => (edge.fst.position, edge.fst.facing, edge.snd)))
    == [(at 2 2, East, 1), (at 2 1, South, 1000), (at 2 1, North, 1000)]
test "moves into the end of the one-turn maze" :=
  let turned := maze oneTurn
  let end: Reindeer := { position = at 1 2, facing = North }
  (turned.before end |> .map (edge => (edge.fst.position, edge.fst.facing, edge.snd)))
    == [(at 2 2, North, 1), (at 1 2, East, 1000), (at 1 2, West, 1000)]
test "scores from the start of the one-turn maze" :=
  let turned := maze oneTurn
  (turned.fromStart.toList |> .map (entry => (entry.fst.position, entry.fst.facing, entry.snd)))
    == [
      (at 1 2, East, 2002),
      (at 1 2, South, 3002),
      (at 1 2, West, 2002),
      (at 1 2, North, 1002),
      (at 2 1, East, 0),
      (at 2 1, South, 1000),
      (at 2 1, West, 2000),
      (at 2 1, North, 1000),
      (at 2 2, East, 1),
      (at 2 2, South, 1001),
      (at 2 2, West, 2001),
      (at 2 2, North, 1001)
    ]
test "the best tiles of the first example" := (maze first).bestTiles.contains (at 13 1) && !(maze first).bestTiles.contains (at 1 1)

test "parse" :=
  (parsed "####\n#SE#\n####\n" |> .map (found => (found.start, found.end, found.openTiles.toList))) == Ok (at 1 1, at 1 2, [at 1 1, at 1 2])
test "parse without a final line break" := (parsed "####\n#SE#\n####" |> .map (found => found.openTiles.size)) == Ok 2
test "no start" := (parsed "####\n#.E#\n####\n" |> .map (found => ())) == Err "no S tile"
test "two ends" := (parsed "#####\n#SEE#\n#####\n" |> .map (found => ())) == Err "more than one E tile"
test "a bad tile" := (parsed "####\n#Sx#\n####\n" |> .map (found => ())) == Err "line 2, column 3: expected '#' or '.' or 'S' or 'E' or the end of the line, got 'x'"
test "a short row" := (parsed "####\n#SE\n####\n" |> .map (found => ())) == Err "line 2: expected 4 tiles, as on the first line, got 3"
