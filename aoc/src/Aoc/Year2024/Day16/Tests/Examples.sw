--| Day 16's tests: the examples from the puzzle and unit tests.
--
-- Kept apart from the program, so
-- `stitchwort run Aoc.Year2024.Day16.main` doesn't check them.

namespace Aoc.Year2024.Day16.Tests
import Aoc.Year2024.Day16 (..)
import Aoc.Year2024.Day16.Spec (Move, follow, score, startingReindeer)
import Aoc.Common (Direction, Heading, Position, headings)
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

--| Forward, a turn to the north, forward.
def oneTurn: Text := """
  ####
  ##E#
  #S.#
  ####
  """

def parsed (input: Text): Result Maze Text := Fail.toResult (() => parseMaze input)

--| A function of the parsed maze, or why it didn't parse: a parse failure fails the test.
def onMaze (input: Text) (f: Maze -> a): Result a Text := parsed input |> .map f

def at (row column: Nat): Position := { row, column }

test "first example, part 1" := onMaze first solvePart1 == Ok 7036
test "second example, part 1" := onMaze second solvePart1 == Ok 11048
test "first example, part 2" := onMaze first solvePart2 == Ok 45
test "second example, part 2" := onMaze second solvePart2 == Ok 64

test "start next to the end, facing it" := onMaze """
  ####
  #SE#
  ####
  """ (found => (solvePart1 found, solvePart2 found)) == Ok (1, 2)
test "start next to the end, facing away" := onMaze """
  ####
  #ES#
  ####
  """ (found => (solvePart1 found, solvePart2 found)) == Ok (2001, 2)
test "one turn" := onMaze oneTurn (found => (solvePart1 found, solvePart2 found)) == Ok (1002, 3)
test "a turn first" := onMaze """
  ###
  #E#
  #S#
  ###
  """ solvePart1 == Ok 1001
test "two equal paths round a pillar" := onMaze """
  #####
  #...#
  #S#E#
  #...#
  #####
  """ (found => (solvePart1 found, solvePart2 found)) == Ok (3004, 8)
test "no way to the end" := onMaze """
  #####
  #S#E#
  #####
  """ (found => (solvePart1 found, solvePart2 found)) == Ok (0, 0)
test "no way to the end fails in main's score" := parsed """
  #####
  #S#E#
  #####
  """ |> .flatMap (found => Fail.toResult (() => bestScore found found.fromStart))
  == Err "no path from the start to the end"
test "a reachable end scores" := parsed """
  ####
  #SE#
  ####
  """ |> .flatMap (found => Fail.toResult (() => bestScore found found.fromStart)) == Ok 1

test "the spec's moves on the one-turn maze" :=
  let moves: List Move := [Forward, Counterclockwise, Forward]
  onMaze oneTurn (turned =>
    follow turned (startingReindeer turned) moves |> .map (standings => standings.map (standing => standing.position)))
    == Ok (Some [at 2 1, at 2 2, at 2 2, at 1 2])
    && score moves == 1002
test "the spec's moves stop at a wall" :=
  onMaze oneTurn (turned => follow turned (startingReindeer turned) [Clockwise, Forward]) == Ok None

--| North is up, east a column on.
test "steps" :=
  let step := (position: Position) (heading: Heading) => position.step heading.toDirection
  step (at 0 0) North == None
    && step (at 0 0) West == None
    && step (at 0 0) East == Some (at 0 1)
    && step (at 0 0) South == Some (at 1 0)
    && step (at 3 4) North == Some (at 2 4)
    && step (at 3 4) West == Some (at 3 3)
test "turns" :=
  headings.map (facing => facing.turnRight) == [East, South, West, North]
    && headings.map (facing => facing.turnLeft) == [West, North, East, South]
test "headings and directions" := headings.map Heading.toDirection == [Up, Right, Down, Left]
test "moves out of the start of the one-turn maze" :=
  onMaze oneTurn (turned =>
    turned.after turned.startReindeer |> .map (edge => (edge.fst.position, edge.fst.facing, edge.snd)))
    == Ok [(at 2 2, East, 1), (at 2 1, South, 1000), (at 2 1, North, 1000)]
test "moves into the end of the one-turn maze" :=
  let end: Reindeer := { position = at 1 2, facing = North }
  onMaze oneTurn (turned => turned.before end |> .map (edge => (edge.fst.position, edge.fst.facing, edge.snd)))
    == Ok [(at 2 2, North, 1), (at 1 2, East, 1000), (at 1 2, West, 1000)]
test "scores from the start of the one-turn maze" :=
  onMaze oneTurn (turned =>
    turned.fromStart.toList |> .map (entry => (entry.fst.position, entry.fst.facing, entry.snd)))
    == Ok [
      (at 1 2, North, 1002),
      (at 1 2, East, 2002),
      (at 1 2, South, 3002),
      (at 1 2, West, 2002),
      (at 2 1, North, 1000),
      (at 2 1, East, 0),
      (at 2 1, South, 1000),
      (at 2 1, West, 2000),
      (at 2 2, North, 1001),
      (at 2 2, East, 1),
      (at 2 2, South, 1001),
      (at 2 2, West, 2001)
    ]
test "the best tiles of the first example" :=
  onMaze first (found => (found.bestTiles.contains (at 13 1), found.bestTiles.contains (at 1 1))) == Ok (True, False)

test "parse" := (parsed """
  ####
  #SE#
  ####
  """ |> .map (found => (found.start, found.end, found.openTiles.toList))) == Ok (at 1 1, at 1 2, [at 1 1, at 1 2])
test "parse without a final line break" := (parsed "####\n#SE#\n####" |> .map (found => found.openTiles.size)) == Ok 2
test "no start" := (parsed "####\n#.E#\n####\n" |> .map (found => ())) == Err "no S tile"
test "two ends" := (parsed "#####\n#SEE#\n#####\n" |> .map (found => ())) == Err "more than one E tile"
test "a bad tile" :=
  (parsed "####\n#Sx#\n####\n" |> .map (found => ()))
    == Err "line 2, column 3: expected '#', '.', 'S', 'E' or the end of the line, got 'x'"
test "a short row" :=
  (parsed "####\n#SE\n####\n" |> .map (found => ())) == Err "line 2: expected 4 cells, as on the first line, got 3"
