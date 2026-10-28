-- Day 20's tests: the example from the puzzle and unit tests. Kept apart
-- from the program, so `stitchwort run Aoc.Year2024.Day20.main` doesn't
-- check them.

namespace Aoc.Year2024.Day20.Tests
import Aoc.Year2024.Day20 (..)
import Aoc.Year2024.Day20.Spec (race)
import Std (Bool, Fail, List, Map, Nat, Option, Result, Set, Text)

def example: Text := """
  ###############
  #...#...#.....#
  #.#.#.#.#.###.#
  #S#...#.#.#...#
  #######.#.#.###
  #######.#.#...#
  #######.#.###.#
  ###..E#...#...#
  ###.#######.###
  #...###...#...#
  #.#####.#.###.#
  #.#...#.#.#...#
  #.#.#.#.#.#.###
  #...#...#...###
  ###############
  """

def parsed (input: Text): Result Racetrack Text := Fail.toResult (() => parseRacetrack input)

def racetrack (input: Text): Racetrack := Fail.orElse ({ track = Set.empty, start = at 0 0, end = at 0 0 }) (() => parseRacetrack input)

def at (row: Nat) (column: Nat): Position := { row, column }

-- The cheats of up to `length` picoseconds saving exactly `saving`.
def savingExactly (length: Nat) (input: Text) (saving: Nat): Nat :=
  countCheats length saving (racetrack input) - countCheats length (saving + 1) (racetrack input)

-- "There are 14 cheats that save 2 picoseconds", and so on.
test "example, part 1, by saving" :=
  [(2, 14), (4, 14), (6, 2), (8, 4), (10, 2), (12, 3), (20, 1), (36, 1), (38, 1), (40, 1), (64, 1)]
    |> .all (((saving, cheats)) => savingExactly 2 example saving == cheats)
test "example, part 1, no other savings" := solvePart1 1 (racetrack example) == 44 && solvePart1 65 (racetrack example) == 0

-- "There are 32 cheats that save 50 picoseconds", and so on.
test "example, part 2, by saving" :=
  [(50, 32), (52, 31), (54, 29), (56, 39), (58, 25), (60, 23), (62, 20), (64, 19), (66, 12), (68, 14), (70, 12), (72, 22), (74, 4), (76, 3)]
    |> .all (((saving, cheats)) => savingExactly 20 example saving == cheats)
test "example, part 2, at least 50" := solvePart2 50 (racetrack example) == 285 && solvePart2 77 (racetrack example) == 0
test "example, at least 100" := solvePart1 100 (racetrack example) == 0 && solvePart2 100 (racetrack example) == 0
test "example, every cheat that saves time" := solvePart2 1 (racetrack example) == 3081

test "a straight track has nothing to cut" :=
  let straight := racetrack "#####\n#S.E#\n#####\n"
  solvePart1 1 straight == 0 && solvePart2 1 straight == 0
test "S next to E" := solvePart2 1 (racetrack "####\n#SE#\n####\n") == 0
test "no way from S to E" := solvePart2 0 (racetrack "#####\n#S#E#\n#####\n") == 0
test "a U-turn round one wall" :=
  let uTurn := "#####\n#S#E#\n#.#.#\n#...#\n#####\n"
  solvePart1 1 (racetrack uTurn) == 2 && savingExactly 2 uTurn 4 == 1 && savingExactly 2 uTurn 2 == 1 && solvePart2 1 (racetrack uTurn) == 4
test "a wall two thick needs three picoseconds" :=
  let thick := "######\n#S##E#\n#.##.#\n#....#\n######\n"
  countCheats 2 1 (racetrack thick) == 0 && countCheats 3 1 (racetrack thick) == 2 && savingExactly 3 thick 4 == 1
test "a short row is walled beyond its end" := solvePart1 1 (racetrack "#####\n#S#E#\n#.#.\n#...#\n#####\n") == 2

test "the search's times" :=
  let track := racetrack example
  track.fromStart.get track.end == Some 84 && track.toEnd.get track.start == Some 84 && track.fromStart.get (at 0 0) == None
    && track.fromStart.size == 85
test "steps" :=
  (at 0 0).step Up == None && (at 0 0).step Left == None && (at 0 0).step Down == Some (at 1 0) && (at 3 4).step Up == Some (at 2 4)
    && (at 3 4).step Left == Some (at 3 3) && (at 3 4).step Right == Some (at 3 5)
test "the spec's race" :=
  let uTurn := racetrack "#####\n#S#E#\n#.#.#\n#...#\n#####\n"
  race uTurn (at 1 1) [Down, Down, Right, Right, Up, Up] == Some (at 1 3) && race uTurn (at 1 1) [Right] == None
    && race uTurn (at 1 1) [Up] == None
test "distance" := (at 3 4).distance (at 1 7) == 5 && (at 1 7).distance (at 3 4) == 5 && (at 2 2).distance (at 2 2) == 0
test "around" :=
  (at 2 2).around 1 == [at 1 2, at 2 1, at 2 2, at 2 3, at 3 2] && (at 0 0).around 2 |> .length == 6 && (at 30 30).around 20 |> .length == 841 && (at 5 5).around 20 |> .length == 436
    && (at 4 4).around 0 == [at 4 4]

test "thresholds" :=
  Fail.toResult (() => thresholdFrom []) == Ok 100 && Fail.toResult (() => thresholdFrom ["50"]) == Ok 50
    && Fail.toResult (() => thresholdFrom ["fifty"]) == Err "expected no arguments, or the least saving to count, such as `50`"
    && Fail.toResult (() => thresholdFrom ["1", "2"]) == Err "expected no arguments, or the least saving to count, such as `50`"

test "parse" :=
  match parsed "#####\n#S.E#\n#####\n" with
    | Ok track => track.start == at 1 1 && track.end == at 1 3 && track.track.toList == [at 1 1, at 1 2, at 1 3]
    | Err message => False
test "parse without a final line break" := (parsed "#S.E#" |> .map (track => track.end)) == Ok (at 0 3)
test "no S" := (parsed "#..E#\n" |> .map (track => ())) == Err "no S tile"
test "two Es" := (parsed "#SEE#\n" |> .map (track => ())) == Err "more than one E tile"
test "an unknown tile" := (parsed "#S.x#\n" |> .map (track => ())) == Err "line 1, column 4: expected '#' or '.' or 'S' or 'E' or the end of the line, got 'x'"
