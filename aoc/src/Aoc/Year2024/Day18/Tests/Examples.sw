-- Day 18's tests: the example from the puzzle and unit tests. Kept apart
-- from the program, so `stitchwort run Aoc.Year2024.Day18.main` doesn't
-- check them.

namespace Aoc.Year2024.Day18.Tests
import Aoc.Year2024.Day18 (..)
import Aoc.Year2024.Day18.Spec (isSafe, walk)
import Std (Fail, List, Map, Nat, Option, Result, Set, Text)

def example: Text := """
  5,4
  4,2
  4,5
  3,0
  2,1
  6,3
  2,4
  1,5
  0,6
  3,3
  2,6
  5,1
  1,2
  5,5
  2,5
  6,5
  1,4
  0,4
  6,4
  1,1
  6,1
  1,0
  0,5
  1,6
  2,0
  """

def parsed (input: Text): Result (List Position) Text := Fail.toResult (() => parseBytes input)

def bytes (input: Text): List Position := Fail.orElse Nil (() => parseBytes input)

def at (x: Nat) (y: Nat): Position := { x, y }

test "example, part 1" := solvePart1 7 12 (bytes example) == Some 22
test "example, part 2" := solvePart2 7 (bytes example) == Some (at 6 1)

test "no bytes" := solvePart1 7 0 Nil == Some 12 && solvePart2 7 Nil == None
test "bytes that never cut the exit off" :=
  let aside := [at 3 3, at 1 0, at 5 2]
  solvePart1 7 3 aside == Some 12 && solvePart2 7 aside == None
test "the first byte lands on the start" :=
  let onStart := [at 0 0, at 3 3]
  solvePart1 7 1 onStart == None && solvePart2 7 onStart == Some (at 0 0)
test "the first byte lands on the exit" :=
  let onExit := [at 6 6, at 3 3]
  solvePart1 7 1 onExit == None && solvePart2 7 onExit == Some (at 6 6)
test "a wall across, completed by the last byte" :=
  let wall := [at 0 2, at 1 2, at 2 2]
  solvePart1 3 2 wall == Some 4 && solvePart2 3 wall == Some (at 2 2)
test "a winding path between two walls" :=
  let walls := [at 1 0, at 1 1, at 1 2, at 1 3, at 3 1, at 3 2, at 3 3, at 3 4]
  solvePart1 5 8 walls == Some 16 && solvePart2 5 walls == None
test "one position, the start and the exit" := solvePart1 1 0 Nil == Some 0
test "bytes outside the memory space change nothing" := solvePart1 3 1 [at 5 5] == Some 4 && solvePart2 3 [at 5 5] == None
test "a byte falling twice" := solvePart2 3 [at 1 1, at 1 1, at 0 1, at 1 0] == Some (at 1 0)

test "steps" :=
  (at 0 0).step Up == None && (at 0 0).step Left == None && (at 0 0).step Down == Some (at 0 1) && (at 0 0).step Right == Some (at 1 0)
    && (at 3 4).step Up == Some (at 3 3) && (at 3 4).step Left == Some (at 2 4)
test "safe positions" :=
  let memory := MemorySpace.after 7 (bytes example) 12
  memory.isSafe (at 0 0) && !memory.isSafe (at 5 4) && !memory.isSafe (at 7 0) && !memory.isSafe (at 0 7)
    && memory.isSafe (at 1 2)
test "edges out of the start" :=
  let memory := MemorySpace.after 3 [at 1 0] 1
  memory.edges (at 0 0) == [(at 0 1, 1)]
test "the spec's walk" :=
  walk 3 [at 1 1] (at 0 0) [Down, Down, Right, Right] == Some (at 2 2) && walk 3 [at 1 1] (at 0 0) [Right, Down] == None
    && walk 3 Nil (at 0 0) [Up] == None
test "the spec's safety" := isSafe 3 [at 1 1] (at 0 0) && !isSafe 3 [at 1 1] (at 1 1) && !isSafe 3 Nil (at 3 0)
test "fewest steps to each position" :=
  let memory := MemorySpace.after 2 [at 1 0] 1
  (memory.fromStart.toList |> .map (entry => (entry.fst, entry.snd))) == [(at 0 0, 0), (at 0 1, 1), (at 1 1, 2)]

test "binary search" :=
  firstBlocked (count => 5 ≤ count) 0 20 == 5 && firstBlocked (count => 1 ≤ count) 0 1 == 1 && firstBlocked (count => 19 ≤ count) 0 20 == 19
test "reachable" := reachable 7 (bytes example) 20 && !reachable 7 (bytes example) 21

test "parse" := parsed "5,4\n4,2\n" == Ok [at 5 4, at 4 2]
test "parse without a final line break" := parsed "5,4\n4,2" == Ok [at 5 4, at 4 2]
test "parse a large coordinate" := parsed "70,69\n" == Ok [at 70 69]
test "a missing comma" := (parsed "5 4\n" |> .map (found => ())) == Err "line 1, column 2: expected ',', got ' '"
test "a negative coordinate" := (parsed "-1,4\n" |> .map (found => ())) == Err "line 1, column 1: expected a number, got '-'"
