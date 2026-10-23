-- Day 4's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Day04.main` doesn't check them.

namespace Aoc.Day04.Tests
import Aoc.Day04 (..)
import Std (Bool, Fail, IO, List, Nat, Option, Pair, Result, Text)

def example: List Text := """
  ..@@.@@@@.
  @@@.@.@.@@
  @@@@@.@.@@
  @.@@@@..@.
  @@.@@@@.@@
  .@@@@@@@.@
  .@.@.@.@@@
  @.@@@.@@@@
  .@@@@@@@@.
  @.@.@@@.@.
  """.lines

-- Both answers for some lines, if they make a grid.
def answers (lines: List Text): Option (Nat, Nat) := Option.map (grid => (solvePart1 grid, solvePart2 grid)) (parseGrid lines)

test "example" := answers example == Some (13, 43)
test "lone roll" := answers ["@"] == Some (1, 1)
test "full square" := answers ["@@", "@@"] == Some (4, 4)
test "plus shape keeps its centre" := answers [".@.", "@@@", ".@."] == Some (4, 5)
test "no lines" := answers [] == Some (0, 0)
test "ragged" := answers ["@@", "@"] == None

test "rolls" := Option.map Grid.rolls (parseGrid example) == Some 71
test "one wide row" := answers ["@@@@@"] == Some (5, 5)
test "one narrow column" := answers ["@", "@", "@", "@", "@"] == Some (5, 5)

-- What `main` prints and how it ends, for some input lines.
def ran (lines: List Text): Pair (List Text) (Result Bool Text) :=
  IO.simulate lines (() => Result.map (u => True) (Fail.toResult main))

test "main on ragged lines" := ran ["@@", "@"] == MkPair [] (Err "expected lines that are all the same length, got a line of a different length")
test "main on a grid" := ran ["@"] == MkPair ["Part 1: 1", "Part 2: 1"] (Ok True)
