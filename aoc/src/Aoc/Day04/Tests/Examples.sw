-- Day 4's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Day04.main` doesn't check them.

namespace Aoc.Day04.Tests
import Aoc.Day04 (..)
import Std (List, Nat, Option, Text)

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
