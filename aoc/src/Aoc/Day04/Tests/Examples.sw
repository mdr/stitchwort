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
def answers (lines: List Text): Result (Nat, Nat) Text := Result.map (grid => (solvePart1 grid, solvePart2 grid)) (parseGrid lines)

test "example" := answers example == Ok (13, 43)
test "lone roll" := answers ["@"] == Ok (1, 1)
test "full square" := answers ["@@", "@@"] == Ok (4, 4)
test "plus shape keeps its centre" := answers [".@.", "@@@", ".@."] == Ok (4, 5)
test "no lines" := answers [] == Ok (0, 0)
test "ragged" := answers ["@@", "@"] == Err "expected lines that are all the same length, got a line of a different length"
test "a character that is neither @ nor ." := answers ["@.@", "@x."] == Err "line 2, column 2: expected '@' or '.', got 'x'"
test "a stray character before a ragged line" := answers ["@@", "@", "..#"] == Err "line 3, column 3: expected '@' or '.', got '#'"
test "stable from the start" := answers [".@@.", "@@@@", "@@@@", ".@@."] == Ok (0, 0)

test "rolls" := Result.map Grid.rolls (parseGrid example) == Ok 71
test "one wide row" := answers ["@@@@@"] == Ok (5, 5)
test "one narrow column" := answers ["@", "@", "@", "@", "@"] == Ok (5, 5)

-- What `main` prints and how it ends, for some input lines.
def ran (lines: List Text): Pair (List Text) (Result Bool Text) :=
  IO.simulate lines (() => Result.map (u => True) (Fail.toResult main))

test "main on ragged lines" := ran ["@@", "@"] == MkPair [] (Err "expected lines that are all the same length, got a line of a different length")
test "main on a stray character" := ran ["@?"] == MkPair [] (Err "line 1, column 2: expected '@' or '.', got '?'")
test "main on a grid" := ran ["@"] == MkPair ["Part 1: 1", "Part 2: 1"] (Ok True)
