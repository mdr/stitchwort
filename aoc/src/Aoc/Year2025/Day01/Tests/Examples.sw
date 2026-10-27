-- Day 1's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Year2025.Day01.main` doesn't check them.

namespace Aoc.Year2025.Day01.Tests
import Aoc.Year2025.Day01 (..)
import Std (Fail, Int, List, Mod, Nat, Option, Text)

def example: List Text := """
  L68
  L30
  R48
  L5
  R60
  L55
  L1
  L99
  R14
  L82
  """.lines

def exampleTurns: List Turn := Fail.orElse [] (() => parseTurns example)

def parsed (lines: List Text): Result (List Turn) Text := Fail.toResult (() => parseTurns lines)

test "example" := (solvePart1 exampleTurns, solvePart2 exampleTurns) == (3, 6)
test "a line that isn't a turn" := parsed ["L68", "L30", "X12"] == Err "line 3: expected a turn like L68, got 'X12'"
test "a turn without a distance" := parsed ["R"] == Err "line 1: expected a turn like L68, got 'R'"
test "a blank line" := parsed ["L1", ""] == Err "line 2: expected a turn like L68, got ''"
test "spaces around a turn" := parsed [" L68", "R5 "] == Ok [Left 68, Right 5]

def after (t: Text): Option Nat := Turn.parseOption t |> .map (turn => startingDial.move turn |> .position |> .value)

test "parseOption" := after "L68" == Some 82
test "parse right" := after "R5" == Some 55
test "parseOption junk" := after "X5" == None

def zerosFrom (x: Int) (t: Turn): Nat := Dial.zerosDuring ({ position = Mod.ofInt x }: Dial 100) t

test "left past zero" := zerosFrom 10 (Left 40) == 1
test "left onto zero" := zerosFrom 20 (Left 20) == 1
test "right onto zero" := zerosFrom 0 (Right 100) == 1
test "left from zero" := zerosFrom 0 (Left 42) == 0
test "left a full turn from zero" := zerosFrom 0 (Left 200) == 2
