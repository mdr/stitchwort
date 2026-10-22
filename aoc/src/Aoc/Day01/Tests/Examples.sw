-- Day 1's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Day01.main` doesn't check them.

namespace Aoc.Day01.Tests
import Aoc.Day01 (..)
import Std (Int, List, Mod, Nat, Option, Text)

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

test "example" := (solvePart1 (parseTurns example), solvePart2 (parseTurns example)) == (3, 6)

def after (t: Text): Option Nat := (Turn.parse t).map (turn => (move startingDial turn).value)

test "parse" := after "L68" == Some 82
test "parse right" := after "R5" == Some 55
test "parse junk" := after "X5" == None

def zerosFrom (x: Int) (t: Turn): Nat := zerosDuring (Mod.ofInt x: Mod 100) t

test "left past zero" := zerosFrom 10 (Left 40) == 1
test "left onto zero" := zerosFrom 20 (Left 20) == 1
test "right onto zero" := zerosFrom 0 (Right 100) == 1
test "left from zero" := zerosFrom 0 (Left 42) == 0
test "left a full turn from zero" := zerosFrom 0 (Left 200) == 2
