--| Day 1's tests: the example from the puzzle and unit tests.
--
-- Kept apart from the program, so `stitchwort run Aoc.Year2025.Day01.main`
-- doesn't check them.

namespace Aoc.Year2025.Day01.Tests
import Aoc.Year2025.Day01 (..)
import Std (Fail, Int, List, Mod, Nat, Option, Parse, Result, Text)

def example: Text := """
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
  """

def parsed (input: Text): Result (List Turn) Text := Fail.toResult (() => parseTurns input)

def exampleTurns: Result (List Turn) Text := parsed example

test "example" := exampleTurns.map (turns => (solvePart1 turns, solvePart2 turns)) == Ok (3, 6)
test "a line that isn't a turn" := parsed """
  L68
  L30
  X12""" == Err "line 3, column 1: expected a turn like L68, got 'X'"
test "a turn without a distance" := parsed "R" == Err "line 1, column 2: expected a number, got the end of the line"
test "a blank line" := parsed "L1\n\n" == Err "line 2, column 1: expected a turn like L68, got the end of the line"
test "spaces around a turn" := parsed """
   L68
  R5 
  """ == Ok [Left 68, Right 5]

--| Where one turn, read from `line`, leaves the starting dial.
def after (line: Text): Option Nat :=
  Fail.toOption (() => Parse.line line turn) |> .map (turn => Dial.start.move turn |> .position |> .value)

test "turn" := after "L68" == Some 82
test "turn right" := after "R5" == Some 55
test "turn junk" := after "X5" == None

def zerosFrom (x: Int) (t: Turn): Nat := Dial.zerosDuring ({ position = Mod.ofInt x }: Dial 100) t

test "left past zero" := zerosFrom 10 (Left 40) == 1
test "left onto zero" := zerosFrom 20 (Left 20) == 1
test "right onto zero" := zerosFrom 0 (Right 100) == 1
test "left from zero" := zerosFrom 0 (Left 42) == 0
test "left a full turn from zero" := zerosFrom 0 (Left 200) == 2
