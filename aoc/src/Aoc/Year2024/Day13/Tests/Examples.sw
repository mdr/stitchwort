-- Day 13's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Year2024.Day13.main` doesn't check them.

namespace Aoc.Year2024.Day13.Tests
import Aoc.Year2024.Day13 (..)
import Aoc.Year2024.Day13.Spec (correctedMachine, part1)
import Std (Fail, Int, List, Nat, Option, Result, Text)

def example: Text := """
  Button A: X+94, Y+34
  Button B: X+22, Y+67
  Prize: X=8400, Y=5400

  Button A: X+26, Y+66
  Button B: X+67, Y+21
  Prize: X=12748, Y=12176

  Button A: X+17, Y+86
  Button B: X+84, Y+37
  Prize: X=7870, Y=6450

  Button A: X+69, Y+23
  Button B: X+27, Y+71
  Prize: X=18641, Y=10279
  """

def parsed (input: Text): Result (List Machine) Text := Fail.toResult (() => parseMachines input)

def exampleMachines: List Machine := Fail.orElse [] (() => parseMachines example)

-- A machine from its buttons' and prize's coordinates.
def claw (ax: Int) (ay: Int) (bx: Int) (by: Int) (px: Int) (py: Int): Machine :=
  { buttonA = { x = ax, y = ay }, buttonB = { x = bx, y = by }, prize = { x = px, y = py } }

def part1Tokens (machine: Machine): Option Nat := machine.fewestTokensWithin 100

test "example, part 1" := solvePart1 exampleMachines == 480
test "example, part 1, each machine" := exampleMachines.map part1Tokens == [Some 280, None, Some 200, None]
test "example, the first machine's presses" := exampleMachines.map (machine => machine.wins 80 40) == [True, False, False, False]
test "example, the spec agrees" := part1 exampleMachines == 480
test "example, part 2" := solvePart2 exampleMachines == 875318608908
test "example, part 2, only the second and fourth machines" :=
  exampleMachines.map (machine => machine.corrected.fewestTokens.isSome) == [False, True, False, True]
test "example, many more than 100 presses" :=
  exampleMachines.all (machine => machine.corrected.fewestTokensWithin 100 == None)
test "the program's correction is the spec's" := exampleMachines.all (machine => machine.corrected == correctedMachine machine)

test "parse" :=
  parsed "Button A: X+1, Y+2\nButton B: X+3, Y+4\nPrize: X=5, Y=6\n" == Ok [claw 1 2 3 4 5 6]
test "parse two machines without a final line break" :=
  parsed "Button A: X+1, Y+2\nButton B: X+3, Y+4\nPrize: X=5, Y=6\n\nButton A: X+0, Y+0\nButton B: X+0, Y+0\nPrize: X=0, Y=0"
    == Ok [claw 1 2 3 4 5 6, claw 0 0 0 0 0 0]
test "a minus sign" :=
  parsed "Button A: X-1, Y+2\nButton B: X+3, Y+4\nPrize: X=5, Y=6\n"
    == Err "line 1, column 11: expected 'X+', got 'X-'"
test "a missing blank line" :=
  parsed "Button A: X+1, Y+2\nButton B: X+3, Y+4\nPrize: X=5, Y=6\nButton A: X+1, Y+2\n"
    == Err "line 4, column 1: expected a blank line or the end of the input, got 'B'"
test "a missing prize" := parsed "Button A: X+1, Y+2\nButton B: X+3, Y+4\n" == Err "line 3, column 1: expected 'Prize: ', got the end of the input"

-- One solution, but negative, not whole, or over 100 presses.
test "a negative solution" := (claw 2 1 1 2 1 5).fewestTokens == None && part1Tokens (claw 2 1 1 2 1 5) == None
test "a solution that isn't whole" := (claw 3 1 1 3 2 2).fewestTokens == None && part1Tokens (claw 3 1 1 3 2 2) == None
test "over 100 presses" := part1Tokens (claw 1 0 0 1 101 5) == None && (claw 1 0 0 1 101 5).fewestTokens == Some 308
test "exactly 100 presses" := part1Tokens (claw 1 0 0 1 100 100) == Some 400
test "the prize where the claw starts" := part1Tokens (claw 94 34 22 67 0 0) == Some 0 && (claw 94 34 22 67 0 0).fewestTokens == Some 0

-- Buttons along the same line: the determinant is 0, and there may be many
-- solutions.
def collinear: List Machine := [
  claw 1 1 2 2 10 10,
  claw 4 4 1 1 8 8,
  claw 5 5 2 2 11 11,
  claw 2 2 3 3 7 7,
  claw 6 4 3 2 21 14,
  claw 1 1 2 2 10 11,
  claw 0 0 2 2 4 4,
  claw 2 2 0 0 4 4,
  claw 0 0 0 0 0 0,
  claw 0 0 0 0 1 0,
  claw 3 0 7 0 20 0,
  claw 0 9 0 2 0 31
]

test "the same line: determinant 0" := collinear.all (machine => machine.determinant == 0)
test "the same line: cheapest" :=
  collinear.map .fewestTokens == [Some 5, Some 6, Some 6, Some 7, Some 7, None, Some 2, Some 6, Some 0, None, Some 8, Some 11]
test "the same line, part 1, by the spec" := collinear.all (machine => part1Tokens machine == Aoc.Year2024.Day13.Spec.fewestTokens machine)
test "the same line, no limit, against a search" := collinear.all (machine => machine.fewestTokens == machine.searchTokens 40)
test "the same line, B cheaper per step" := (claw 2 2 1 1 701 701).fewestTokens == Some 701
test "the same line, A cheaper per step" := (claw 70 70 1 1 700 700).fewestTokens == Some 30

test "edge cases, part 1, the spec agrees" :=
  [claw 2 1 1 2 1 5, claw 3 1 1 3 2 2, claw 1 0 0 1 101 5, claw 1 0 0 1 100 100, claw 94 34 22 67 0 0].all (machine =>
    part1Tokens machine == Aoc.Year2024.Day13.Spec.fewestTokens machine)
