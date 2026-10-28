-- Advent of Code 2024, day 7: calibration equations, one per line, a test
-- value and the numbers that should make it ("3267: 81 40 27"). Part 1 adds
-- up the test values of the equations that some choice of `+` and `*`
-- between the numbers, evaluated left to right, makes true; part 2 also
-- allows concatenation (`12 || 345` is 12345).
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day07.main < inputs/2024/day07.txt
--
-- The proofs are in `Aoc.Year2024.Day07.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day07.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day07
import Std (Fail, IO, List, Nat, Parse, Text)
import Std.Parse (char, many1, nat, token)

def main(): {IO, Fail} () :=
  let equations := parseEquations IO.readAll()
  IO.print "Part 1: ${solvePart1 equations}"
  IO.print "Part 2: ${solvePart2 equations}"

-- One line of the input: the test value, then the numbers in order.
type Equation = { testValue: Nat, numbers: List Nat }

type Operator =
  | Add
  | Multiply
  | Concatenate

-- "3267: 81 40 27".
def equationLine(): {Parse} Equation :=
  let testValue := nat()
  char ':'
  let numbers := many1 (() => token nat)
  { testValue, numbers }

-- One equation per line. A failure names the line and column.
def parseEquations (input: Text): {Fail} (List Equation) := Parse.eachLine input equationLine

-- 10 to the power of the number of digits of `number`: what concatenating
-- `number` onto the right multiplies the left side by.
def placeValue (number: Nat): Nat := Nat.pow 10 (Nat.digitCount number)

-- Whether the operators can join `first` and the numbers after it to make
-- `target`. The numbers after `first` come last one first: the last operator
-- is undone from `target`, leaving what the numbers before it must make.
def canMake (operators: List Operator) (first: Nat) (target: Nat): List Nat → Bool
  | Nil => target == first
  | Cons last earlier =>
    operators.any (operator =>
      match operator with
        | Add => last <= target && canMake operators first (target - last) earlier
        | Multiply =>
          if last != 0 then
            target % last == 0 && canMake operators first (target / last) earlier
          -- Anything times 0 is 0.
          else target == 0
        | Concatenate =>
          let place := placeValue last
          target % place == last && canMake operators first (target / place) earlier)

-- Whether some choice of the operators between the numbers makes the test
-- value.
def couldBeTrue (operators: List Operator) (equation: Equation): Bool :=
  match equation.numbers with
    | Nil => False
    | Cons first rest => canMake operators first equation.testValue rest.reverse

-- The sum of the test values of the equations that could be true.
def calibrationResult (operators: List Operator) (equations: List Equation): Nat :=
  equations.filter (couldBeTrue operators) |> .sumBy (equation => equation.testValue)

def solvePart1 (equations: List Equation): Nat := calibrationResult [Add, Multiply] equations

def solvePart2 (equations: List Equation): Nat := calibrationResult [Add, Multiply, Concatenate] equations
