-- Day 7 as the puzzle states it. The proofs (Proofs/) show the program
-- computes these, for every list of equations.

namespace Aoc.Year2024.Day07.Spec
import Aoc.Year2024.Day07 (..)
import Std (List, Nat)

-- "The concatenation operator (||) combines the digits from its left and
-- right inputs into a single number."
def concatenate (left: Nat) (right: Nat): Nat := Nat.fromDigits ((Nat.digits left).append (Nat.digits right))

-- What each operator does: "add (+) and multiply (*)", and concatenation.
def combine: Operator → Nat → Nat → Nat
  | Add, left, right => left + right
  | Multiply, left, right => left * right
  | Concatenate, left, right => concatenate left right

-- "Operators are always evaluated left-to-right, not according to precedence
-- rules": each operator combines the value so far with the next number.
def evaluate (first: Nat) (steps: List (Operator, Nat)): Nat :=
  steps.foldLeft first (value step => combine step.fst value step.snd)

-- "Any combination of operators": every list of `count` operators from
-- `operators`.
def combinations (operators: List Operator): Nat → List (List Operator)
  | Zero => [[]]
  | Succ count => operators.flatMap (operator => combinations operators count |> .map (Cons operator))

-- "Determine whether the remaining numbers can be combined with operators to
-- produce the test value": one operator between each pair of numbers, which
-- "cannot be rearranged".
def couldPossiblyBeTrue (operators: List Operator) (equation: Equation): Bool :=
  match equation.numbers with
    | Nil => False
    | Cons first rest =>
      combinations operators rest.length |> .any (chosen => evaluate first (chosen.zip rest) == equation.testValue)

-- "The total calibration result, which is the sum of the test values from
-- just the equations that could possibly be true."
def totalCalibrationResult (operators: List Operator) (equations: List Equation): Nat :=
  equations.filter (couldPossiblyBeTrue operators) |> .sumBy (equation => equation.testValue)

-- Part 1: "two different types of operators: add (+) and multiply (*)".
def part1 (equations: List Equation): Nat := totalCalibrationResult [Add, Multiply] equations

-- Part 2: "a third type of operator", concatenation.
def part2 (equations: List Equation): Nat := totalCalibrationResult [Add, Multiply, Concatenate] equations
