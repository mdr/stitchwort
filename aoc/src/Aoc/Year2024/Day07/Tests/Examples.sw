-- Day 7's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Year2024.Day07.main` doesn't check them.

namespace Aoc.Year2024.Day07.Tests
import Aoc.Year2024.Day07 (..)
import Aoc.Year2024.Day07.Spec (combinations, concatenate, couldPossiblyBeTrue, evaluate)
import Std (Fail, List, Nat, Result, Text)

def example: Text := """
  190: 10 19
  3267: 81 40 27
  83: 17 5
  156: 15 6
  7290: 6 8 6 15
  161011: 16 10 13
  192: 17 8 14
  21037: 9 7 18 13
  292: 11 6 16 20
  """

def parsed (input: Text): Result (List Equation) Text := Fail.toResult (() => parseEquations input)

def exampleEquations: List Equation := Fail.orElse [] (() => parseEquations example)

def addMultiply: List Operator := [Add, Multiply]

def allOperators: List Operator := [Add, Multiply, Concatenate]

def holds (operators: List Operator) (testValue: Nat) (numbers: List Nat): Bool := Equation.couldBeTrue { testValue, numbers } operators

test "example, part 1" := solvePart1 exampleEquations == 3749
test "example, part 2" := solvePart2 exampleEquations == 11387
test "example, which could be true with + and *" :=
  exampleEquations.map (.couldBeTrue addMultiply) == [True, True, False, False, False, False, False, False, True]
test "example, which could be true with ||" :=
  exampleEquations.map (.couldBeTrue allOperators) == [True, True, False, True, True, False, True, False, True]
test "example, the spec agrees" :=
  exampleEquations.all (equation =>
    equation.couldBeTrue addMultiply == couldPossiblyBeTrue addMultiply equation
      && equation.couldBeTrue allOperators == couldPossiblyBeTrue allOperators equation)

test "parse" := parsed "190: 10 19\n3: 3\n" ==
  Ok ([{ testValue = 190, numbers = [10, 19] }, { testValue = 3, numbers = [3] }]: List Equation)
test "parse without a final line break" := parsed "7: 1 2 3" == Ok ([{ testValue = 7, numbers = [1, 2, 3] }]: List Equation)
test "no numbers" := parsed "190:\n" == Err "line 1, column 5: expected a number, got the end of the line"
test "no colon" := parsed "190 10 19\n" == Err "line 1, column 4: expected ':', got ' '"
test "a bad number" := parsed "1: 2\n3: 4 x\n" == Err "line 2, column 6: expected a number or the end of the line, got 'x'"

test "one number: it is the test value" := holds allOperators 5 [5] && !(holds allOperators 6 [5])
test "no operators: only one number" := holds [] 5 [5] && !(holds [] 5 [2, 3])
test "left to right, not by precedence" := holds addMultiply 20 [2, 3, 4] && !(holds addMultiply 14 [2, 3, 4])
test "numbers aren't rearranged" := !(holds [Concatenate] 21 [1, 2])
test "times 0" := holds addMultiply 0 [7, 0] && holds addMultiply 0 [7, 3, 0] && !(holds [Multiply] 1 [7, 0])
test "times 0, then more" := holds addMultiply 5 [7, 0, 5] && !(holds [Add] 5 [7, 0, 5])
test "plus 0" := holds [Add] 7 [7, 0]
test "concatenate 0" := holds [Concatenate] 70 [7, 0] && holds [Concatenate] 5 [0, 5]
test "concatenate a number with zeros" := holds [Concatenate] 12100 [12, 100] && !(holds [Concatenate] 1200 [12, 100])
test "concatenate then multiply" := holds allOperators 7290 [6, 8, 6, 15]
test "a large test value" := holds allOperators 12863083290 [9, 72, 13, 7, 5, 3, 4, 2, 264, 90]

test "concatenate" := concatenate 12 345 == 12345 && concatenate 0 5 == 5 && concatenate 5 0 == 50
test "place value" := [placeValue 0, placeValue 9, placeValue 10, placeValue 345] == [10, 10, 100, 1000]
test "evaluate, left to right" := evaluate 81 [(Add, 40), (Multiply, 27)] == 3267
test "combinations" := combinations addMultiply 2 == [[Add, Add], [Add, Multiply], [Multiply, Add], [Multiply, Multiply]]
test "combinations of none" := combinations allOperators 0 == [[]] && combinations [] 2 == []
