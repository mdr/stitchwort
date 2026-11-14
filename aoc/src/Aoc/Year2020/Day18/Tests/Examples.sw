--| Day 18's puzzle examples, a line at a time and summed, the trees the
--| two parts make of one line, and lines the parser refuses.

namespace Aoc.Year2020.Day18.Tests
import Aoc.Year2020.Day18 (..)
import Aoc.Year2020.Day18 (Spec)
import Std (Fail, List, Nat, Result, Text)

def parsed (input: Text) (precedence: Precedence): Result Homework Text :=
  Fail.toResult (() => parseHomework input precedence)

def values (input: Text) (precedence: Precedence): Result (List Nat) Text :=
  (parsed input precedence).map (homework => homework.expressions.map .value)

def examples: Text := """
  1 + 2 * 3 + 4 * 5 + 6
  1 + (2 * 3) + (4 * (5 + 6))
  2 * 3 + (4 * 5)
  5 + (8 * 3 + 9 + 3 * 4 * 3)
  5 * 9 * (7 * 3 * 3 + 9 * 3 + (8 + 6 * 4))
  ((2 + 4 * 9) * (6 + 9 * 8 + 6) + 6) + 2 + 4 * 2
  """

test "the examples, part 1" := values examples samePrecedence == Ok [71, 51, 26, 437, 12240, 13632]
test "the examples, part 2" := values examples additionFirst == Ok [231, 51, 46, 1445, 669060, 23340]

test "the examples summed, part 1" := (parsed examples samePrecedence).map .sum == Ok 26457
test "the examples summed, part 2" := (parsed examples additionFirst).map .sum == Ok 694173

test "part 1 groups from the left" :=
  (parsed "1 + 2 * 3" samePrecedence).map .expressions
    == Ok [Operation Times (Operation Plus (Number 1) (Number 2)) (Number 3)]

test "part 2 adds first" :=
  (parsed "1 * 2 + 3" additionFirst).map .expressions
    == Ok [Operation Times (Number 1) (Operation Plus (Number 2) (Number 3))]

test "parentheses stay in the tree" :=
  (parsed "(1 + 2)" samePrecedence).map .expressions == Ok [Parenthesised (Operation Plus (Number 1) (Number 2))]

test "the spec's value agrees on the examples" := [samePrecedence, additionFirst].all (precedence =>
  (parsed examples precedence).map (homework =>
    homework.expressions.all (expression => expression.value == Spec.value expression))
    == Ok True)

test "numbers can have several digits" := values "12 * 10 + 1" additionFirst == Ok [132]
test "an operator needs a space either side" := not (parsed "1+2" samePrecedence).isOk
test "a parenthesis must close" := not (parsed "(1 + 2" samePrecedence).isOk
test "no spaces inside parentheses" := not (parsed "( 1 + 2 )" samePrecedence).isOk
test "only + and *" := not (parsed "1 - 2" samePrecedence).isOk
