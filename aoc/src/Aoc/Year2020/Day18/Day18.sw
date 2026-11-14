--| Advent of Code 2020, day 18: Operation Order. Each line of the homework
--| is an expression of single numbers, `+`, `*` and parentheses, and the
--| answer is the sum of their values. The rules aren't the usual ones: in
--| part 1, `+` and `*` bind equally and are evaluated left to right; in
--| part 2, `+` binds tighter than `*`. Parentheses come first in both.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day18.main < inputs/2020/day18.txt
--|
--| One parser serves both parts: a `Precedence` lists the operators a
--| level each, loosest first, and each level is a left-to-right chain of
--| the next level's expressions. The parser builds the expression's tree,
--| brackets included, so the proofs can say which tree a line is. The
--| proofs, that the parser's tree is the only one the part's rules allow
--| for the line and that the answer is the sum of their values, are in
--| `Aoc.Year2020.Day18.Proofs` (Proofs/), and the tests in
--| `Aoc.Year2020.Day18.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2020.Day18
import Std (Fail, IO, List, Nat, Parse, Text)

def main(): {IO, Fail} () :=
  let input := IO.readAll()
  IO.print "Part 1: ${parseHomework input samePrecedence |> .sum}"
  IO.print "Part 2: ${parseHomework input additionFirst |> .sum}"

type Operator = | Plus | Times

--| How the homework writes an operator, with the spaces around it.
def Operator.spaced: Operator → Text
  | Plus => " + "
  | Times => " * "

def Operator.apply: Operator → Nat → Nat → Nat
  | Plus, left, right => left + right
  | Times, left, right => left * right

--| An expression as it is written: its parentheses are part of it.
type Expression =
  | Number (value: Nat)
  | Operation (operator: Operator) (left: Expression) (right: Expression)
  | Parenthesised (inner: Expression)

def Expression.value: Expression → Nat
  | Number value => value
  | Operation operator left right => operator.apply left.value right.value
  | Parenthesised inner => inner.value

--| The operators a level each, loosest first. Operators on one level are
--| evaluated left to right.
type Precedence = { levels: List (List Operator) }

--| Part 1: "addition and multiplication have the same precedence".
def samePrecedence: Precedence := { levels = [[Plus, Times]] }

--| Part 2: "addition is evaluated before multiplication".
def additionFirst: Precedence := { levels = [[Times], [Plus]] }

type Homework = { expressions: List Expression }

def Homework.sum (homework: Homework): Nat := homework.expressions.map .value |> .sum

-- The format

--| A number, or a whole expression in parentheses.
def operand (expression: () → {Parse} Expression): {Parse} Expression := Parse.oneOf [
  () =>
    let value := Parse.nat()
    Number value,
  () =>
    Parse.char '('
    let inner := expression()
    Parse.char ')'
    Parenthesised inner
]

def operator (operators: List Operator): {Parse} Operator :=
  Parse.pick (operators.map (operator => (operator.spaced, operator)))

--| The expression node an operator builds from its two sides.
def Operator.node (operator: Operator): Expression → Expression → Expression := left right =>
  Operation operator left right

--| `term`s joined by `operators`, grouped from the left.
def chain (operators: List Operator) (term: () → {Parse} Expression): {Parse} Expression :=
  Parse.chainLeft term (() => Operator.node (operator operators))

--| An expression whose loosest operators are the first of `levels`;
--| `expression` reads a whole one, for inside parentheses.
def level (expression: () → {Parse} Expression): List (List Operator) → {Parse} Expression
  | [] => operand expression
  | [operators, ..tighter] => chain operators (() => level expression tighter)

def Precedence.expression (precedence: Precedence): {Parse} Expression :=
  Parse.recursive (self => level self precedence.levels)

--| An expression a line, read by `precedence`'s rules.
def parseHomework (input: Text) (precedence: Precedence): {Fail} Homework :=
  { expressions = Parse.eachLine input (() => precedence.expression) }
