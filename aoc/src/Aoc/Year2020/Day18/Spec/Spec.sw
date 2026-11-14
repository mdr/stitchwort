--| Day 18 as the puzzle states it: how an expression is written, which
--| expression a line is under each part's rules, its value, and the
--| answer, the sum of the lines' values. Nothing is shared with the
--| program but the data types (`Operator`, `Expression`). The proofs
--| (Proofs/) show the program computes these.
--|
--| A part's rules are how strongly each operator binds. A line is the tree
--| written out, and the tree's shape follows the rules: an operation's
--| left side binds at least as strongly as its operator and its right side
--| more strongly, unless the side is a number or in parentheses. "Left to
--| right" is the left side allowed to bind equally, the right side not;
--| "parentheses can override this order" is a bracketed side allowed
--| anywhere. This is how a grammar with a level per strength reads, said
--| of the tree, and the same line is a different tree in each part.

namespace Aoc.Year2020.Day18.Spec
import Aoc.Year2020.Day18 (Expression, Operator)
import Std (Char, List, Nat, Parse, Text)

-- The format

def NumberWritten (read: List Char) (number: Nat): Prop :=
  read ≠ [] ∧ read.all Parse.isDigit = True ∧ number = Parse.digitsValue read

def symbol: Operator → Char
  | Plus => '+'
  | Times => '*'

--| "Each line in the homework contains an expression": `2 * 3 + (4 * 5)`,
--| an operator with a space on either side, parentheses with none inside.
def Written: Expression → List Char → Prop
  | Number value, read => NumberWritten read value
  | Operation operator left right, read =>
    ∃ (leftRead: List Char) => ∃ (rightRead: List Char) => read = leftRead ++ [' ', symbol operator, ' '] ++ rightRead
      ∧ Written left leftRead
      ∧ Written right rightRead
  | Parenthesised inner, read =>
    ∃ (innerRead: List Char) => read = ['('] ++ innerRead ++ [')'] ∧ Written inner innerRead

-- The rules

--| Part 1: "the operators have the same precedence, and are evaluated
--| left-to-right regardless of the order in which they appear".
def part1Strength (operator: Operator): Nat := 0

--| Part 2: "addition is evaluated before multiplication".
def part2Strength: Operator → Nat
  | Plus => 1
  | Times => 0

--| `expression`, as a side of an operation, binds at least `strength`
--| strongly: a number or parentheses always do.
def BindsAtLeast (strengthOf: Operator → Nat) (strength: Nat): Expression → Prop
  | Number value => Unit
  | Operation operator left right => strength ≤ strengthOf operator
  | Parenthesised inner => Unit

--| Every operation in `expression` has a left side binding at least as
--| strongly as its operator, and a right side binding more strongly.
def Follows (strengthOf: Operator → Nat): Expression → Prop
  | Number value => Unit
  | Operation operator left right =>
    BindsAtLeast strengthOf (strengthOf operator) left
      ∧ BindsAtLeast strengthOf (strengthOf operator + 1) right
      ∧ Follows strengthOf left
      ∧ Follows strengthOf right
  | Parenthesised inner => Follows strengthOf inner

--| `read` is `expression`, under the rules `strengthOf`.
def Means (strengthOf: Operator → Nat) (read: List Char) (expression: Expression): Prop :=
  Written expression read ∧ Follows strengthOf expression

-- The answer

--| "Evaluate the expression": `+` adds, `*` multiplies.
def value: Expression → Nat
  | Number value => value
  | Operation Plus left right => value left + value right
  | Operation Times left right => value left * value right
  | Parenthesised inner => value inner

--| "What do you get if you add up the resulting values?": the sum of the
--| values of the expressions the lines are, under the rules `strengthOf`.
def Answer (strengthOf: Operator → Nat) (input: Text) (answer: Nat): Prop :=
  ∃ (expressions: List Expression) => List.All2 (Means strengthOf) (input.lines.map Text.toList) expressions
    ∧ answer = (expressions.map value).sum

def Part1 (input: Text) (answer: Nat): Prop := Answer part1Strength input answer

def Part2 (input: Text) (answer: Nat): Prop := Answer part2Strength input answer
