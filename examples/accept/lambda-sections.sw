-- Short forms of lambdas that don't name their argument
-- (docs/syntax.md, "Method sections" and "Operator sections"; design:
-- docs/proposals/anonymous-lambdas.md). Each is exactly the lambda written
-- out, the same term:
--   (.id == id)    is  x => x.id == id     a section that starts an
--                                          expression takes all of it
--   (== 'S')       is  x => x == 'S'       an operator with its left operand
--   (k +)          is  x => k + x          ... or its right operand missing
--   (&&)           is  a b => a && b       a bare operator is a function
-- `-` is not a section operator: `(- 1)` is the number.

import Std (List, Option)

type Booking = { id: Text, start: Nat }

def bookings: List Booking := [{ id = "a", start = 1 }, { id = "b", start = 5 }]

-- A section that starts an expression takes the whole expression.
def findBooking (id: Text) (bookings: List Booking): Option Booking :=
  bookings.find (.id == id)

test "a section to the end of the expression" :=
  (findBooking "b" bookings).map .start == Some 5

test "the same as the lambda" :=
  findBooking "a" bookings == bookings.find (booking => booking.id == "a")

def late (bookings: List Booking): List Booking := bookings.filter (.start + 1 > 3)

test "arithmetic after the section" := (late bookings).length == 1

-- After a pipe the section is the call it stands for: `xs |> .sum == 6` is
-- `xs.sum == 6`.
test "a section after a pipe" := ([1, 2, 3] |> .sum == 6)

-- A pipe inside the brackets continues the section.
def total (rows: List (List Nat)): Nat := rows.map (.map (x => x * 2) |> .sum) |> .sum

test "a pipe inside the section" := total [[1, 2], [3]] == 12

-- Operator sections: the missing operand is the argument.
def sIndex (line: List Char): Option Nat := line.findIndex (== 'S')

test "an operator section" := sIndex ['.', 'S', '.'] == Some 1

test "a comparison section" := [1, 5, 2, 8].filter (> 3) == [5, 8]

test "an arithmetic section" := [1, 2, 3].map (* 2) == [2, 4, 6]

test "text appended" := ["a", "b"].map (++ "!") == ["a!", "b!"]

-- With the right operand missing, the argument is the right operand.
test "a left operand given" := [1, 2, 3].map (10 +) == [11, 12, 13]

test "text prepended" := ["a", "b"].map ("<" ++) == ["<a", "<b"]

test "a factor on the left" := [1, 2, 3].map (2 *) == [2, 4, 6]

-- The logic notation works too.
test "membership section" := ['a', 'b', 'c'].filter (∈ ['a', 'c']) == ['a', 'c']

test "non-membership section" := ['a', 'b', 'c'].filter (∉ ['a', 'c']) == ['b']

test "a conjunction section" := [True, False].map (∧ False) == [False, False]

test "a disjunction section" := [True, False].map (∨ False) == [True, False]

theorem equivalenceSection (p: Prop): ((↔ p): Prop → Prop) = (q => q ↔ p) := rfl

-- A negative number is still a number.
test "minus is negation" := [1, 2, 3].map (x => x + (-1)) == [0, 1, 2]

-- A bare operator is a function of two arguments.
test "a bare operator" := [1, 2, 3].foldLeft 0 (+) == 6

test "a bare conjunction" := [True, True].foldLeft True (∧) == True

test "a bare subtraction" := ((-): Nat → Nat → Nat) 7 2 == 5
