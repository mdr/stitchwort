-- A `let`-bound lambda that performs nothing is a pure function, even when
-- its body calls an effect-polymorphic function (`List.filter`) and it's
-- called in a body that may fail: its calls are plain calls.

import Std (Fail, List, Nat, Set)

type Found = { count: Nat, others: Set Nat }

def parseDigit (n: Nat): {Fail} Nat :=
  Fail.ensure (n < 10) "expected a digit, got ${n}"
  n

-- Matching on the lambda's result, with another call in a record field.
def onlyOne (input: List Nat) (wanted: Nat): {Fail} Found :=
  let digits := input.map parseDigit
  let equalTo := (target: Nat) => digits.filter (digit => digit == target)
  match equalTo wanted with
    | [_] => { count = 1, others = Set.fromList (equalTo (wanted + 1)) }
    | [] => Fail.fail "none"
    | _ => Fail.fail "several"

-- The same call written out where the lambda's call stood.
def onlyOneInline (input: List Nat) (wanted: Nat): {Fail} Found :=
  let digits := input.map parseDigit
  { count = 1, others = Set.fromList (digits.filter (digit => digit == wanted + 1)) }

def applyPure (f: Nat → List Nat) (n: Nat): List Nat := f n

-- Called in the failing body, then passed where a pure function is wanted.
def callThenPass (input: List Nat): {Fail} (List Nat) :=
  let digits := input.map parseDigit
  let equalTo := (target: Nat) => digits.filter (digit => digit == target)
  let ones := equalTo 1
  ones ++ applyPure equalTo 2

test "one match" := Fail.toResult (() => onlyOne [1, 2, 2] 1) |> .isOk
test "inline" := Fail.toResult (() => onlyOneInline [1, 2] 1) |> .isOk
test "call then pass" := Fail.toResult (() => callThenPass [1, 2, 1]) == Ok [1, 1, 2]
