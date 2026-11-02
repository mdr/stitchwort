-- expect-error: E-NO-EQUATION
-- Arm 3 comes after an arm that overlaps it, so its body is elaborated once
-- for each case of arm 2's patterns, and its lifted `match` captures the
-- refined variables: no one right side states the arm in its own
-- variables, so `explode.eq3` isn't generated
-- (docs/proposals/function-equations.md, stage 1a). Its branches'
-- equations, `explode.eq3.some` and `explode.eq3.none`, are (SW-1071).
import Std (Nat, Option)

type Number =
  | Regular (value: Nat)
  | Pair (left: Number) (right: Number)

def explode (depth: Nat): Number → Option Nat
  | Regular _ => None
  | Pair (Regular a) (Regular b) => if 4 ≤ depth then Some (a + b) else None
  | Pair left right =>
    match explode (depth + 1) left with
      | Some n => Some n
      | None => explode (depth + 1) right

theorem general (depth: Nat) (left: Number) (right: Number):
    explode depth (Pair left right) = explode depth (Pair left right) :=
  explode.eq3 depth left right
