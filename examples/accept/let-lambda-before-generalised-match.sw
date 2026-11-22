-- A lambda bound by `let` whose parameter has no written type, before a
-- `match` on an expression, used in one of its arms: generalising over the
-- expression doesn't wait for the parameter's type, which only the arm's
-- use works out (SW-873, SW-4590).

import Std (Bool, List, Nat)

type Box = { items: List Nat }

-- A membership, decided once the field's type is known.
def has (b: Box) (n: Nat): Bool :=
  let check := r => 3 ∈ r.items
  match n == 0 with
    | True => check b
    | False => False

-- The parameter's type is the argument's, on a `Nat` expression.
def same (b n: Nat): Nat :=
  let f := r => r
  match n % 2 with
    | 0 => f b
    | _ => 0

test "has" := has { items = [3] } 0 ∧ !has { items = [4] } 0 ∧ !has { items = [3] } 1

test "same" := same 5 4 == 5 ∧ same 5 3 == 0
