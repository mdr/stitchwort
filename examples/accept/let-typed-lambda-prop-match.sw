-- A `let`-bound lambda with a written type, whose body is a proposition,
-- decided as a `match`'s scrutinee: the typed twin of
-- `let-lambda-prop-match.sw` (SW-4598). The typed `let` checks its value
-- against the type, so the value is a bare lambda, not an annotated one.

import Std (Bool, List, Nat)

def hasThree (n: List Nat): Nat :=
  let check: List Nat → Prop := r => 3 ∈ r
  match check n with
    | True => 1
    | False => 0

test "a list with a 3" := hasThree [1, 3] == 1

test "a list without one" := hasThree [1, 2] == 0
