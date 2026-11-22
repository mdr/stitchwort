-- A `let`-bound lambda whose body is a proposition, applied as a `match`'s
-- scrutinee and decided there (SW-4588). The decision's proposition is the
-- call, `check n`; the `match` waits as a queued check, whose term passes
-- `check` on to the `match`'s helper as the lambda itself, and the
-- helper's call applies it: annotated with its type, so the kernel can
-- check that application.

import Std (Bool, List, Nat)

def hasThree (n: List Nat): Nat :=
  let check := (r: List Nat) => 3 ∈ r
  match check n with
    | True => 1
    | False => 0

test "a list with a 3" := hasThree [1, 3] == 1

test "a list without one" := hasThree [1, 2] == 0
