-- A proposition where a `Bool` is expected is decided, but not before what
-- it holds is known (docs/proposals/postponement.md, D2035). `r.items`
-- waits for `r`'s type, which only `check b` fixes, so `3 ∈ r.items` can't
-- be decided where it's written: which procedure decides it depends on
-- what `r.items` is. The decision waits for the `.items` too, and is made
-- once `r` is known to be a `Box`.

import Std (Bool, List, Nat)

type Box = { items: List Nat }

def has (b: Box): Bool :=
  let check := r => 3 ∈ r.items
  check b

def annotated (b: Box): Bool :=
  let check := (r: Box) => 3 ∈ r.items
  check b

def empty (b: Box): Bool :=
  let check := r => r.items = []
  check b

test "has" := has { items = [1, 3] } == True

test "has not" := has { items = [1, 2] } == False

test "as annotated" := has { items = [3] } == annotated { items = [3] }

test "empty" := empty { items = [] } && !empty { items = [3] }
