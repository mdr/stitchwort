-- A lambda bound by `let` whose parameter has no written type, before a
-- `match` that splits a variable, used in one of its arms: the arm's use
-- works out the parameter's type, which the split doesn't change, as it
-- doesn't for a lambda whose body matches (SW-873, SW-4586).

import Std (List, Option)

type Box = { items: List Nat }

-- The parameter's type is the argument's.
def same (b: Nat) (o: Option Nat): Nat :=
  let f := r => r
  match o with
    | Some _ => f b
    | None => 0

-- A field of the parameter, looked up once its type is known.
def size (b: Box) (o: Option Nat): Nat :=
  let size := r => r.items.length
  match o with
    | Some _ => size b
    | None => 0

-- A membership, decided once the field's type is known.
def has (b: Box) (o: Option Nat): Bool :=
  let check := r => 3 ∈ r.items
  match o with
    | Some _ => check b
    | None => False

-- Without a `match`: as the condition of an `if`, decided once the field's
-- type is known, as it is where a `Bool` is expected.
def count (b: Box): Nat :=
  let check := r => 3 ∈ r.items
  if check b then 1 else 0

test "same" := same 4 (Some 1) == 4 ∧ same 4 None == 0

test "size" := size { items = [1, 2] } (Some 1) == 2 ∧ size { items = [1, 2] } None == 0

test "has" := has { items = [3] } (Some 1) ∧ !has { items = [4] } (Some 1) ∧ !has { items = [3] } None

test "count" := count { items = [3] } == 1 ∧ count { items = [4] } == 0
