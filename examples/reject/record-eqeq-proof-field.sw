-- expect-error: E-INSTANCE-NONE
-- `DecEq` isn't derived for a record with a proof field that isn't an
-- equation: two records with equal data could still have different proofs,
-- so comparing the data doesn't decide `=` on the record
-- (docs/proposals/interfaces.md §5.11, D179). The message says why. A proof
-- field that's an equation in a type with `DecEq` is fine: `Short`, in
-- examples/accept/eqeq-proof-fields.sw.

type Ascending: List Nat -> Prop =
  | Empty: Ascending []
  | One (x: Nat): Ascending [x]

type Sorted = { items: List Nat, ok: Ascending items }

def one: Sorted := { items = [1], ok = One 1 }

test "a record with a proof" := one == one
