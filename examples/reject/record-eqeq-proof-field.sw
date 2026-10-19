-- expect-error: E-AUTO-NONE
-- `==` isn't derived for a record with a proof field: two records with
-- equal data could still have different proofs, so comparing the data
-- doesn't decide `=` on the record (docs/proposals/records.md §11.4). The
-- message says why. `==` on a record of data fields is derived
-- (examples/accept/records.sw).

def IsShort (xs: List Nat): Prop := List.length xs <= 2

type Short = { items: List Nat, short: IsShort items }

def one: Short := { items = [1], short = rfl }

test "a record with a proof" := one == one
