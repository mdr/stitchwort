-- A number literal waits for what the rest of the declaration says its type
-- is (D2084): `3 - 5` has no expected type, and `m + i` with `i: Int` makes
-- `m` an `Int`, so `m` is `-2`. Only where nothing says is a literal a `Nat`.
def r (i: Int): Bool :=
  let m := 3 - 5
  m + i == 0

test "m is an Int" := r 2

test "and not a Nat" := not (r 0)
