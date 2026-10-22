-- expect-error: E-UNKNOWN-NAME
-- No `T.ext` for a record whose data fields depend on each other (`items`
-- has a type that mentions `size`): `x.items = y.items` isn't a statement.

import Std (Nat, Vec)

type Sized = { size: Nat, items: Vec Nat size }

theorem same (a: Sized) (b: Sized) (e: a.size = b.size): a = b := Sized.ext a b e
