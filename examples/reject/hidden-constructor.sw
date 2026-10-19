-- expect-error: E-UNKNOWN-NAME
-- This file's own `Maybe` hides the library's, and the library's `Just`
-- and `Nothing` go with it (they're `Std.Maybe.Just` and `Std.Maybe.Nothing`).
type Maybe (a: Type): Type =
  | Absent
  | Present (value: a)

def one: Std.Maybe Nat := Just 1
