-- expect-error: E-UNKNOWN-NAME
-- This file's own `Option` hides the library's, and the library's `Some`
-- and `None` go with it (they're `Std.Option.Some` and `Std.Option.None`).
type Option (a: Type): Type =
  | Absent
  | Present (value: a)

def one: Std.Option Nat := Some 1
