-- expect-error: E-OR-PATTERN-BINDS
-- An alternative of an or-pattern can't bind a name: `x` would have no
-- value when `None` matched. Write separate arms instead.
def orZero (o: Option Nat): Nat :=
  match o with
    | Some x | None => 0
