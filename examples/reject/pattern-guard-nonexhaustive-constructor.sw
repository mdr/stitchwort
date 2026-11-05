-- expect-error: E-NONEXHAUSTIVE
-- `Some` has only a guarded arm, so `Some _` is missing.

def positiveOrZero: Option Nat → Nat
  | Some x if x > 0 => x
  | None => 0
