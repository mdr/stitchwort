-- expect-error: E-NOT-EMPTY
-- `()` below a guard is as absurd as without one: `Bool` has values.

def notEmpty: (Nat, Bool) → Nat
  | (x, _) if x > 3 => 1
  | (_, ()) => 0
