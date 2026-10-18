-- expect-error: E-TERMINATION
-- Rebuilding a parameter that isn't the last one bound is still the
-- parameter itself, not something smaller.
def loop : Nat -> Nat -> Nat
  | 0,      m => m
  | Succ n, m => loop (Succ n) m
