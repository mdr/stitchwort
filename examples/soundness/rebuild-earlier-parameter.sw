-- expect-error: E-TERMINATION
-- Rebuilding a parameter that isn't the last one bound is still the
-- parameter itself, not something smaller.
loop : Nat -> Nat -> Nat
loop 0        m = m
loop (Succ n) m = loop (Succ n) m
