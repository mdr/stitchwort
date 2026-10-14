-- expect-error: E-TERMINATION
-- The argument grows instead of shrinking, so this never terminates.
grow : Nat -> Nat
grow n = grow (Succ n)
