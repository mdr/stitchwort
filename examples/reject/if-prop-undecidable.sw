-- expect-error: E-AUTO-NONE
-- `if` on a proposition needs a decision procedure for it, and nothing
-- decides whether two functions are equal.
same : (Nat -> Nat) -> (Nat -> Nat) -> Nat
same f g = if f = g then 1 else 0
