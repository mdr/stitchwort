-- expect-error: E-AUTO-NONE
-- `if` on a proposition needs a decision procedure for it, and nothing
-- decides whether two functions are equal.
def same (f: Nat -> Nat) (g: Nat -> Nat): Nat := if f = g then 1 else 0
