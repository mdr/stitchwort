-- expect-error: E-INSTANCE-NONE
-- `if` on a proposition needs a decision procedure for it; an equation is
-- decided by its type's `DecEq` instance, and functions have none.
def same (f: Nat → Nat) (g: Nat → Nat): Nat := if f = g then 1 else 0
