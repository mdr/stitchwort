-- expect-error: E-AUTO-NONE
-- `g = h` compares functions, which has no decision procedure, so the
-- conjunction `x < 3 && g = h` can't be decided in an `if`.
def f (g: Nat -> Nat) (h: Nat -> Nat) (x: Nat): Nat := if x < 3 && g = h then 1 else 0
