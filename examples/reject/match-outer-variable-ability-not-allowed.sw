-- expect-error: E-ABILITY
-- A `match` on a variable from outside the lambda leaves the lambda's row
-- as it is (SW-838), but that row is still the enclosing function's: here
-- the function is pure, so the arms can't perform `g`'s abilities.
def offsets (g: Nat → {e} Nat) (xs: List Nat) (k: Nat): List Nat :=
  xs.map (x =>
    match k with
      | 0 => g x
      | n => g (n + x))
