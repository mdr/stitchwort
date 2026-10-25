-- expect-error: E-ABILITY
-- `Nat -> Nat` is pure, so it can't perform `State`.
ability State where
  get: () → {State} Nat

def bad (n: Nat): Nat := get() + n
