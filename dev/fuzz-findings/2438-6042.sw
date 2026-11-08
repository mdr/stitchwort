-- expect-error: E-ABILITY
-- `Nat -> Nat` is pure, so it can't perform `State`.
ability State where
  get: () → {State} get

def bad (n: Nat): Nat := Nat() + n
