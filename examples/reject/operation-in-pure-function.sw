-- expect-error: E-ABILITY
-- `Nat -> Nat` is pure, so it can't perform `State`.
ability State where
  get : () -> {State} Nat

bad : Nat -> Nat
bad n = get () + n
