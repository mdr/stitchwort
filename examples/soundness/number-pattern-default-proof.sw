-- expect-error: E-REFL
-- The equation after a number pattern runs for every *other* number, so it
-- can't claim the argument is that number. (accept/number-patterns.sw has
-- `isNotFound`, which decides it instead.)
def isNotFound: (n: Nat) → Decidable (n = 404)
  | 404 => Yes rfl
  | n   => Yes rfl
