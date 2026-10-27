-- expect-error: E-ABILITY
-- A lambda with no type written or expected is inferred as pure, so its
-- body can't perform an ability, even inside a function that may: the note
-- says to write the lambda's type.
ability Ask where
  ask: () → {Ask} Nat

def twice (n: Nat): {Ask} Nat :=
  let next := () => ask() + n
  next() + next()
