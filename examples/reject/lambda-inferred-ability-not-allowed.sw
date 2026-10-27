-- expect-error: E-ABILITY
-- A lambda with no type written may perform abilities, so binding it is
-- fine, but calling it performs `Ask`, which the enclosing function doesn't
-- allow: the error is at the call.
ability Ask where
  ask: () → {Ask} Nat

def twice (n: Nat): Nat :=
  let next := () => ask() + n
  next() + next()
