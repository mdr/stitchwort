-- expect-error: E-UNKNOWN-NAME
-- Nothing in scope is close to `frobnicate`, so there is no "did you mean".
def x: Nat :=
  frobnicate
