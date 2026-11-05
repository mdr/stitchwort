-- expect-error: E-AUTO-STUCK
-- A disjunction doesn't offer its sides: `b != 0 || c != 0` says only that
-- one of them holds, so the `then` branch can't prove `b ≠ 0`.
def modEither (a: Nat) (b: Nat) (c: Nat): Nat :=
  if b != 0 || c != 0 then a % b else 0
