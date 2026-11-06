-- expect-error: E-AUTO-STUCK
-- A disjunction doesn't offer its sides: `b != 0 || c != 0` says only that
-- one of them holds, so the `then` branch can't prove `b ≠ 0`.
def nonzero (d: Nat) [auto ok: d ≠ 0]: Nat := d

def pickEither (b: Nat) (c: Nat): Nat :=
  if b != 0 || c != 0 then nonzero b else 0
