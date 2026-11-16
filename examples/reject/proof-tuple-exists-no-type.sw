-- expect-error: E-CANNOT-INFER
-- A witness and a proof fit many `∃` statements, so a tuple proving one
-- needs its goal known.
def seven (h: 7 * 7 = 49): Nat :=
  let found := (7, h)
  7
