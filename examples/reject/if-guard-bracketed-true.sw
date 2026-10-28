-- expect-error: E-TYPE-MISMATCH
-- With brackets `= True` parses, but in an `if h:` guard `<` is the
-- proposition, not a `Bool`; the note says to leave `= True` out.
def pick (low: Nat) (high: Nat): Nat :=
  if apart: (Succ low < high) = True then low else high
