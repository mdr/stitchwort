-- expect-error: E-PARSE
-- `if h:` takes a proposition, so `<` is one already; `= True` after it
-- doesn't parse, and the note says to leave it out.
def pick (low: Nat) (high: Nat): Nat :=
  if apart: Succ low < high = True then low else high
