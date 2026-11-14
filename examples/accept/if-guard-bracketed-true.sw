-- With brackets, `(Succ low < high) = True` in an `if h:` guard reads `<` as
-- the `Bool` test, since the proposition reading fails against `True`
-- (SW-944). It was rejected before, with a note to leave `= True` out.
def pick (low high: Nat): Nat := if apart: (Succ low < high) = True then low else high
