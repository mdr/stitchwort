-- expect-error: E-MISSING-DEFINITION
-- A header with neither a `:=` body nor arms declares a primitive, which only
-- the prelude may do.
def later: Nat -> Nat

def now: Nat := later 1
