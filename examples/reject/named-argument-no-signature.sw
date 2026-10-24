-- expect-error: E-UNKNOWN-NAME
-- Names come from a declared signature, never from unification (D1115): an
-- `if` whose branches name their parameters differently has no names, so
-- they can't depend on which branch is checked first.

def lower (low: Nat) (high: Nat): Nat := low
def upper (high: Nat) (low: Nat): Nat := high

def pickOne (first: Bool): Nat := (if first then lower else upper) (low := 1) 2
