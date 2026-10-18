-- expect-error: E-TERMINATION
-- Two constants defined as each other: neither has a parameter that could
-- get smaller, so the loop is refused (the arity-zero case, §6.5).
-- Neighbour: `ten` in extract/mutual.sw, a constant computed from a group.
def c : Nat := d

def d : Nat := c
