-- expect-error: E-TERMINATION
-- Two definitions that pass their argument back and forth unchanged:
-- `ping 0` loops (§6.8, example 10).
-- Neighbour: `countdown`/`step` in accept/mutual.sw, where `step` makes it
-- smaller.
def ping (n: Nat): Nat := pong n

def pong (n: Nat): Nat := ping n
