-- expect-error: E-UNIVERSE
-- A component of a pair is a `Type`, never a proposition.
def Bad : Type := (Nat, 1 = 1)
