-- expect-error: E-UNIVERSE
-- A component of a pair is a `Type`, never a proposition.
Bad : Type
Bad = (Nat, 1 = 1)
