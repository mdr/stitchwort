-- expect-error: E-TYPE-MISMATCH
-- The expected type `Nat` decides the group, so `x: Int` does not fit.
def r (x: Int): Nat := (x + 1: Nat)
