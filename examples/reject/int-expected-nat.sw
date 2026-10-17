-- expect-error: E-TYPE-MISMATCH
-- The expected type `Nat` decides the group, so `x : Int` does not fit.
r : Int -> Nat
r x = (x + 1 : Nat)
