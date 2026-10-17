-- expect-error: E-TYPE-MISMATCH
-- Prefix minus makes its group `Int`, and a `Nat` operand is not converted.
r : Nat -> Int
r n = -n
