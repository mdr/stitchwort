-- expect-error: E-TYPE-MISMATCH
-- A `Nat` and an `Int` can not be mixed; convert with `n.toInt`.
r : Nat -> Int -> Bool
r n i = n + i == 0
