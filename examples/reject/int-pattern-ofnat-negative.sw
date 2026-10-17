-- expect-error: E-TYPE-MISMATCH
-- `OfNat` wraps a `Nat`, which has no negative numbers. Write `(-1)` on its
-- own to match the negative `Int`.
f : Int -> Nat
f (OfNat (-1)) = 1
f _ = 2
