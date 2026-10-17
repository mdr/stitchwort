-- expect-error: E-TYPE-MISMATCH
-- A number pattern tests the value: in the second equation nothing is known
-- about `x` (it could still be 0), so `R x` doesn't compute to `Bool`. Match
-- `OfNat Zero` and the other constructors instead (see
-- accept/int-patterns.sw).
R : Int -> Type
R (OfNat Zero) = Nat
R _ = Bool

make : (x : Int) -> R x
make 0 = 0
make x = False
