-- expect-error: E-NONEXHAUSTIVE
-- `OfNat n` covers the non-negative `Int`s and `0` is already among them, so
-- the negative numbers are left with no equation.
def f: Int -> Nat
  | OfNat n => 1
  | 0 => 2
