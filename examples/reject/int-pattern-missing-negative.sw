-- expect-error: E-NONEXHAUSTIVE
-- `OfNat n` covers every non-negative `Int`, but the negative ones are only
-- covered down to `-1`; other negative numbers have no equation.
def f: Int → Nat
  | OfNat n => 1
  | (-1) => 2
