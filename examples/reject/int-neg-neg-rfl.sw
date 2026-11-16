-- expect-error: E-REFL
-- `-(-x) = x` is a theorem, not `byComputing`: `Int.negNeg` proves it by cases.
def negNeg (x: Int): -(-x) = x := byComputing
