-- expect-error: E-REFL
-- `-(-x) = x` is a theorem, not `rfl`: `Int.negNeg` proves it by cases.
negNeg : (x : Int) -> -(-x) = x
negNeg x = rfl
