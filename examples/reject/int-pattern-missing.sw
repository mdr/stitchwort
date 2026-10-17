-- expect-error: E-NONEXHAUSTIVE
-- Number patterns alone never cover every `Int`: there are always other
-- numbers, positive and negative.
f : Int -> Nat
f 0 = 1
f (-1) = 2
