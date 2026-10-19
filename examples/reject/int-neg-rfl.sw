-- expect-error: E-REFL
-- `-x = x` is false for `x = 1`; the true neighbour is `Int.negNeg`.
def negSelf (x: Int): -x = x := rfl
