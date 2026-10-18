-- expect-error: E-REFL
-- `x % 3 = 1` does not hold by computation for a variable `x`; it is not true
-- for every `x` at all.
def bad (x : Int) : x % 3 = 1 := rfl
