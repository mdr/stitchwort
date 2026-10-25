-- expect-error: E-TYPE-MISMATCH
-- `-` is not an operator section: `(- 1)` is the number negative one, not
-- `x => x - 1`, so `map` is given a number where it wants a function. For the
-- function write `(x => x - 1)`, or `.sub 1`.

def decrement (xs: List Int): List Int := xs.map (- 1)
