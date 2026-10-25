-- expect-error: E-TYPE-MISMATCH

import Std (List)

-- `x |> f` is `f x`: the value is the function's first argument, here a
-- list, but `"abc"` is a `Text`.
def f: Nat := "abc" |> List.sum
