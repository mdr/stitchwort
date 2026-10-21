-- expect-error: E-TYPE-MISMATCH
-- `x |> f` is `f x`: the value is the function's last argument, here a
-- list, but `"abc"` is a `Text`.
def f: Nat := "abc" |> List.sum
