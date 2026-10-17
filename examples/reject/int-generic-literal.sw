-- expect-error: E-TYPE-MISMATCH
-- Known limit: a generic function's literal argument is a `Nat`, so `f 5 + i`
-- fails with `i : Int`. Write `ident (5 : Int) + i`.
ident : [a : Type] -> a -> a
ident x = x

r : Int -> Int
r i = ident 5 + i
