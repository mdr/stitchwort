-- expect-error: E-TYPE-MISMATCH
-- Known limitation: the literal `5` is checked as a `Nat` before `i` is seen.
-- Write `(5 : Int)`.
chooseFirst : [a : Type] -> a -> a -> a
chooseFirst x y = x

r : Int -> Int
r i = chooseFirst 5 i
