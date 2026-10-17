-- expect-error: E-TYPE-MISMATCH
-- The expected type `Int` is used first, so `a := Int`, and then `True`
-- doesn't fit. The application is then elaborated again the old way, and that
-- way's error is reported: the literal made `a` a `Nat`.
chooseFirst : [a : Type] -> a -> a -> a
chooseFirst x y = x

bad : Int
bad = chooseFirst 5 True
