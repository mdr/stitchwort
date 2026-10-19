-- expect-error: E-TYPE-MISMATCH
-- The expected type `Int` is used first, so `a := Int`, and then `True`
-- doesn't fit. The application is then elaborated again the old way, and that
-- way's error is reported: the literal made `a` a `Nat`.
def chooseFirst [a: Type] (x: a) (y: a): a := x

def bad: Int := chooseFirst 5 True
