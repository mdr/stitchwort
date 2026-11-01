-- expect-error: E-TYPE-MISMATCH
-- The expected type `Int` is used first, so `a := Int`, and then `True`
-- doesn't fit. The application is then elaborated again the old way: the
-- literal `5` waits for its type, `True` makes `a` a `Bool`, and a numeral
-- can't be a `Bool`, which is the error reported, at the literal.
def chooseFirst [a: Type] (x: a) (y: a): a := x

def bad: Int := chooseFirst 5 True
