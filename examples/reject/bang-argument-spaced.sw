-- expect-error: E-PARSE
-- `!` with a space on both sides is not an argument: `f ! a` is `f` followed
-- by a stray `!`. Write `f !a`.
def g (f: Bool -> Bool) (a: Bool): Bool := f ! a
