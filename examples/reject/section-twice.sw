-- expect-error: E-TYPE-MISMATCH
-- A section that starts an expression is one function of one argument, used
-- once, at the start: `(.isEmpty || .startsWith "a")` is
-- `x => x.isEmpty || (.startsWith "a")`, and the second section is a function
-- where a `Bool` is wanted. To use the argument twice, write the lambda:
-- `x => x.isEmpty || x.startsWith "a"`.

def f (xs: List Text): List Text := xs.filter (.isEmpty ∨ .startsWith "a")
