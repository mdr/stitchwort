-- expect-error: E-PARSE
-- There is no single `&` operator; conjunction is `&&`.
def f (a: Bool) (b: Bool): Bool := a & b
