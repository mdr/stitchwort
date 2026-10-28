-- expect-error: E-PARSE
-- `!` glued to the operand on its left is not an argument either: `f!a`.
def g (f: Bool -> Bool) (a: Bool): Bool := f!a
