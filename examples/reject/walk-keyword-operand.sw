-- expect-error: E-PARSE
-- `byWalking` starts a walk where an expression starts; anywhere else, such as an
-- operator's right side, the keyword is an error, not a name.
def a (x y: Nat): Nat := x + byWalking [y]
