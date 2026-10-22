-- expect-error: E-PARSE
-- A syntax error doesn't hide the type error in a later declaration.
def f (xs: List Nat): Nat := xs.
def g: Nat := "a"
