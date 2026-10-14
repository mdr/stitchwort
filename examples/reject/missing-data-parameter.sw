-- expect-error: E-ARITY
-- `List` needs to know what it's a list of.
size : List -> Nat
size xs = 0
