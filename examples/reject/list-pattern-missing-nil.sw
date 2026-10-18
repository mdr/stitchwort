-- expect-error: E-NONEXHAUSTIVE
-- Only non-empty lists are matched: the empty one is missing.
f : List Nat -> Nat
f [x] = x
f [x, y] = y
f (Cons x (Cons y (Cons z rest))) = z
