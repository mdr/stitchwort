-- expect-error: E-NONEXHAUSTIVE
-- Lists of two or more elements aren't matched.
f : List Nat -> Nat
f [] = 0
f [x] = x
