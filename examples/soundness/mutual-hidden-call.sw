-- expect-error: E-TERMINATION
-- A call hidden inside an argument of an accepted call (§6.8, example 14):
-- the outer call to `b` is on the smaller `n`, but its argument calls `a`
-- again on the same number.
-- Neighbour: `isEven`/`isOdd` in accept/mutual.sw.
a : Nat -> Nat
a Zero     = Zero
a (Succ n) = b n (a (Succ n))

b : Nat -> Nat -> Nat
b Zero     m = m
b (Succ n) m = a n
