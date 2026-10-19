-- expect-error: E-TERMINATION
-- A call hidden inside an argument of an accepted call (§6.8, example 14):
-- the outer call to `b` is on the smaller `n`, but its argument calls `a`
-- again on the same number.
-- Neighbour: `isEven`/`isOdd` in accept/mutual.sw.
def a: Nat -> Nat
  | Zero   => Zero
  | Succ n => b n (a (Succ n))

def b: Nat -> Nat -> Nat
  | Zero,   m => m
  | Succ n, m => a n
