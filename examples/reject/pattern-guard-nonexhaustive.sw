-- expect-error: E-NONEXHAUSTIVE
-- An arm with a condition covers nothing: the checker doesn't reason about
-- conditions, so `n < 5` and `n >= 5` together still leave a case.

def twoSides: Nat → Nat
  | n if n < 5 => n
  | n if n >= 5 => n
