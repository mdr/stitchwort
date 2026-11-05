-- expect-error: E-TERMINATION
-- Halving isn't recursion on a part of `n`, so the checker can't see that it
-- stops. A depth limit would: an extra `fuel: Nat` argument, decreased on each
-- call and failing (or returning a default) when it runs out, keeps the
-- definition total as well as provable.
def halve (n: Nat): Nat :=
  if n ≤ 1 then 0 else Succ (halve (n / 2))
