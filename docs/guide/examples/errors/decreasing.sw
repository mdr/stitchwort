def countDown (n step: Nat): Nat
    decreasing n
:=
  if n ≤ 0 then 0 else 1 + countDown (n - step) step
