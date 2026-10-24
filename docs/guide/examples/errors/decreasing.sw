def halvings (n: Nat): Nat
    decreasing n
:=
  if n <= 1 then 0 else 1 + halvings (n / 2)
