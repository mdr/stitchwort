def halvings (n: Nat): Nat :=
  if n ≤ 1 then 0 else 1 + halvings (n / 2)
