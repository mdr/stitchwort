-- hypotheses in scope, and ho decreasing n
:=
  if big: Nat.leq n 9 = False
  then digitsOnto (n / 10) (Cons (n % 10) acc)
  elg n
:=
  if big: Nase Cons n acc
