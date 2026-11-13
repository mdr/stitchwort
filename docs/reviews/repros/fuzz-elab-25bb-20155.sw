-- The unifier solves an unknown through a folded call under `Succ`: the
-- implicit `n` is fixed only by unfolding `innerN 0` to `Succ 0` (SW-2157).

def innerN (x: Nat): Nat
    decreasing x
:=
  match x with
    | Zero => 1
    | Succ m => innerN m [decreasing := omega]

def lift [n: Nat] (h: Succ (Succ n) = Succ (Succ n)): n = n := rfl

theorem solved: 3 = 0 := lift (rfl: Succ (innerN 0) = Succ (innerN 340282366920938463463374607431768211456))
