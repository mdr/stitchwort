-- `omega` sees through a folded `decreasing` call: `two 0` computes to `2`,
-- so it is a number, not an unknown atom (SW-2253).

def two (x: Nat): Nat
    decreasing x
:=
  match x with
    | Zero => 2
    | Succ m => two m [decreasing := omega]

theorem aboveX (x: Nat): x + two 0 > x := omega

theorem fromFact (x: Nat) (h: x = two 0): x = 2 := omega

theorem intoFact (x: Nat) (h: x = 2): x = two 0 := omega

theorem sumOf (x: Nat) (y: Nat) (h: y = two 0): x + y = x + 2 := omega

theorem asInt (x: Nat): x.toInt + (two 0).toInt = x.toInt + 2 := omega
