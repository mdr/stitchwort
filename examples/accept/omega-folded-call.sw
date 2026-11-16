-- `arithmetic` sees through a folded `decreasing` call: `two 0` computes to `2`,
-- so it is a number, not an unknown atom (SW-2253).

def two (x: Nat): Nat
    decreasing x
:=
  match x with
    | Zero => 2
    | Succ m => two m [decreasing := arithmetic]

theorem aboveX ∀ (x: Nat): x + two 0 > x := arithmetic

theorem fromFact ∀ (x: Nat) (h: x = two 0): x = 2 := arithmetic

theorem intoFact ∀ (x: Nat) (h: x = 2): x = two 0 := arithmetic

theorem sumOf ∀ (x y: Nat) (h: y = two 0): x + y = x + 2 := arithmetic

theorem asInt ∀ (x: Nat): x.toInt + (two 0).toInt = x.toInt + 2 := arithmetic

-- A folded call inside a sum that is itself stuck on a variable.
theorem nested ∀ (x y: Nat): x + (y + two 0) = x + y + 2 := arithmetic

theorem nestedInt ∀ (x y: Nat): (x + (y + two 0)).toInt = x.toInt + y.toInt + 2 := arithmetic

-- A call that is slow to unfold in a fact the goal doesn't need doesn't make
-- `arithmetic` fail: it stays an atom once unfolding takes too long.
def fib (n: Nat): Nat
    decreasing n
:=
  match n with
    | Zero => 0
    | Succ Zero => 1
    | Succ (Succ m) => fib m [decreasing := arithmetic] + fib (Succ m) [decreasing := arithmetic]

theorem unusedSlowFact ∀ (x r: Nat) (h: r = fib 40): x + 1 > x := arithmetic
