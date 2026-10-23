-- core/Division.sw. `Nat.div` and `Nat.mod`, and the order lemmas (`leTrans`,
-- `lessTrans`) that `calc` and the `Ord` laws use. Loaded with the core:
-- `Nat.div`/`mod` are operators' meanings, and `Nat.leTrans` and
-- `Nat.lessTrans` are registry built-ins for `calc`
-- (docs/proposals/prelude-slim.md §2.1).

-- Division

-- Counts how many times `divisor` fits into `n`, using `fuel` to stay structurally
-- recursive (`n` is always enough fuel when `divisor` isn't zero).
def Nat.divFuel: Nat -> Nat -> Nat -> Nat
  | Zero, n, divisor => 0
  | Succ fuel, n, divisor => if Nat.leq divisor n then Succ (Nat.divFuel fuel (n - divisor) divisor) else 0

-- `n / divisor` and `n % divisor` need a proof that `divisor` isn't zero, which `auto` finds.
def Nat.div (n: Nat) (divisor: Nat): [auto ok: divisor != 0] -> Nat := Nat.divFuel n n divisor

-- The quotient goes on the left: `*` recurses on its left argument, so
-- `(n / divisor) * 100` stays put while checking, where `100 * (n / divisor)` would
-- unfold into a hundred additions.
def Nat.mod (n: Nat) (divisor: Nat): [auto ok: divisor != 0] -> Nat := n - (n / divisor) * divisor

theorem Nat.leSucc: (n: Nat) -> n <= Succ n
  | Zero => rfl
  | Succ n => Nat.leSucc n

theorem Nat.leTrans: (a: Nat) -> (b: Nat) -> (c: Nat) -> a <= b -> b <= c -> a <= c
  | Zero, b, c, h1, h2 => rfl
  | Succ a, Zero, c, h1, h2 => Void.exfalso (Bool.falseNotTrue h1)
  | Succ a, Succ b, Zero, h1, h2 => Void.exfalso (Bool.falseNotTrue h2)
  | Succ a, Succ b, Succ c, h1, h2 => Nat.leTrans a b c h1 h2

theorem Nat.leRefl: (n: Nat) -> n <= n
  | Zero => rfl
  | Succ n => Nat.leRefl n

theorem Nat.lessLe (m: Nat) (n: Nat) (h: m < n): m <= n := Nat.leTrans m (Succ m) n (Nat.leSucc m) h

theorem Nat.lessTrans (m: Nat) (n: Nat) (p: Nat) (h1: m < n) (h2: n < p): m < p := Nat.leTrans (Succ m) n p h1 (Nat.lessLe n p h2)
