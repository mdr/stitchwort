-- core/Division.sw. `Nat.div` and `Nat.mod`, and the order lemmas (`leTrans`,
-- `lessTrans`) that `calc` and the `Ord` laws use. Loaded with the core:
-- `Nat.div`/`mod` are operators' meanings, and `Nat.leTrans` and
-- `Nat.lessTrans` are registry built-ins for `calc`
-- (docs/proposals/prelude-slim.md §2.1).

-- Division

-- Counts how many times `d` fits into `n`, using `fuel` to stay structurally
-- recursive (`n` is always enough fuel when `d` isn't zero).
def Nat.divFuel: Nat -> Nat -> Nat -> Nat
  | Zero,      n, d => 0
  | Succ fuel, n, d => if Nat.leq d n then Succ (Nat.divFuel fuel (n - d) d) else 0

-- `n / d` and `n % d` need a proof that `d` isn't zero, which `auto` finds.
def Nat.div (n: Nat) (d: Nat): [auto ok: d != 0] -> Nat := Nat.divFuel n n d

-- The quotient goes on the left: `*` recurses on its left argument, so
-- `(n / d) * 100` stays put while checking, where `100 * (n / d)` would
-- unfold into a hundred additions.
def Nat.mod (n: Nat) (d: Nat): [auto ok: d != 0] -> Nat := n - (n / d) * d

theorem Nat.leSucc: (n: Nat) -> n <= Succ n
  | Zero => rfl
  | Succ n => Nat.leSucc n

theorem Nat.leTrans: (a: Nat) -> (b: Nat) -> (c: Nat) -> a <= b -> b <= c -> a <= c
  | Zero, b, c, h1, h2 => rfl
  | Succ a, Zero, c, h1, h2 => Void.exfalso (Bool.falseNotTrue h1)
  | Succ a, Succ b, Zero, h1, h2 => Void.exfalso (Bool.falseNotTrue h2)
  | Succ a, Succ b, Succ c, h1, h2 => Nat.leTrans a b c h1 h2

theorem Nat.lessLe (m: Nat) (n: Nat) (h: m < n): m <= n := Nat.leTrans m (Succ m) n (Nat.leSucc m) h

theorem Nat.lessTrans (m: Nat) (n: Nat) (p: Nat) (h1: m < n) (h2: n < p): m < p := Nat.leTrans (Succ m) n p h1 (Nat.lessLe n p h2)

