--| [`Nat.div`] and [`Nat.mod`], and the order lemmas (`leTrans`,
--| `lessTrans`) that `calc` and the `Ord` laws use.
-- Loaded with the core: `Nat.div`/`mod` are operators' meanings, and
-- `Nat.leTrans` and `Nat.lessTrans` are registry built-ins for `calc`
-- (docs/proposals/prelude-slim.md §2.1).

-- Division

--| Counts how many times `divisor` fits into `n`, using `fuel` to stay structurally
--| recursive (`n` is always enough fuel when `divisor` isn't zero).
def Nat.divFuel: (fuel: Nat) → (n: Nat) → (divisor: Nat) → Nat
  | Zero, n, divisor => 0
  | Succ fuel, n, divisor => Nat.divStep (Nat.leq divisor n) fuel n divisor

--| One step of [`Nat.divFuel`], given whether `divisor` fits into `n`: if it
--| does, one more than the count for `n - divisor`. Goals show a step as the
--| `/` it comes from.
-- The comparison is an argument, rather than `divFuel` writing
-- `if … then Succ (…) else 0`, so that a step whose comparison can't be
-- decided (`n` has an unknown part) is one call stuck on it,
-- `Nat.divStep (d <= n) …`, not an `if` holding the next step in its
-- branch. Since `x + 12345` computes to 12345 `Succ`s around `x`, the `if`
-- put 12345 nested steps into the normal form of `(x + 12345) / d`, a term
-- growing with the square of the constant (docs/proposals/division.md).
@[noReceiver]
def Nat.divStep: (fits: Bool) → (fuel: Nat) → (n: Nat) → (divisor: Nat) → Nat
  | False, fuel, n, divisor => 0
  | True, fuel, n, divisor => Succ (Nat.divFuel fuel (n - divisor) divisor)

--| `n / divisor`, rounded down: `17 / 5` is 3. It needs a proof that `divisor` isn't zero, which `auto` finds.
def Nat.div (n: Nat) (divisor: Nat): [auto ok: divisor ≠ 0] → Nat := Nat.divFuel n n divisor

--| `n % divisor`, the remainder of `n / divisor`: `17 % 5` is 2.
-- The quotient goes on the left: `*` recurses on its left argument, so
-- `(n / divisor) * 100` stays put while checking, where `100 * (n / divisor)` would
-- unfold into a hundred additions.
def Nat.mod (n: Nat) (divisor: Nat): [auto ok: divisor ≠ 0] → Nat := n - (n / divisor) * divisor

theorem Nat.leSucc: (n: Nat) → n ≤ Succ n
  | Zero => rfl
  | Succ n => Nat.leSucc n

theorem Nat.leTrans: (a: Nat) → (b: Nat) → (c: Nat) → a ≤ b → b ≤ c → a ≤ c
  | Zero, b, c, h1, h2 => rfl
  | Succ a, Zero, c, h1, h2 => Void.exfalso (Bool.falseNotTrue h1)
  | Succ a, Succ b, Zero, h1, h2 => Void.exfalso (Bool.falseNotTrue h2)
  | Succ a, Succ b, Succ c, h1, h2 => Nat.leTrans a b c h1 h2

theorem Nat.leRefl: (n: Nat) → n ≤ n
  | Zero => rfl
  | Succ n => Nat.leRefl n

theorem Nat.lessLe (m: Nat) (n: Nat) (h: m < n): m ≤ n := Nat.leTrans m (Succ m) n (Nat.leSucc m) h

theorem Nat.lessTrans (m: Nat) (n: Nat) (p: Nat) (h1: m < n) (h2: n < p): m < p := Nat.leTrans (Succ m) n p h1 (Nat.lessLe n p h2)

--| A bound on either side of a sum bounds the sum. These are the steps of the
--| proofs generated for a nested type's `T.size` (an element of a list in a
--| node is smaller than the node).
theorem Nat.leAddOfLeLeft: (a: Nat) → (b: Nat) → (c: Nat) → a ≤ b → a ≤ b + c
  | Zero, b, c, h => rfl
  | Succ a, Zero, c, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ a, Succ b, c, h => Nat.leAddOfLeLeft a b c h

theorem Nat.leAddOfLeRight: (a: Nat) → (b: Nat) → (c: Nat) → a ≤ c → a ≤ b + c
  | a, Zero, c, h => h
  | a, Succ b, c, h => Nat.leTrans a (b + c) (Succ (b + c)) (Nat.leAddOfLeRight a b c h) (Nat.leSucc (b + c))

-- Lexicographic order on pairs of numbers

--| `(a1, a2)` comes before `(b1, b2)`: the first number is smaller, or it's the
--| same and the second is smaller. A recursive call of a definition with
--| `decreasing (m1, m2)` needs this of its arguments' measures and the
--| parameters': written `Nat.LexLess.First h` or `Nat.LexLess.Second rfl h`, or
--| found by `omega` or `auto`.
-- (docs/proposals/well-founded-recursion.md, stage 3d)
-- (Constructors rather than lemmas: a lemma would take the numbers as
-- arguments, and `stitchwort test` would compute them, an inner recursive
-- call's result among them.)
type Nat.LexLess (a1: Nat) (a2: Nat) (b1: Nat) (b2: Nat): Prop =
  | First (first: a1 < b1)
  | Second (same: a1 = b1) (second: a2 < b2)

--| When the first number didn't get smaller, it stayed the same, so it's still
--| below the first fuel; and the second got smaller.
-- The fuel `decreasing (m1, m2)` compiles to takes these steps.
theorem Nat.lexKeepsFirst: (a1: Nat) → (a2: Nat) → (b1: Nat) → (b2: Nat) → (k: Nat) → Nat.LexLess a1 a2 b1 b2 → ¬(a1 < b1) → b1 < k → a1 < k
  | a1, a2, b1, b2, k, Nat.LexLess.First first, no, h => Void.exfalso (no first)
  | a1, a2, b1, b2, k, Nat.LexLess.Second same second, no, h => J (z q => z < k) h (Eq.sym same)

theorem Nat.lexSecondLess: (a1: Nat) → (a2: Nat) → (b1: Nat) → (b2: Nat) → (k: Nat) → Nat.LexLess a1 a2 b1 b2 → ¬(a1 < b1) → b2 < Succ k → a2 < k
  | a1, a2, b1, b2, k, Nat.LexLess.First first, no, h => Void.exfalso (no first)
  | a1, a2, b1, b2, k, Nat.LexLess.Second same second, no, h => Nat.leTrans (Succ a2) b2 k second h
