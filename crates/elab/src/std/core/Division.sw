--| [`Nat.div`] and [`Nat.mod`], and the order lemmas (`leTrans`,
--| `lessTrans`) that `calc` and the `Ord` laws use.
-- Loaded with the core: `Nat.div`/`mod` are operators' meanings, and
-- `Nat.leTrans` and `Nat.lessTrans` are registry built-ins for `calc`
-- (docs/proposals/prelude-slim.md §2.1).

-- Division

--| Counts how many times `divisor` fits into `n`, using `fuel` to stay structurally
--| recursive (`n` is always enough fuel when `divisor` isn't zero). It's 0 when
--| `divisor` is 0.
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
-- A zero divisor always fits, and counts as fitting no times, which makes
-- `n / 0 = 0`. The test is in the step, after the comparison, so that `0 / d`
-- is 0 and a stuck `n / d` is still one stuck comparison.
@[noReceiver]
def Nat.divStep: (fits: Bool) → (fuel: Nat) → (n: Nat) → (divisor: Nat) → Nat
  | False, fuel, n, divisor => 0
  | True, fuel, n, Zero => 0
  | True, fuel, n, Succ divisor => Succ (Nat.divFuel fuel (n - Succ divisor) (Succ divisor))

--| `n / divisor`, rounded down: `17 / 5` is 3. Dividing by 0 gives 0, as in
--| Lean: `n / 0 = 0`, so that `n = (n / d) * d + n % d` holds for every `d`.
--| Lemmas that need a divisor that isn't 0 (`Nat.modLt`) take it as a hypothesis.
def Nat.div (n: Nat) (divisor: Nat): Nat := Nat.divFuel n n divisor

--| `n % divisor`, the remainder of `n / divisor`: `17 % 5` is 2. The
--| remainder of dividing by 0 is the number itself: `n % 0 = n`.
-- The quotient goes on the left: `*` recurses on its left argument, so
-- `(n / divisor) * 100` stays put while checking, where `100 * (n / divisor)` would
-- unfold into a hundred additions.
def Nat.mod (n: Nat) (divisor: Nat): Nat := n - (n / divisor) * divisor

theorem Nat.leSucc (n: Nat): n ≤ Succ n := match n with
  | Zero => rfl
  | Succ n => Nat.leSucc n

theorem Nat.leTrans (a b c: Nat) (h1: a ≤ b) (h2: b ≤ c): a ≤ c := match a, b, c with
  | Zero, b, c => rfl
  | Succ a, Succ b, Succ c => Nat.leTrans a b c h1 h2

theorem Nat.leRefl (n: Nat): n ≤ n := match n with
  | Zero => rfl
  | Succ n => Nat.leRefl n

theorem Nat.lessLe (m: Nat) (n: Nat) (h: m < n): m ≤ n := Nat.leTrans m (Succ m) n (Nat.leSucc m) h

theorem Nat.lessTrans (m: Nat) (n: Nat) (p: Nat) (h1: m < n) (h2: n < p): m < p := Nat.leTrans (Succ m) n p h1 (Nat.lessLe n p h2)

--| A bound on either side of a sum bounds the sum. These are the steps of the
--| proofs generated for a nested type's `T.size` (an element of a list in a
--| node is smaller than the node).
theorem Nat.leAddOfLeLeft (a b c: Nat) (h: a ≤ b): a ≤ b + c := match a, b with
  | Zero, b => rfl
  | Succ a, Succ b => Nat.leAddOfLeLeft a b c h

theorem Nat.leAddOfLeRight (a b c: Nat) (h: a ≤ c): a ≤ b + c := match b with
  | Zero => h
  | Succ b => Nat.leTrans a (b + c) (Succ (b + c)) (Nat.leAddOfLeRight a b c h) (Nat.leSucc (b + c))

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
theorem Nat.lexKeepsFirst (a1 a2 b1 b2 k: Nat) (lex: Nat.LexLess a1 a2 b1 b2) (no: ¬(a1 < b1)) (h: b1 < k): a1 < k :=
  match lex with
    | Nat.LexLess.First first => Void.exfalso (no first)
    | Nat.LexLess.Second same second => J (z q => z < k) h (Eq.sym same)

theorem Nat.lexSecondLess (a1 a2 b1 b2 k: Nat) (lex: Nat.LexLess a1 a2 b1 b2) (no: ¬(a1 < b1)) (h: b2 < Succ k): a2 < k :=
  match lex with
    | Nat.LexLess.First first => Void.exfalso (no first)
    | Nat.LexLess.Second same second => Nat.leTrans (Succ a2) b2 k second h
