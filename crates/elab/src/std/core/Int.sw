--| `Int`: the type, its arithmetic, decidable equality,
--| comparison, `toText`, and Euclidean `div`/`mod`.
-- Loaded with the core: `Int` is pinned by content hash, and `+ * < <=` on
-- `Int` go through instances that need these definitions
-- (docs/proposals/prelude-slim.md §2.1).

-- Integers (docs/proposals/integers.md)

--| An integer: `OfNat n` is `n`, and `NegSucc n` is `-(n + 1)`, so each
--| integer has exactly one form. The definitions compute through `Nat`'s, so
--| they're as compact as `Nat` is, and the kernel needs nothing new.
type Int: Type = | OfNat (n: Nat) | NegSucc (n: Nat)

--| `-x`: the integer with the other sign.
def Int.neg: (x: Int) → Int
  | OfNat Zero => OfNat Zero
  | OfNat (Succ n) => NegSucc n
  | NegSucc n => OfNat (Succ n)

--| `m - n` for naturals, as an integer.
-- One subtraction decides which side is bigger: `n - m` is zero exactly
-- when `n <= m`.
def Int.subNatNatFrom (m n: Nat): (diff: Nat) → Int
  | Zero => OfNat (m - n)
  | Succ k => NegSucc k

--| `m - n` for naturals, as an integer: negative when `n` is bigger.
def Int.subNatNat (m n: Nat): Int := Int.subNatNatFrom m n (n - m)

--| `a + b`: addition of integers.
def Int.add: (x: Int) → (y: Int) → Int
  | OfNat m, OfNat n => OfNat (m + n)
  | OfNat m, NegSucc n => Int.subNatNat m (Succ n)
  | NegSucc m, OfNat n => Int.subNatNat n (Succ m)
  | NegSucc m, NegSucc n => NegSucc (Succ (m + n))

--| `a - b`: subtraction of integers, which can go below zero.
def Int.sub (a b: Int): Int := Int.add a (Int.neg b)

--| `a * b`: multiplication of integers. By constructors first, so `OfNat m * OfNat n` is `OfNat (m * n)`.
def Int.mul: (x: Int) → (y: Int) → Int
  | OfNat m, OfNat n => OfNat (m * n)
  | OfNat m, NegSucc n => Int.neg (OfNat (m * Succ n))
  | NegSucc m, OfNat n => Int.neg (OfNat (Succ m * n))
  | NegSucc m, NegSucc n => OfNat (Succ m * Succ n)

--| `|x|`, as a `Nat`.
def Int.natAbs: (x: Int) → Nat
  | OfNat n => n
  | NegSucc n => Succ n

--| `x` if it isn't negative, otherwise `0`.
def Int.toNat: (x: Int) → Nat
  | OfNat n => n
  | NegSucc n => 0

-- The two constructors are different, and each is injective.

--| `Unit` (true) for an `OfNat` and `Void` (false) for a `NegSucc`: how `OfNat m ≠ NegSucc n` is proved.
def Int.IsOfNat: (x: Int) → Prop
  | OfNat n => Unit
  | NegSucc n => Void

theorem Int.ofNatNotNegSucc ∀ (m n: Nat): OfNat m ≠ NegSucc n
  | p => J (y q => Int.IsOfNat y) Trivial p

theorem Int.negSuccNotOfNat ∀ (m n: Nat): NegSucc m ≠ OfNat n
  | p => Int.ofNatNotNegSucc n m (Eq.sym p)

theorem Int.ofNatInjective ∀ (m n: Nat) (p: OfNat m = OfNat n): m = n := Eq.cong Int.toNat p

theorem Int.negSuccInjective ∀ [m n: Nat] (p: NegSucc m = NegSucc n): m = n := Nat.succInjective (Eq.cong Int.natAbs p)

--| Decides whether two `OfNat`s are equal, from a decision about their numbers.
def Int.decOfNat (m n: Nat) (dec: Decidable (m = n)): Decidable (OfNat m = OfNat n) :=
  Decidable.map dec (Eq.cong OfNat) (Int.ofNatInjective m n)

--| Decides whether two `NegSucc`s are equal, from a decision about their numbers.
def Int.decNegSucc (m n: Nat) (dec: Decidable (m = n)): Decidable (NegSucc m = NegSucc n) :=
  Decidable.map dec (Eq.cong NegSucc) (p => Int.negSuccInjective p)

--| Its test is [`Nat.equal`] on the numbers, for two of the same sign, so it
--| runs natively however big they are.
def Int.decEq: (a: Int) → (b: Int) → Decidable (a = b)
  | OfNat m, OfNat n => Int.decOfNat m n (Nat.decEq m n)
  | OfNat m, NegSucc n => Decidable.no (Int.ofNatNotNegSucc m n)
  | NegSucc m, OfNat n => Decidable.no (Int.negSuccNotOfNat m n)
  | NegSucc m, NegSucc n => Int.decNegSucc m n (Nat.decEq m n)

--| Whether `a <= b`, as a `Bool`. Every negative is below every non-negative; among negatives the
--| order flips, since `NegSucc n` is `-(n+1)`.
def Int.leq: (x: Int) → (y: Int) → Bool
  | OfNat m, OfNat n => Nat.leq m n
  | OfNat m, NegSucc n => False
  | NegSucc m, OfNat n => True
  | NegSucc m, NegSucc n => Nat.leq n m

--| Whether `a < b`, as a `Bool`.
def Int.less: (x: Int) → (y: Int) → Bool
  | OfNat m, OfNat n => Nat.leq (Succ m) n
  | OfNat m, NegSucc n => False
  | NegSucc m, OfNat n => True
  | NegSucc m, NegSucc n => Nat.leq (Succ n) m

--| `a <= b` as a proposition, defined by computation.
def Int.LessEq (a b: Int): Prop := Int.leq a b = True

--| `a < b` as a proposition, defined by computation.
def Int.LessThan (a b: Int): Prop := Int.less a b = True

--| `Int.leq a b` (what `a <= b` is on `Int`) reads as `a ≤ b`.
@[reading]
theorem Int.leqReads ∀ (a b: Int): Int.leq a b ↔ Int.LessEq a b := { forward = h => h, backward = h => h }

--| `Int.leq a b` is `False` exactly when `b` is below `a`.
@[reading]
theorem Int.leqReadsFalse ∀ (a b: Int): Int.leq a b = False ↔ Int.LessThan b a := match a, b with
  | OfNat m, OfNat n => Nat.leqReadsFalse m n
  | OfNat m, NegSucc n => { forward = h => rfl, backward = h => rfl }
  | NegSucc m, OfNat n =>
    { forward = h => Void.exfalso (Bool.trueNotFalse h), backward = h => Void.exfalso (Bool.falseNotTrue h) }
  | NegSucc m, NegSucc n => Nat.leqReadsFalse n m

--| `Int.less a b` (what `a < b` is on `Int`) reads as `a < b`.
@[reading]
theorem Int.lessReads ∀ (a b: Int): Int.less a b ↔ Int.LessThan a b := { forward = h => h, backward = h => h }

--| `Int.less a b` is `False` exactly when `b` is at most `a`.
@[reading]
theorem Int.lessReadsFalse ∀ (a b: Int): Int.less a b = False ↔ Int.LessEq b a := match a, b with
  | OfNat m, OfNat n => Nat.leqReadsFalse (Succ m) n
  | OfNat m, NegSucc n => { forward = h => rfl, backward = h => rfl }
  | NegSucc m, OfNat n =>
    { forward = h => Void.exfalso (Bool.trueNotFalse h), backward = h => Void.exfalso (Bool.falseNotTrue h) }
  | NegSucc m, NegSucc n => Nat.leqReadsFalse (Succ n) m

instance Int.decLessEq (a: Int) (b: Int): Decidable (Int.LessEq a b) := Bool.decTrue (Int.leq a b)

instance Int.decLessThan (a: Int) (b: Int): Decidable (Int.LessThan a b) := Bool.decTrue (Int.less a b)

--| How `x` compares with `y`: `Int.compare (-3) 2` is `Less`.
def Int.compare: (x: Int) → (y: Int) → Ordering
  | OfNat m, OfNat n => Nat.compare m n
  | OfNat m, NegSucc n => Greater
  | NegSucc m, OfNat n => Less
  | NegSucc m, NegSucc n => Nat.compare n m

--| Decimal, with a `-` in front of a negative: `"-42"`. Never `"-0"`.
def Int.toText: (x: Int) → Text
  | OfNat n => Nat.toText n
  | NegSucc n => MkText ['-', ..Text.toList (Nat.toText (Succ n))]

--| `dividend / divisor`, Euclidean: the remainder it leaves is at least 0 and below `|divisor|`, so `-18 / 100` is `-1`.
--| (`Int.divAddMod`, `Int.modNonneg`, `Int.modLtAbs`.)
--| With [`Int.mod`], `dividend = divisor * (dividend / divisor) + dividend % divisor`
--| with `0 <= dividend % divisor < |divisor|`, whatever the signs, so `-18 % 100` is `82`.
--| Dividing by 0 gives 0, as for `Nat`: `x / 0 = 0` and `x % 0 = x`.
def Int.div: (dividend: Int) → (divisor: Int) → Int
  | dividend, OfNat Zero => OfNat Zero
  | OfNat m, OfNat (Succ n) => OfNat (m / Succ n)
  | NegSucc m, OfNat (Succ n) => NegSucc (m / Succ n)
  | OfNat m, NegSucc n => Int.neg (OfNat (m / Succ n))
  | NegSucc m, NegSucc n => OfNat (Succ (m / Succ n))

--| `dividend % divisor`, Euclidean: never negative, and below `|divisor|`, so `-18 % 100` is `82`.
--| The remainder of dividing by 0 is the dividend: `x % 0 = x`, negative or not.
-- For `NegSucc m`, `m % Succ n <= n`, so the subtraction doesn't stop at
-- zero.
def Int.mod: (dividend: Int) → (divisor: Int) → Int
  | dividend, OfNat Zero => dividend
  | OfNat m, OfNat (Succ n) => OfNat (m % Succ n)
  | NegSucc m, OfNat (Succ n) => OfNat (n - m % Succ n)
  | OfNat m, NegSucc n => OfNat (m % Succ n)
  | NegSucc m, NegSucc n => OfNat (n - m % Succ n)
