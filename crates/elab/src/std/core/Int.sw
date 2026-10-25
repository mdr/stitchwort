-- core/Int.sw. `Int`: the type, its arithmetic, decidable equality,
-- comparison, `toText`, and Euclidean `div`/`mod`. Loaded with the core:
-- `Int` is pinned by content hash, and `+ * < <=` on `Int` go through
-- instances that need these definitions (docs/proposals/prelude-slim.md
-- §2.1).

-- Integers (docs/proposals/integers.md)

-- An integer: `OfNat n` is `n`, and `NegSucc n` is `-(n + 1)`, so each
-- integer has exactly one form. The definitions compute through `Nat`'s, so
-- they're as compact as `Nat` is, and the kernel needs nothing new.
type Int: Type =
  | OfNat (n: Nat)
  | NegSucc (n: Nat)

-- `-x`
def Int.neg: Int → Int
  | OfNat Zero => OfNat Zero
  | OfNat (Succ n) => NegSucc n
  | NegSucc n => OfNat (Succ n)

-- `m - n` for naturals, as an integer. One subtraction decides which side
-- is bigger: `n - m` is zero exactly when `n <= m`.
def Int.subNatNatFrom (m: Nat) (n: Nat): Nat → Int
  | Zero => OfNat (m - n)
  | Succ k => NegSucc k

def Int.subNatNat (m: Nat) (n: Nat): Int := Int.subNatNatFrom m n (n - m)

-- `a + b`
def Int.add: Int → Int → Int
  | OfNat m, OfNat n => OfNat (m + n)
  | OfNat m, NegSucc n => Int.subNatNat m (Succ n)
  | NegSucc m, OfNat n => Int.subNatNat n (Succ m)
  | NegSucc m, NegSucc n => NegSucc (Succ (m + n))

-- `a - b`
def Int.sub (a: Int) (b: Int): Int := Int.add a (Int.neg b)

-- `a * b`. By constructors first, so `OfNat m * OfNat n` is `OfNat (m * n)`.
def Int.mul: Int → Int → Int
  | OfNat m, OfNat n => OfNat (m * n)
  | OfNat m, NegSucc n => Int.neg (OfNat (m * Succ n))
  | NegSucc m, OfNat n => Int.neg (OfNat (Succ m * n))
  | NegSucc m, NegSucc n => OfNat (Succ m * Succ n)

-- `|x|`, as a `Nat`.
def Int.natAbs: Int → Nat
  | OfNat n => n
  | NegSucc n => Succ n

-- `x` if it isn't negative, otherwise `0`.
def Int.toNat: Int → Nat
  | OfNat n => n
  | NegSucc n => 0

-- The two constructors are different, and each is injective.

def Int.IsOfNat: Int → Prop
  | OfNat n => Unit
  | NegSucc n => Void

theorem Int.ofNatNotNegSucc (m: Nat) (n: Nat): Not (OfNat m = NegSucc n)
  | p => J (y q => Int.IsOfNat y) Trivial p

theorem Int.negSuccNotOfNat (m: Nat) (n: Nat): Not (NegSucc m = OfNat n)
  | p => Int.ofNatNotNegSucc n m (Eq.sym p)

theorem Int.ofNatInjective (m: Nat) (n: Nat) (p: OfNat m = OfNat n): m = n := Eq.cong Int.toNat p

theorem Int.negSuccInjective (m: Nat) (n: Nat) (p: NegSucc m = NegSucc n): m = n := Nat.succInjective m n (Eq.cong Int.natAbs p)

def Int.decOfNat (m: Nat) (n: Nat): Decidable (m = n) → Decidable (OfNat m = OfNat n)
  | Yes p => Yes (Eq.cong OfNat p)
  | No r => No (p => r (Int.ofNatInjective m n p))

def Int.decNegSucc (m: Nat) (n: Nat): Decidable (m = n) → Decidable (NegSucc m = NegSucc n)
  | Yes p => Yes (Eq.cong NegSucc p)
  | No r => No (p => r (Int.negSuccInjective m n p))

-- For two integers this computes `Yes rfl` or a `No` of constant size,
-- however big they are, since `Nat.decEq` does.
def Int.decEq: (a: Int) → (b: Int) → Decidable (a = b)
  | OfNat m, OfNat n => Int.decOfNat m n (Nat.decEq m n)
  | OfNat m, NegSucc n => No (Int.ofNatNotNegSucc m n)
  | NegSucc m, OfNat n => No (Int.negSuccNotOfNat m n)
  | NegSucc m, NegSucc n => Int.decNegSucc m n (Nat.decEq m n)

-- `a <= b`. Every negative is below every non-negative; among negatives the
-- order flips, since `NegSucc n` is `-(n+1)`.
def Int.leq: Int → Int → Bool
  | OfNat m, OfNat n => Nat.leq m n
  | OfNat m, NegSucc n => False
  | NegSucc m, OfNat n => True
  | NegSucc m, NegSucc n => Nat.leq n m

-- `a < b`
def Int.less: Int → Int → Bool
  | OfNat m, OfNat n => Nat.leq (Succ m) n
  | OfNat m, NegSucc n => False
  | NegSucc m, OfNat n => True
  | NegSucc m, NegSucc n => Nat.leq (Succ n) m

def Int.LessEq (a: Int) (b: Int): Prop := Int.leq a b = True

def Int.LessThan (a: Int) (b: Int): Prop := Int.less a b = True

instance Int.decLessEq (a: Int) (b: Int): Decidable (Int.LessEq a b) := Bool.decTrue (Int.leq a b)

instance Int.decLessThan (a: Int) (b: Int): Decidable (Int.LessThan a b) := Bool.decTrue (Int.less a b)

def Int.compare: Int → Int → Ordering
  | OfNat m, OfNat n => Nat.compare m n
  | OfNat m, NegSucc n => Greater
  | NegSucc m, OfNat n => Less
  | NegSucc m, NegSucc n => Nat.compare n m

-- Decimal, with a `-` in front of a negative: `"-42"`. Never `"-0"`.
def Int.toText: Int → Text
  | OfNat n => Nat.toText n
  | NegSucc n => MkText (Cons '-' (Text.toList (Nat.toText (Succ n))))

-- Division. `dividend / divisor` and `dividend % divisor` are Euclidean: `dividend = divisor * (dividend / divisor) + dividend % divisor`
-- with `0 <= dividend % divisor < |divisor|`, whatever the signs, so `-18 % 100` is `82`.
-- Each case divides naturals by a `Succ n`, which `auto` sees isn't zero.
-- The divisor can't be zero, but the case still has to be covered: `ok`
-- rules it out.
def Int.div: (dividend: Int) → (divisor: Int) → [auto ok: divisor ≠ OfNat 0] → Int
  | dividend, OfNat Zero => Void.absurd (ok rfl)
  | OfNat m, OfNat (Succ n) => OfNat (m / Succ n)
  | NegSucc m, OfNat (Succ n) => NegSucc (m / Succ n)
  | OfNat m, NegSucc n => Int.neg (OfNat (m / Succ n))
  | NegSucc m, NegSucc n => OfNat (Succ (m / Succ n))

-- Never negative. For `NegSucc m`, `m % Succ n <= n`, so the subtraction
-- doesn't stop at zero.
def Int.mod: (dividend: Int) → (divisor: Int) → [auto ok: divisor ≠ OfNat 0] → Int
  | dividend, OfNat Zero => Void.absurd (ok rfl)
  | OfNat m, OfNat (Succ n) => OfNat (m % Succ n)
  | NegSucc m, OfNat (Succ n) => OfNat (n - m % Succ n)
  | OfNat m, NegSucc n => OfNat (m % Succ n)
  | NegSucc m, NegSucc n => OfNat (n - m % Succ n)
